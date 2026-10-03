import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayValueConservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureAccounting

/-! Buffered contributors publish before later successful carriers on one replay ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Source concatenation retains exact raw output offsets
-----------------------------------------------------------------------------------------

/-- Raw replay concatenates outputs while threading exactly the intermediate queue.
Witness: induction over the first source prefix, using the existing head-step equation.
-/
theorem State.rawEventReplay_append (queue : State) (before after : List GraphEvent)
    : queue.rawEventReplay (before ++ after)
      = let first := queue.rawEventReplay before
        let last := first.1.rawEventReplay after
        (last.1, first.2 ++ last.2) := by
  induction before generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      simp only [List.cons_append, State.rawEventReplay_cons, ih, List.append_assoc]

-----------------------------------------------------------------------------------------
-- Later successful carriers cannot recreate already registered contributing groups
-----------------------------------------------------------------------------------------

/-- Matching event replay preserves registration coverage and all earlier registrations.
Witness: compose the existing per-handler registration theorem in source order.
-/
theorem State.replayGraphEvents_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.replayGraphEvents events).LiveGroupsRegistered
      ∧ (queue.replayGraphEvents events).TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.replayGraphEvents events).registeredGroups := by
  induction events generalizing queue with
  | nil => exact ⟨live, tasks, List.Subset.refl _⟩
  | cons event rest ih =>
      have next := queue.handleGraphEvent_registration live tasks event
        (matching event List.mem_cons_self)
      have final := ih next.1 next.2.1
        (fun later member => matching later (List.mem_cons_of_mem _ member))
      exact ⟨final.1, final.2.1, next.2.2.trans final.2.2⟩

/-- A successful carrier's previously registered group is live at the handler input.
Witness: otherwise permanent retirement would forbid that handler from emitting its
closing ref. Newly registered groups are intentionally excluded by the registry premise.
-/
theorem State.handleGraphEvent_success_live_registered {queue : State} {work event}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (matching : event.MatchesWork work) {group groups streams}
    (registered : group.ref ∈ queue.registeredGroups)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (queue.handleGraphEvent event).2)
    : ∃ owner, queue.groupNode? group.ref = some owner := by
  cases found : queue.groupNode? group.ref with
  | some owner => exact ⟨owner, rfl⟩
  | none =>
      have retired := State.RetiredGroup.of_lookup_none registered found
      have accounted := queue.handleGraphEvent_closureAccounting live tasks event matching
      exact False.elim (accounted.excludes group.ref retired
        (List.mem_flatMap.mpr ⟨.groupSuccess group groups streams, carrier,
          List.mem_cons_self⟩))

-----------------------------------------------------------------------------------------
-- Prefix-bounded conservation meets exact handler-local buffered coverage
-----------------------------------------------------------------------------------------

/-- An initially buffered contributor publishes strictly before a later group carrier.
Witness: registration and closure uniqueness retain a live contributor at the carrier's
input. Prefix-bounded conservation either places the value earlier or retains its exact
lookup; handler coverage then places it before the selected closing event. Both branches
use consecutive prefixes of the same occurrence ledger.
-/
theorem State.ReplayClosuresCovered.buffered_carrier {queue : State}
    {work before event published}
    (covered : queue.ReplayClosuresCovered (before ++ [event]) published)
    (live : queue.LiveGroupsRegistered) (registered : queue.TaskGroupsRegistered)
    (started : queue.StartedTasksRegistered)
    (matching : ∀ input ∈ before ++ [event], input.MatchesWork work)
    {index group groups streams}
    (carrier
      : ((queue.replayGraphEvents before).handleGraphEvent event).2[index]?
        = some (.groupSuccess group groups streams))
    {occurrence node value} (found : queue.taskNode? occurrence = some node)
    (stored : node.value = some value)
    (contributes : group.ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    : (occurrence, value)
      ∈ published.take
          (((queue.rawEventReplay before).2.flatMap WorkQueueEvent.objectValues).length
            + ((((queue.replayGraphEvents before).handleGraphEvent event).2.take
                  index).flatMap
                WorkQueueEvent.objectValues).length) := by
  have earlierMatching : ∀ input ∈ before, input.MatchesWork work :=
    fun input member => matching input (List.mem_append_left _ member)
  have boundary := queue.replayGraphEvents_registration live registered before earlierMatching
  have known := State.taskNode?_some found
  have recorded := registered node.task (started node known.1) group.ref contributes
  obtain ⟨owner, ownerLive⟩ := State.handleGraphEvent_success_live_registered
    boundary.1 boundary.2.1 (matching event (List.mem_append_right _ List.mem_cons_self))
    (boundary.2.2 recorded) (List.mem_of_getElem? carrier)
  obtain ⟨contributor, contributorMem, same⟩ := List.mem_map.mp contributes
  have survives : ∃ contributor ∈ node.task.groups, ∃ owner,
      (queue.replayGraphEvents before).groupNode? contributor.ref = some owner :=
    ⟨contributor, contributorMem, owner, same ▸ ownerLive⟩
  have conserved := (covered.prefix before [event]).conserves live registered started
    earlierMatching
  rw [List.take_add]
  rcases conserved occurrence node value found stored survives with earlier | retained
  · exact List.mem_append_left _ earlier
  · have localCoverage := (covered.atPrefix before event []).1
    have delivered := localCoverage index group groups streams carrier
      occurrence node value retained stored contributes
    have bounded :
        ((((queue.replayGraphEvents before).handleGraphEvent event).2.take index).flatMap
          WorkQueueEvent.objectValues).length
        ≤ (((queue.replayGraphEvents before).handleGraphEvent event).2.flatMap
          WorkQueueEvent.objectValues).length := by
      have split := congrArg (fun events : List WorkQueueEvent =>
        (events.flatMap WorkQueueEvent.objectValues).length)
        (List.take_append_drop index
          ((queue.replayGraphEvents before).handleGraphEvent event).2)
      simp only [List.flatMap_append, List.length_append] at split
      omega
    apply List.mem_append_right
    simpa only [List.take_take, Nat.min_eq_left bounded] using delivered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
