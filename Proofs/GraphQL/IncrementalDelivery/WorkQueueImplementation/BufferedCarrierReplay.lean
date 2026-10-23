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
    (available : List (Occurrence × Nat) := [])
    : queue.rawEventReplay (before ++ after) available
      = let first := queue.rawEventReplay before available
        let last := first.1.rawEventReplay after available
        (last.1, first.2 ++ last.2) := by
  induction before generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      simp only [List.cons_append, State.rawEventReplay_cons, ih, List.append_assoc]

-----------------------------------------------------------------------------------------
-- Later successful carriers cannot recreate already registered contributing groups
-----------------------------------------------------------------------------------------

/-- A successful carrier's previously registered group is live at the handler input.
Witness: otherwise permanent retirement would forbid that handler from emitting its
closing ref. Newly registered groups are intentionally excluded by the registry premise.
-/
theorem State.handleGraphEvent_success_live_registered {queue : State}
    {available : List (Occurrence × Nat)} {work event} (live : queue.LiveGroupsRegistered)
    (_tasks : queue.TaskGroupsRegistered) (_matching : event.MatchesWork work)
    {group groups streams} (registered : group.ref ∈ queue.registeredGroups)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (queue.handleGraphEvent event available).2.1)
    : ∃ owner, queue.groupNode? group.ref = some owner := by
  cases found : queue.groupNode? group.ref with
  | some owner => exact ⟨owner, rfl⟩
  | none =>
      have retired := State.RetiredGroup.of_lookup_none registered found
      have ordinary : ∀ failure, event ≠ .groupFailure failure := by
        intro failure same
        subst event
        simp only [State.handleGraphEvent, State.groupFailure] at carrier
        split at carrier
        · cases carrier
        · split at carrier <;> simp at carrier
      have accounted := queue.handleGraphEvent_removalAccounting live event available ordinary
      exact False.elim
        (accounted.excludes group.ref retired
          (List.mem_flatMap.mpr
            ⟨
              .groupSuccess group groups streams,
              List.mem_append_left _ carrier,
              List.mem_cons_self
            ⟩))

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
    {available : List (Occurrence × Nat)} {work before event published}
    (covered : queue.ReplayClosuresCovered (before ++ [event]) published available)
    (live : queue.LiveGroupsRegistered) (registered : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work)
    (matching : ∀ input ∈ before ++ [event], input.MatchesWork work)
    {index group groups streams}
    (carrier
      : ((queue.replayGraphEvents before available).handleGraphEvent event
          available).2.1[index]?
        = some (.groupSuccess group groups streams))
    {occurrence node value} (found : queue.taskNode? occurrence = some node)
    (stored : node.value = some value)
    (contributes : group.ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    : (occurrence, value)
      ∈ published.take
          (((queue.rawEventReplay before available).2.flatMap
              WorkQueueEvent.objectValues).length
            + ((((queue.replayGraphEvents before available).handleGraphEvent event
                  available).2.1.take
                  index).flatMap
                WorkQueueEvent.objectValues).length) := by
  have earlierMatching : ∀ input ∈ before, input.MatchesWork work :=
    fun input member => matching input (List.mem_append_left _ member)
  have boundary := queue.replayGraphEvents_registration live registered before earlierMatching frame
    available
  have known := State.taskNode?_some found
  have recorded := registered node.task (frame.started node known.1) group.ref contributes
  obtain ⟨owner, ownerLive⟩ := State.handleGraphEvent_success_live_registered
    boundary.1 boundary.2.1 (matching event (List.mem_append_right _ List.mem_cons_self))
    (boundary.2.2 recorded) (List.mem_of_getElem? carrier)
  obtain ⟨contributor, contributorMem, same⟩ := List.mem_map.mp contributes
  have survives : ∃ contributor ∈ node.task.groups, ∃ owner,
      (queue.replayGraphEvents before available).groupNode? contributor.ref = some owner :=
    ⟨contributor, contributorMem, owner, same ▸ ownerLive⟩
  have conserved := (covered.prefix before [event]).conserves frame earlierMatching
  rw [List.take_add]
  rcases conserved occurrence node value found stored survives with earlier | retained
  · exact List.mem_append_left _ earlier
  · have localCoverage := (covered.atPrefix before event []).1
    have delivered := localCoverage index group groups streams carrier
      occurrence node value retained stored contributes
    have bounded :
        ((((queue.replayGraphEvents before available).handleGraphEvent event available).2.1.take
              index).flatMap
          WorkQueueEvent.objectValues).length
        ≤ (((queue.replayGraphEvents before available).handleGraphEvent event available).2.1.flatMap
          WorkQueueEvent.objectValues).length := by
      have split := congrArg (fun events : List WorkQueueEvent =>
        (events.flatMap WorkQueueEvent.objectValues).length)
        (List.take_append_drop index
          ((queue.replayGraphEvents before available).handleGraphEvent event available).2.1)
      simp only [List.flatMap_append, List.length_append] at split
      omega
    apply List.mem_append_right
    simpa only [State.dispatchGraphEvent, List.take_take, Nat.min_eq_left bounded] using delivered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
