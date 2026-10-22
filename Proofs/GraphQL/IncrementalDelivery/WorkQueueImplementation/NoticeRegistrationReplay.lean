import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedCarrierReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReferences

/-! Source handlers retain the registrations supporting every carried group notice. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Both value-bearing handlers announce only permanently registered groups
-----------------------------------------------------------------------------------------

/-- Object-success notices belong to the registry after that same input handler.
Witness: child integration supplies registration coverage; the owner fold and subsequent
drain preserve the resulting registry and only announce refs already in it.
-/
theorem State.taskSuccess_groupNoticesRegistered {queue : State} {work occurrence result}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ∀ event ∈ (queue.taskSuccess occurrence result available).2.1,
        event.GroupNoticesRegistered
          (queue.taskSuccess occurrence result available).1.registeredGroups := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
      let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
      have registeredTask := frame.started node (State.taskNode?_some found).1
      have supplied := (frame.children node.task registeredTask).sourceChild
        (State.taskNode?_some found).2 matching
      have registered := stored.maybeIntegrateWork_registration live tasks result.work
        supplied.contributors (some occurrence)
      have folded := State.successGroupFold_groupNoticesRegistered registered.1 registered.2.1
        node.task.groups
      let finished := node.task.groups.foldl successGroupStep (integrated, [], {})
      let activated := (finished.1.startNewWork finished.2.2 available).1
      have active := State.startNewWork_registration folded.1 folded.2.1 finished.2.2 available
      have drained := State.drainReadyGroups_registration active.1 active.2 available
      have later := State.drainReadyGroups_go_groupNoticesRegistered active.1 active.2
        activated.groupNodes.length available
      have same : (activated.drainReadyGroups available).1.registeredGroups
          = integrated.registeredGroups := by
        rw [drained.2.2, State.startNewWork_registeredGroups, folded.2.2.1]
      change ∀ event ∈ finished.2.1 ++ (activated.drainReadyGroups available).2.1,
        event.GroupNoticesRegistered
          (activated.drainReadyGroups available).1.registeredGroups
      rw [same]
      rw [State.startNewWork_registeredGroups, folded.2.2.1] at later
      intro event member
      exact (List.mem_append.mp member).elim (folded.2.2.2 event) (later event)

/-- An item's pruned group notices remain registered after its own integration.
Witness: a kept ref has a live record in the exact pruned state, whose registration
coverage follows from source matching. Activation leaves the registry unchanged.
-/
theorem State.integrateStreamItem_groupNoticesRegistered {queue : State}
    {work stream items item} (refs : queue.GroupRefsUnique)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items)
    (available : List (Occurrence × Nat) := [])
    : ∀ child ∈
        ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
          (queue.maybeIntegrateWork item.work).2.newGroups).2,
        child.ref ∈ (queue.integrateStreamItem item available).registeredGroups := by
  let integrated := queue.maybeIntegrateWork item.work
  have registered := queue.maybeIntegrateWork_registration live tasks item.work
    (by
      intro task included ref contributes
      exact .inr (matching.streamItem_childTasksCovered frame.source member
        task included ref contributes))
  have pruned := integrated.1.pruneEmptyGroups_registration registered.1 registered.2.1
    integrated.2.newGroups
  intro child noticed
  obtain ⟨node, present, same⟩ := List.mem_map.mp
    (integrated.1.pruneEmptyGroups_keptPresent integrated.2.newGroups
      (refs.maybeIntegrateWork item.work) child.ref (List.mem_map_of_mem noticed))
  unfold State.integrateStreamItem
  rw [State.startNewWork_registeredGroups]
  exact same ▸ pruned.1 node present

/-- Item integration preserves all earlier notice registrations and registers new ones.
Witness: the actual metadata fold threads live-ref uniqueness and registration coverage;
its monotone registry retains earlier item notices before the eventual leading event.
-/
theorem State.streamItemFold_groupNoticesRegistered {queue : State} {work stream items}
    (refs : queue.GroupRefsUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : let prepared :=
        items.foldl (fun acc item => streamItemStep acc item available)
          (queue, [], [], [], [])
      prepared.1.LiveGroupsRegistered
      ∧ prepared.1.TaskGroupsRegistered
      ∧ ∀ child ∈ prepared.2.1, child.ref ∈ prepared.1.registeredGroups := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue × List GroupFailureEvent)
      (unique : acc.1.GroupRefsUnique) (covered : acc.1.LiveGroupsRegistered)
      (taskCoverage : acc.1.TaskGroupsRegistered)
      (context : acc.1.RegistrationFrame work)
      (known : ∀ child ∈ acc.2.1, child.ref ∈ acc.1.registeredGroups)
      : let prepared := more.foldl (fun acc item => streamItemStep acc item available) acc
        prepared.1.LiveGroupsRegistered ∧ prepared.1.TaskGroupsRegistered
        ∧ ∀ child ∈ prepared.2.1, child.ref ∈ prepared.1.registeredGroups := by
    induction more generalizing acc with
    | nil => exact ⟨covered, taskCoverage, known⟩
    | cons item rest ih =>
        have member := included List.mem_cons_self
        have registered := acc.1.integrateStreamItem_registration covered taskCoverage
          matching member context available
        have itemRefs : (acc.1.integrateStreamItem item available).GroupRefsUnique :=
          ((unique.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available
        apply ih (fun _ later => included (List.mem_cons_of_mem _ later))
          (streamItemStep acc item available) itemRefs registered.1 registered.2.1
          (context.integrateStreamItem matching member available).1
        intro child noticed
        rcases List.mem_append.mp noticed with old | new
        · exact registered.2.2 (known child old)
        · exact acc.1.integrateStreamItem_groupNoticesRegistered unique covered taskCoverage context
            matching member available child new
  exact loop items (List.Subset.refl _) (queue, [], [], [], []) refs live tasks frame
    (by simp)

/-- Every item-handler notice belongs to the registry immediately after that handler.
Witness: the leading event carries notices from the exact integration fold; later group
carriers use its registry-preserving drain. Future source inputs play no part.
-/
theorem State.streamItems_groupNoticesRegistered {queue : State} {work stream items}
    (refs : queue.GroupRefsUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ∀ event ∈ (queue.streamItems stream items available).2.1,
        event.GroupNoticesRegistered
          (queue.streamItems stream items available).1.registeredGroups := by
  rw [queue.streamItems_eq stream items available]
  split
  · simp
  · have prepared := queue.streamItemFold_groupNoticesRegistered refs live tasks frame matching available
    have drained := State.drainReadyGroups_registration prepared.1 prepared.2.1 available
    have later := State.drainReadyGroups_go_groupNoticesRegistered prepared.1 prepared.2.1
      (queue.preparedStreamItems items available).groupNodes.length available
    intro event member
    rw [drained.2.2]
    rcases List.mem_cons.mp member with first | rest
    · subst event
      exact prepared.2.2
    · exact later event rest

-----------------------------------------------------------------------------------------
-- The actual matched handler is the registration cutoff
-----------------------------------------------------------------------------------------

/-- A matching handler cannot announce a group first registered by a future input.
Witness: the two value-bearing handlers give the registration bridge; all failure and
closure-only handlers carry no group notices, including ignored-input branches.
-/
theorem State.handleGraphEvent_groupNoticesRegistered {queue : State} {work}
    (refs : queue.GroupRefsUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work) (event : GraphEvent)
    (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ∀ output ∈ (queue.handleGraphEvent event available).2.1,
        output.GroupNoticesRegistered
          (queue.handleGraphEvent event available).1.registeredGroups := by
  let current := queue.cacheTaskFailures available
  have cached := queue.cacheTaskFailures_registration live tasks available
  have unique := refs.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      exact current.taskSuccess_groupNoticesRegistered cached.1 cached.2 (frame.cacheTaskFailures available) matching available
  | streamItems stream items =>
      exact current.streamItems_groupNoticesRegistered unique cached.1 cached.2 (frame.cacheTaskFailures available) matching available
  | taskFailure occurrence errors =>
      intro output member
      cases output with
      | groupSuccess group groups streams =>
          exact False.elim (current.taskFailure_noGroupSuccess occurrence errors group groups
            streams member)
      | streamValues stream values groups streams =>
          have impossible : stream.ref ∈
              (current.taskFailure occurrence errors).2.flatMap rawStreamReferenceRefs :=
            List.mem_flatMap.mpr ⟨_, member, List.mem_cons_self⟩
          rw [State.taskFailure_streamReferences] at impossible
          cases impossible
      | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination
        =>
          trivial
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [WorkQueueEvent.GroupNoticesRegistered]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [WorkQueueEvent.GroupNoticesRegistered]

  | groupFailure failure =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · simp
      · split <;> simp [WorkQueueEvent.GroupNoticesRegistered]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
