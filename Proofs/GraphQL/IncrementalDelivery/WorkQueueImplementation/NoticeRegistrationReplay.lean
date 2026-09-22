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
drain preserve the resulting registry and only announce keys already in it.
-/
theorem State.taskSuccess_groupNoticesRegistered {queue : State} {work occurrence result}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : ∀ event ∈ (queue.taskSuccess occurrence result).2,
        event.GroupNoticesRegistered
          (queue.taskSuccess occurrence result).1.registeredGroups := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · simp
      · let stored := queue.putTaskNode { node with value := some result.value }
        let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
        have registered := stored.maybeIntegrateWork_registration live tasks result.work
          matching.childTasksCovered (some occurrence)
        have folded := State.successGroupFold_groupNoticesRegistered registered.1 registered.2.1
          node.task.groups
        let finished := node.task.groups.foldl successGroupStep (integrated, [], {})
        have active := State.startNewWork_registration folded.1 folded.2.1 finished.2.2
        have drained := State.drainReadyGroups_registration active.1 active.2
        have later := State.drainReadyGroups_go_groupNoticesRegistered active.1 active.2
          (finished.1.startNewWork finished.2.2).groupNodes.length
        have same : (finished.1.startNewWork finished.2.2).drainReadyGroups.1.registeredGroups
            = integrated.registeredGroups := by
          rw [drained.2.2, State.startNewWork_registeredGroups, folded.2.2.1]
        change ∀ event ∈ finished.2.1 ++ (finished.1.startNewWork finished.2.2).drainReadyGroups.2,
          event.GroupNoticesRegistered
            (finished.1.startNewWork finished.2.2).drainReadyGroups.1.registeredGroups
        rw [same]
        rw [State.startNewWork_registeredGroups, folded.2.2.1] at later
        intro event member
        exact (List.mem_append.mp member).elim (folded.2.2.2 event) (later event)

/-- An item's pruned group notices remain registered after its own integration.
Witness: a kept key has a live record in the exact pruned state, whose registration
coverage follows from source matching. Activation leaves the registry unchanged.
-/
theorem State.integrateStreamItem_groupNoticesRegistered {queue : State}
    {work stream items item} (keys : queue.GroupKeysUnique)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items)
    : ∀ child ∈
        ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
          (queue.maybeIntegrateWork item.work).2.newGroups).2,
        child.key ∈ (queue.integrateStreamItem item).registeredGroups := by
  let integrated := queue.maybeIntegrateWork item.work
  have registered := queue.maybeIntegrateWork_registration live tasks item.work
    (matching.streamItem_childTasksCovered member)
  have pruned := integrated.1.pruneEmptyGroups_registration registered.1 registered.2.1
    integrated.2.newGroups
  intro child noticed
  obtain ⟨node, present, same⟩ := List.mem_map.mp
    (integrated.1.pruneEmptyGroups_keptPresent integrated.2.newGroups
      (keys.maybeIntegrateWork item.work) child.key (List.mem_map_of_mem noticed))
  unfold State.integrateStreamItem
  rw [State.startNewWork_registeredGroups]
  exact same ▸ pruned.1 node present

/-- Item integration preserves all earlier notice registrations and registers new ones.
Witness: the actual metadata fold threads live-key uniqueness and registration coverage;
its monotone registry retains earlier item notices before the eventual leading event.
-/
theorem State.streamItemFold_groupNoticesRegistered {queue : State} {work stream items}
    (keys : queue.GroupKeysUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : let prepared := items.foldl streamItemStep (queue, [], [], [])
      prepared.1.LiveGroupsRegistered
      ∧ prepared.1.TaskGroupsRegistered
      ∧ ∀ child ∈ prepared.2.1, child.key ∈ prepared.1.registeredGroups := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue)
      (unique : acc.1.GroupKeysUnique) (covered : acc.1.LiveGroupsRegistered)
      (taskCoverage : acc.1.TaskGroupsRegistered)
      (known : ∀ child ∈ acc.2.1, child.key ∈ acc.1.registeredGroups)
      : let prepared := more.foldl streamItemStep acc
        prepared.1.LiveGroupsRegistered ∧ prepared.1.TaskGroupsRegistered
        ∧ ∀ child ∈ prepared.2.1, child.key ∈ prepared.1.registeredGroups := by
    induction more generalizing acc with
    | nil => exact ⟨covered, taskCoverage, known⟩
    | cons item rest ih =>
        have member := included List.mem_cons_self
        have registered := acc.1.integrateStreamItem_registration covered taskCoverage
          matching member
        have itemKeys : (acc.1.integrateStreamItem item).GroupKeysUnique :=
          ((unique.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
        apply ih (fun _ later => included (List.mem_cons_of_mem _ later))
          (streamItemStep acc item) itemKeys registered.1 registered.2.1
        intro child noticed
        rcases List.mem_append.mp noticed with old | new
        · exact registered.2.2 (known child old)
        · exact acc.1.integrateStreamItem_groupNoticesRegistered unique covered taskCoverage
            matching member child new
  exact loop items (List.Subset.refl _) (queue, [], [], []) keys live tasks (by simp)

/-- Every item-handler notice belongs to the registry immediately after that handler.
Witness: the leading event carries notices from the exact integration fold; later group
carriers use its registry-preserving drain. Future source inputs play no part.
-/
theorem State.streamItems_groupNoticesRegistered {queue : State} {work stream items}
    (keys : queue.GroupKeysUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : ∀ event ∈ (queue.streamItems stream items).2,
        event.GroupNoticesRegistered
          (queue.streamItems stream items).1.registeredGroups := by
  rw [queue.streamItems_eq stream items]
  split
  · simp
  · have prepared := queue.streamItemFold_groupNoticesRegistered keys live tasks matching
    have drained := State.drainReadyGroups_registration prepared.1 prepared.2.1
    have later := State.drainReadyGroups_go_groupNoticesRegistered prepared.1 prepared.2.1
      (queue.preparedStreamItems items).groupNodes.length
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
    (keys : queue.GroupKeysUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (event : GraphEvent)
    (matching : event.MatchesWork work)
    : ∀ output ∈ (queue.handleGraphEvent event).2,
        output.GroupNoticesRegistered
          (queue.handleGraphEvent event).1.registeredGroups := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_groupNoticesRegistered live tasks matching
  | streamItems stream items =>
      exact queue.streamItems_groupNoticesRegistered keys live tasks matching
  | taskFailure occurrence errors =>
      intro output member
      cases output with
      | groupSuccess group groups streams =>
          exact False.elim (queue.taskFailure_noGroupSuccess occurrence errors group groups streams
            member)
      | streamValues stream values groups streams =>
          have impossible : stream.key ∈
              (queue.taskFailure occurrence errors).2.flatMap rawStreamReferenceKeys :=
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

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
