import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailurePersistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay

/-! Cached failures survive host processing until permanent cancellation is recorded. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Successful task processing cannot erase a retained failure.
Witness: integration retains caches; a success flush requires an empty selected cache;
activation and final draining retain the failure or its permanent cancellation marker.
-/
theorem State.FailureRetained.taskSuccess {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (occurrence : Occurrence) (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.FailureRetained ref := by
  have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (prior : acc.1.FailureRetained ref) (refs : acc.1.GroupRefsUnique)
      : (successGroupStep acc group).1.FailureRetained ref
        ∧ (successGroupStep acc group).1.GroupRefsUnique := by
    obtain ⟨current, outputs, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact ⟨prior, refs⟩
    · rename_i node found
      have updated := prior.putCounters refs found (node.pending - 1) node.failure
        (fun same => same)
      have updatedRefs := refs.putGroupNode { node with pending := node.pending - 1 }
      split
      · rename_i success
        have clear : node.failure = none := by
          have parts :
              ((current.putGroupNode { node with pending := node.pending - 1 }).rootGroups.contains
                  group.ref = true ∧ node.pending - 1 == 0)
                ∧ node.failure.isNone = true := by
            simpa only [Bool.and_eq_true] using success
          simpa using parts.2
        have member : { node with pending := node.pending - 1 }
            ∈ (current.putGroupNode { node with pending := node.pending - 1 }).groupNodes :=
          List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found, by simp⟩
        exact ⟨updated.finishGroupSuccess updatedRefs _ member clear,
          updatedRefs.finishGroupSuccess _⟩
      · exact ⟨updated, updatedRefs⟩
  have fold (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (prior : acc.1.FailureRetained ref) (refs : acc.1.GroupRefsUnique)
      : (groups.foldl successGroupStep acc).1.FailureRetained ref
        ∧ (groups.foldl successGroupStep acc).1.GroupRefsUnique := by
    induction groups generalizing acc with
    | nil => exact ⟨prior, refs⟩
    | cons group rest ih =>
        obtain ⟨retained, unique⟩ := step acc group prior refs
        exact ih _ retained unique
  unfold State.taskSuccess
  split
  · exact retained
  · rename_i node found
    split
    · exact retained.removeTask occurrence
    · let stored := queue.putTaskNode { node with value := some result.value }
      have prior : stored.FailureRetained ref := retained
      have refs : stored.GroupRefsUnique := unique
      obtain ⟨retained, unique⟩ := fold node.task.groups
        ((stored.maybeIntegrateWork result.work (some occurrence)).1, [], {})
        (prior.maybeIntegrateWork refs result.work (some occurrence))
        (refs.maybeIntegrateWork result.work (some occurrence))
      exact (retained.startNewWork _).drainReadyGroups (unique.startNewWork _)

/-- Failed task processing retains each earlier cache or marks its removal.
Witness: immediate failures record subtree cancellations; latent updates install a cache;
ignored settlements only remove task memberships.
-/
theorem State.FailureRetained.taskFailure {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.FailureRetained ref := by
  have fold (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : acc.1.FailureRetained ref) (refs : acc.1.GroupRefsUnique)
      : (groups.foldl (failureGroupStep errors) acc).1.FailureRetained ref := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        · dsimp only [failureGroupStep]
          split
          · exact prior
          · rename_i node found
            split
            · exact prior.removeGroup _
            · exact prior.putCounters refs found _ _ (by simp)
        · dsimp only [failureGroupStep]
          split
          · exact refs
          · split
            · exact refs.removeGroup _
            · exact refs.putGroupNode _
  unfold State.taskFailure
  split
  · exact retained
  · rename_i node found
    split
    · exact retained.removeTask occurrence
    · exact fold node.task.groups (queue.removeTask occurrence, [])
        (retained.removeTask occurrence) (unique.removeTask occurrence)

/-- Item arrival retains earlier failure caches through preparation and draining.
Witness: item-child integration, pruning, activation, and the final drain each preserve
the concrete cache-or-cancellation alternative. The stream need not be active.
-/
theorem State.FailureRetained.streamItems {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : (queue.streamItems stream items).1.FailureRetained ref := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    (pruned.startNewWork { more with newGroups := nonempty }, groups ++ nonempty,
      streams ++ more.newStreams, values ++ [item.value])
  have fold (more : List StreamItem) (acc)
      (prior : acc.1.FailureRetained ref) (refs : acc.1.GroupRefsUnique)
      : (more.foldl step acc).1.FailureRetained ref
        ∧ (more.foldl step acc).1.GroupRefsUnique := by
    induction more generalizing acc with
    | nil => exact ⟨prior, refs⟩
    | cons item rest ih =>
        have integrated := prior.maybeIntegrateWork refs item.work
        have integratedRefs := refs.maybeIntegrateWork item.work
        exact ih _ ((integrated.pruneEmptyGroups integratedRefs _).startNewWork _)
          ((integratedRefs.pruneEmptyGroups _).startNewWork _)
  unfold State.streamItems
  split
  · exact retained
  · obtain ⟨retained, unique⟩ := fold items (queue, [], [], []) retained unique
    exact retained.drainReadyGroups unique

/-- Every executable host handler preserves a retained failure without source premises.
Witness: dispatch the exact handlers; stream closure leaves group data untouched.
-/
theorem State.FailureRetained.handleGraphEvent {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (event : GraphEvent)
    : (queue.handleGraphEvent event).1.FailureRetained ref := by
  cases event with
  | taskSuccess occurrence result => exact retained.taskSuccess unique occurrence result
  | taskFailure occurrence errors => exact retained.taskFailure unique occurrence errors
  | streamItems stream items => exact retained.streamItems unique stream items
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.FailureRetained ref
      unfold State.streamSuccess
      split <;> exact retained
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.FailureRetained ref
      unfold State.streamFailure
      split <;> exact retained

/-- An earlier failure survives every finite raw continuation until marked cancelled.
Witness: replay induction composes handler retention and unique-ref preservation.
No event matching, source fairness, wire admission, or terminal-reporting premise is used.
-/
theorem State.FailureRetained.rawEventReplay {queue : State} {ref}
    (retained : queue.FailureRetained ref) (unique : queue.GroupRefsUnique)
    (events : List GraphEvent)
    : (queue.rawEventReplay events).1.FailureRetained ref := by
  induction events generalizing queue with
  | nil => exact retained
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      exact ih (retained.handleGraphEvent unique event) (unique.handleGraphEvent event)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
