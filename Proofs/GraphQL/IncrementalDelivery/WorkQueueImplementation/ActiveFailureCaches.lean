import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureReplay

/-! Active groups never retain an older failure cache at source-handler boundaries. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every live active group has no retained error cache.
This concerns the executable cache only, not semantic health of ancestors or dependents.
-/
def State.NoActiveCachedFailure (queue : State) : Prop :=
  ∀ node ∈ queue.groupNodes, node.group.node.ref ∈ queue.rootGroups → node.failure = none

/-- A completed drain leaves no cached failure on an active group.
Witness: unique refs identify each live node with its lookup; the drain normal form then
rules out a retained failure. The uniqueness premise is needed only on the final state.
-/
theorem State.drainReadyGroups_noActiveCachedFailure (queue : State)
    (unique : queue.drainReadyGroups.1.GroupRefsUnique)
    : queue.drainReadyGroups.1.NoActiveCachedFailure := by
  intro node member active
  cases found : queue.drainReadyGroups.1.groupNode? node.group.node.ref with
  | none =>
      have impossible := List.find?_eq_none.mp found node member
      simp at impossible
  | some selected =>
      have same := unique.sameNode (List.mem_of_find?_eq_some found) member
        (State.groupNode?_ref found)
      subst selected
      exact (queue.drainReadyGroups_normalForm _ active _ found).1

/-- Removing task memberships changes no active ref or failure cache.
Witness: project each mapped node's unchanged ref and cache.
-/
theorem State.NoActiveCachedFailure.removeTask {queue : State}
    (clear : queue.NoActiveCachedFailure) (occurrence : Occurrence)
    : (queue.removeTask occurrence).NoActiveCachedFailure := by
  intro node member active
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact clear old oldMember active

/-- Removing a group only filters live nodes and active refs.
Witness: both surviving memberships belonged to the original queue.
-/
theorem State.NoActiveCachedFailure.removeGroup {queue : State}
    (clear : queue.NoActiveCachedFailure) (ref : NodeRef)
    : (queue.removeGroup ref).NoActiveCachedFailure := by
  intro node member active
  exact clear node (List.mem_filter.mp member).1 (List.mem_filter.mp active).1

/-- Storing an error on a latent group cannot create an active cached failure.
Witness: a replaced node's ref is inactive; all other nodes and active refs are unchanged.
-/
theorem State.NoActiveCachedFailure.putLatent {queue : State}
    (clear : queue.NoActiveCachedFailure) (updated : GroupNode)
    (latent : updated.group.node.ref ∉ queue.rootGroups)
    : (queue.putGroupNode updated).NoActiveCachedFailure := by
  intro node member active
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact (latent active).elim
  · subst node; exact clear old oldMember active

/-- Immediate failure processing leaves no cached failure on a still-active group.
Witness: active contributors close; only inactive contributors receive retained counts.
-/
theorem State.NoActiveCachedFailure.taskFailure {queue : State}
    (clear : queue.NoActiveCachedFailure) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.NoActiveCachedFailure := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : acc.1.NoActiveCachedFailure)
      : (groups.foldl (failureGroupStep errors) acc).1.NoActiveCachedFailure := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        obtain ⟨current, events⟩ := acc
        dsimp only [failureGroupStep]
        split
        · exact prior
        · rename_i node found
          split
          · exact prior.removeGroup node.group.node.ref
          · rename_i latent
            exact prior.putLatent _ (by simpa [current.groupNode?_ref found] using latent)
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using clear
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      split
      · exact clear.removeTask occurrence
      · exact loop task.task.groups (queue.removeTask occurrence, [])
          (clear.removeTask occurrence)

/-- Successful settlement retains clear active caches before returning to its caller.
Witness: eligible tasks end with a full drain; ignored tasks remove only memberships.
-/
theorem State.NoActiveCachedFailure.taskSuccess {queue : State}
    (clear : queue.NoActiveCachedFailure) (unique : queue.GroupRefsUnique)
    (occurrence : Occurrence) (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.NoActiveCachedFailure := by
  have finalUnique := unique.taskSuccess occurrence result
  unfold State.taskSuccess at finalUnique ⊢
  split
  · exact clear
  · rename_i node found
    simp only [found] at finalUnique
    cases eligible : queue.taskHasHealthyOwner node.task with
    | false =>
        simpa only [eligible, Bool.not_false, ↓reduceIte] using clear.removeTask occurrence
    | true =>
        simp only [eligible, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at finalUnique ⊢
        exact State.drainReadyGroups_noActiveCachedFailure _ finalUnique

/-- Item processing clears every active cache after integrating and announcing children.
Witness: the active-stream branch ends with a full drain; an ignored stream changes nothing.
-/
theorem State.NoActiveCachedFailure.streamItems {queue : State}
    (clear : queue.NoActiveCachedFailure) (unique : queue.GroupRefsUnique)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : (queue.streamItems stream items).1.NoActiveCachedFailure := by
  have finalUnique := unique.streamItems stream items
  unfold State.streamItems at finalUnique ⊢
  split
  · exact clear
  · rename_i active
    simp only [active] at finalUnique
    exact State.drainReadyGroups_noActiveCachedFailure _ finalUnique

/-- Every handler preserves the no-active-cache invariant.
Witness: failure retains only latent caches, success/item arrival drains, and stream
closure leaves group nodes and active group refs unchanged.
-/
theorem State.NoActiveCachedFailure.handleGraphEvent {queue : State}
    (clear : queue.NoActiveCachedFailure) (unique : queue.GroupRefsUnique)
    (event : GraphEvent)
    : (queue.handleGraphEvent event).1.NoActiveCachedFailure := by
  cases event with
  | taskSuccess occurrence result => exact clear.taskSuccess unique occurrence result
  | taskFailure occurrence errors => exact clear.taskFailure occurrence errors
  | streamItems stream items => exact clear.streamItems unique stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact clear
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact clear

/-- Raw handler replay preserves clear active caches, without source-admission premises.
Witness: thread ref uniqueness and the cache invariant through each actual handler.
-/
theorem State.NoActiveCachedFailure.replayGraphEvents {queue : State}
    (clear : queue.NoActiveCachedFailure) (unique : queue.GroupRefsUnique)
    (events : List GraphEvent)
    : (queue.replayGraphEvents events).NoActiveCachedFailure := by
  induction events generalizing queue with
  | nil => exact clear
  | cons event rest ih =>
      simpa only [State.replayGraphEvents, List.foldl_cons]
        using ih (clear.handleGraphEvent unique event) (unique.handleGraphEvent event)

/-- Batch wrapping cannot leave a cached failure on an active group.
Witness: ignored batches preserve the state; processed batches add only a termination flag.
-/
theorem State.NoActiveCachedFailure.handleGraphEvents {queue : State}
    (clear : queue.NoActiveCachedFailure) (unique : queue.GroupRefsUnique)
    (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.NoActiveCachedFailure := by
  cases running : queue.terminated with
  | true => simpa only [State.handleGraphEvents, running, ↓reduceIte] using clear
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      rw [same]
      exact clear.replayGraphEvents unique events

/-- Normalized replay retains clear active caches across all supplied batches.
Witness: the actual state fold, independent of publisher output, start checks, or validity.
-/
theorem State.NoActiveCachedFailure.runNormalized {queue : State}
    (clear : queue.NoActiveCachedFailure) (unique : queue.GroupRefsUnique)
    (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1.NoActiveCachedFailure := by
  rw [State.runNormalized_stateFold]
  induction batches generalizing queue with
  | nil => exact clear
  | cons batch rest ih =>
      exact ih (clear.handleGraphEvents unique batch) (unique.handleGraphEvents batch)

/-- Every initialized runner has clear active caches at each host-handler boundary.
Witness: creation has no caches anywhere, then uniqueness and handler replay preserve it.
This is derived implementation behavior, not an added scheduler or event-source law.
-/
theorem createWorkQueue_runNormalized_noActiveCachedFailure
    (input : Work) (batches : List (List GraphEvent))
    : ((State.initialize input).runNormalized batches).1.NoActiveCachedFailure := by
  have empty : (State.initialize input).NoActiveCachedFailure := by
    intro node member _
    cases cache : node.failure with
    | none => rfl
    | some errors => exact (createWorkQueue_cachedErrors input (fun _ _ => False)
        node member errors cache).elim
  exact empty.runNormalized (createWorkQueue_groupRefsUnique input) batches

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
