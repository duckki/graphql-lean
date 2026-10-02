import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupKeys

/-! Induction over the executable release-time drain, without source assumptions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- A predicate survives draining when it survives each selected closure and activation.
Witness: induction on the drain's live-node budget; lookup supplies a live active node,
and a selected healthy node must have a zero pending counter.
-/
theorem State.drainReadyGroups_go_preserves (invariant : State → Prop)
    (success
      : ∀ queue node,
          invariant queue
          → node ∈ queue.groupNodes
          → node.group.node.key ∈ queue.rootGroups
          → node.failure = none
          → node.pending = 0
          → invariant
              ((queue.finishGroupSuccess node).1.startNewWork
                (queue.finishGroupSuccess node).2.2))
    (failure
      : ∀ queue node errors,
          invariant queue
          → node ∈ queue.groupNodes
          → node.group.node.key ∈ queue.rootGroups
          → node.failure = some errors
          → invariant (queue.finishGroupFailure node errors).1)
    {queue : State} (valid : invariant queue) (fuel : Nat)
    : invariant (State.drainReadyGroups.go fuel queue).1 := by
  have loop (fuel : Nat) (current : State) (valid : invariant current)
      : invariant (State.drainReadyGroups.go fuel current).1 := by
    induction fuel generalizing current with
    | zero => exact valid
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact valid
        · rename_i node selected
          obtain ⟨key, active, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : current.groupNode? key with
          | none => simp [found] at choice
          | some candidate =>
              simp only [found] at choice
              change (if candidate.failure.isSome || candidate.pending == 0 then
                some candidate else none) = some node at choice
              split at choice
              · rename_i ready
                have equal := Option.some.inj choice
                subst candidate
                have member := List.mem_of_find?_eq_some found
                have root := current.groupNode?_key found ▸ active
                cases failed : node.failure with
                | none =>
                    have zero : node.pending = 0 := by simpa [failed] using ready
                    exact ih _ (success current node valid member root failed zero)
                | some errors =>
                    exact ih _ (failure current node errors valid member root failed)
              · contradiction
  exact loop fuel queue valid

/-- The complete release drain inherits the arbitrary-budget induction principle.
Witness: specialize to the implementation's initial live-group count.
-/
theorem State.drainReadyGroups_preserves (invariant : State → Prop)
    (success
      : ∀ queue node,
          invariant queue
          → node ∈ queue.groupNodes
          → node.group.node.key ∈ queue.rootGroups
          → node.failure = none
          → node.pending = 0
          → invariant
              ((queue.finishGroupSuccess node).1.startNewWork
                (queue.finishGroupSuccess node).2.2))
    (failure
      : ∀ queue node errors,
          invariant queue
          → node ∈ queue.groupNodes
          → node.group.node.key ∈ queue.rootGroups
          → node.failure = some errors
          → invariant (queue.finishGroupFailure node errors).1)
    {queue : State} (valid : invariant queue)
    : invariant queue.drainReadyGroups.1 :=
  State.drainReadyGroups_go_preserves invariant success failure valid
    queue.groupNodes.length

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
