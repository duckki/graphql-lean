import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain

/-! Thread both queue state and the actual accumulated outputs through release draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- An output-aware invariant survives each actual drain closure and its activation.
Witness: induction over the executable budget and exact output concatenation. Callback
premises expose live/active record facts, not assumed output-admission properties.
-/
theorem State.drainReadyGroups_go_outputPreserves
    (invariant : State → List Execution.WorkQueueEvent → Prop)
    (success
      : ∀ queue history node,
          invariant queue history
          → node ∈ queue.groupNodes
          → node.group.node.ref ∈ queue.rootGroups
          → queue.rejectedTask? node = none
          → node.pending = 0
          → invariant
              ((queue.finishGroupSuccess node).1.startNewWork
                (queue.finishGroupSuccess node).2.2)
              (history ++ (queue.finishGroupSuccess node).2.1))
    (failure
      : ∀ queue history node occurrence errors,
          invariant queue history
          → node ∈ queue.groupNodes
          → node.group.node.ref ∈ queue.rootGroups
          → queue.rejectedTask? node = some (occurrence, errors)
          → invariant (queue.taskFailure occurrence errors).1
              (history ++ (queue.taskFailure occurrence errors).2))
    {queue history} (valid : invariant queue history) (fuel : Nat)
    : invariant (State.drainReadyGroups.go fuel queue).1
        (history ++ (State.drainReadyGroups.go fuel queue).2) := by
  induction fuel generalizing queue history with
  | zero => simpa only [State.drainReadyGroups.go, List.append_nil] using valid
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · simpa only [List.append_nil] using valid
      · rename_i node selected
        obtain ⟨ref, active, choice⟩ := List.exists_of_findSome?_eq_some selected
        cases found : queue.groupNode? ref with
        | none => simp [found] at choice
        | some candidate =>
            simp only [found] at choice
            change (if (queue.rejectedTask? candidate).isSome || candidate.pending == 0 then
              some candidate else none) = some node at choice
            split at choice
            · rename_i ready
              have equal := Option.some.inj choice
              subst candidate
              have member := List.mem_of_find?_eq_some found
              have root := queue.groupNode?_ref found ▸ active
              cases failed : queue.rejectedTask? node with
              | none =>
                  have zero : node.pending = 0 := by simpa [failed] using ready
                  simpa only [List.append_assoc]
                    using ih (success queue history node valid member root failed zero)
              | some rejection =>
                  obtain ⟨occurrence, errors⟩ := rejection
                  simpa only [List.append_assoc]
                    using ih
                      (failure queue history node occurrence errors valid member root
                        failed)
            · contradiction

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
