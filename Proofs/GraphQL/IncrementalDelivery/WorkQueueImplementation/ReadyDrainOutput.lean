import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain

/-! Thread queue state and immediate outputs through release draining.
Startup failure notices remain separate transition results for later batch forwarding.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

/-- An output-aware invariant survives each actual successful closure and activation.
Witness: induction over the executable budget and exact immediate-output concatenation.
-/
theorem State.drainReadyGroups_go_outputPreserves
    (invariant : State → List Execution.WorkQueueEvent → Prop)
    {available : List (Occurrence × Nat)}
    (success
      : ∀ queue history node,
          invariant queue history
          → node ∈ queue.groupNodes
          → node.group.node.ref ∈ queue.rootGroups
          → node.pending = 0
          → invariant
              ((queue.finishGroupSuccess node).1.startNewWork
                (queue.finishGroupSuccess node).2.2 available).1
              (history ++ (queue.finishGroupSuccess node).2.1))
    {queue history} (valid : invariant queue history) (fuel : Nat)
    : invariant (State.drainReadyGroups.go available fuel queue).1
        (history ++ (State.drainReadyGroups.go available fuel queue).2.1) := by
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
            change (if candidate.pending == 0 then some candidate else none) = some node at choice
            split at choice
            · rename_i ready
              have equal := Option.some.inj choice
              subst candidate
              have member := List.mem_of_find?_eq_some found
              have root := queue.groupNode?_ref found ▸ active
              have zero : node.pending = 0 := by simpa using ready
              simpa only [List.append_assoc]
                using ih (success queue history node valid member root zero)
            · contradiction

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
