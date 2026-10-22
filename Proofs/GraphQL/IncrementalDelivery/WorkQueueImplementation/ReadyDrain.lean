import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRefs

/-! Induction over the executable release-time drain, without source assumptions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

/-- A predicate survives draining when it survives successful closure and activation.
Witness: induction on the live-node budget. The drain selects only zero-pending active
nodes; cached rejections in newly released work are handled by startup.
-/
theorem State.drainReadyGroups_go_preserves (invariant : State → Prop)
    {available : List (Occurrence × Nat)}
    (success
      : ∀ queue node,
          invariant queue
          → node ∈ queue.groupNodes
          → node.group.node.ref ∈ queue.rootGroups
          → node.pending = 0
          → invariant
              ((queue.finishGroupSuccess node).1.startNewWork
                (queue.finishGroupSuccess node).2.2 available).1)
    {queue : State} (valid : invariant queue) (fuel : Nat)
    : invariant (State.drainReadyGroups.go available fuel queue).1 := by
  have loop (fuel : Nat) (current : State) (valid : invariant current)
      : invariant (State.drainReadyGroups.go available fuel current).1 := by
    induction fuel generalizing current with
    | zero => exact valid
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact valid
        · rename_i node selected
          obtain ⟨ref, active, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : current.groupNode? ref with
          | none => simp [found] at choice
          | some candidate =>
              simp only [found] at choice
              change (if candidate.pending == 0 then some candidate else none) = some node at choice
              split at choice
              · rename_i ready
                have equal := Option.some.inj choice
                subst candidate
                have member := List.mem_of_find?_eq_some found
                have root := current.groupNode?_ref found ▸ active
                have zero : node.pending = 0 := by simpa using ready
                exact ih _ (success current node valid member root zero)
              · contradiction
  exact loop fuel queue valid

/-- The complete release drain inherits the arbitrary-budget induction principle. -/
theorem State.drainReadyGroups_preserves (invariant : State → Prop)
    {available : List (Occurrence × Nat)}
    (success
      : ∀ queue node,
          invariant queue
          → node ∈ queue.groupNodes
          → node.group.node.ref ∈ queue.rootGroups
          → node.pending = 0
          → invariant
              ((queue.finishGroupSuccess node).1.startNewWork
                (queue.finishGroupSuccess node).2.2 available).1)
    {queue : State} (valid : invariant queue)
    : invariant (queue.drainReadyGroups available).1 :=
  State.drainReadyGroups_go_preserves invariant success valid queue.groupNodes.length

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
