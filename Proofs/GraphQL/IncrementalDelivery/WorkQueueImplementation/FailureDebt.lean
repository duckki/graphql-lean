import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalBasics

/-! Failed settlements discharge counter debt before latent error retention. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Removing groups leaves the exact debt of every survivor unchanged.
Witness: the implementation filters live group nodes without changing their fields.
-/
theorem State.PendingDebt.removeGroup {queue : State} {eligible settled remaining}
    (tracks : queue.PendingDebt eligible settled remaining) (ref : NodeRef)
    : (queue.removeGroup ref).PendingDebt eligible settled remaining := by
  intro node member relevant
  exact tracks node (List.mem_filter.mp member).1 relevant

/-- The literal failure-owner fold, named only for induction proofs.
Active owners close immediately; latent owners pay one decrement and cache their error.
-/
def failureGroupStep (errors : Nat) (acc : State × List WorkQueueEvent)
    (group : Execution.DeliveryNode)
    : State × List WorkQueueEvent :=
  let (current, events) := acc
  match current.groupNode? group.ref with
  | none => (current, events)
  | some node =>
      if current.rootGroups.contains group.ref then
        let (next, failure) := current.finishGroupFailure node errors
        (next, events ++ [failure])
      else
        (
          current.putGroupNode
            {
              node with
                pending := node.pending - 1
                failure := some (node.failure.getD 0 + errors)
            },
          events
        )

/-- Each failed contributor either disappears or pays its single decrement debt.
Witness: induction over distinct contributor refs, retaining any invariant preserved by
group removal and latent error updates. No claim is made for inconsistent raw ledgers.
-/
theorem failureGroupFold_preserves (eligible : Nat → Prop) (settled : List Occurrence)
    (invariant : State → Prop)
    (refs : ∀ queue, invariant queue → queue.GroupRefsUnique)
    (decrement
      : ∀ queue (node : GroupNode) errors,
          invariant queue
          → queue.groupNode? node.group.node.ref = some node
          → invariant
              (queue.putGroupNode
                {
                  node with
                    pending := node.pending - 1
                    failure := some (node.failure.getD 0 + errors)
                }))
    (remove : ∀ queue ref, invariant queue → invariant (queue.removeGroup ref))
    (errors : Nat) (groups : List Execution.DeliveryNode)
    (unique : (groups.map Execution.DeliveryNode.ref).Nodup)
    (acc : State × List WorkQueueEvent) (valid : invariant acc.1)
    (tracks : acc.1.PendingDebt eligible settled (groups.map Execution.DeliveryNode.ref))
    : invariant (groups.foldl (failureGroupStep errors) acc).1
      ∧ (groups.foldl (failureGroupStep errors) acc).1.PendingDebt eligible settled
          [] := by
  induction groups generalizing acc with
  | nil => exact ⟨valid, tracks⟩
  | cons group rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      have step : invariant (failureGroupStep errors acc group).1
          ∧ (failureGroupStep errors acc group).1.PendingDebt eligible settled
              (rest.map Execution.DeliveryNode.ref) := by
        obtain ⟨queue, events⟩ := acc
        dsimp only [failureGroupStep]
        cases found : queue.groupNode? group.ref with
        | none => exact ⟨valid, tracks.skipMissing found⟩
        | some node =>
            dsimp only
            split
            · have same := queue.groupNode?_ref found
              change invariant (queue.removeGroup node.group.node.ref)
                ∧ (queue.removeGroup node.group.node.ref).PendingDebt eligible settled _
              rw [same]
              exact ⟨remove queue group.ref valid,
                (tracks.removeGroup group.ref).skipMissing
                  (queue.removeGroup_ownGroupAbsent group.ref)⟩
            · have same := queue.groupNode?_ref found
              exact ⟨decrement queue node errors valid (same ▸ found),
                tracks.decrement (refs queue valid) absent found
                  (some (node.failure.getD 0 + errors))⟩
      exact ih tailUnique (failureGroupStep errors acc group) step.1 step.2

/-- Task failure removes membership, then either ignores cancellation or records errors.
Witness: definitional equality, retaining the pre-settlement healthy-owner guard.
-/
theorem State.taskFailure_eq {queue : State} (occurrence : Occurrence) (errors : Nat)
    (node : TaskNode) (found : queue.taskNode? occurrence = some node)
    : queue.taskFailure occurrence errors
      = if !queue.taskHasHealthyOwner node.task then
          (queue.removeTask occurrence, [])
        else
          node.task.groups.foldl (failureGroupStep errors)
            (queue.removeTask occurrence, []) := by
  simp only [State.taskFailure, found]
  rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
