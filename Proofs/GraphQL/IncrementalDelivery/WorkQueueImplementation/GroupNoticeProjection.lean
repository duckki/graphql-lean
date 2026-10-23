import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDebt

/-! Raw group-notice projections and exact successful-release frontiers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Group refs announced by a raw carrier; stream notices are deliberately excluded. -/
def rawGroupNoticeRefs : WorkQueueEvent → NodeRefs
  | .groupSuccess _ groups _ | .streamValues _ _ groups _ =>
      groups.map Execution.DeliveryNode.ref
  | _ => []

/-- A failed group closure references its own ref, not any newly released child. -/
def rawGroupFailureRefs : WorkQueueEvent → NodeRefs
  | .groupFailure group _ => [group.ref]
  | _ => []

/-- A successful flush announces exactly the group roots returned for activation.
Witness: its optional values carry no notices; its final success carries the release list.
-/
theorem State.finishGroupSuccess_groupNotices (queue : State) (node : GroupNode)
    : (queue.finishGroupSuccess node).2.2.newGroups.map Execution.DeliveryNode.ref
      = (queue.finishGroupSuccess node).2.1.flatMap rawGroupNoticeRefs := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output, List.flatMap_append]
  split <;> simp [rawGroupNoticeRefs]

/-- The owner fold's pending frontier contains exactly its emitted group-notice refs.
Witness: each successful step appends the same pruned frontier to output and new work;
missing/counter-only steps change neither list. No freshness premise is needed.
-/
theorem successGroupFold_groupNotices (queue : State)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl successGroupStep (queue, [], {})).2.2.newGroups.map
        Execution.DeliveryNode.ref
      = (groups.foldl successGroupStep (queue, [], {})).2.1.flatMap
          rawGroupNoticeRefs := by
  have loop (more : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (same : acc.2.2.newGroups.map Execution.DeliveryNode.ref
        = acc.2.1.flatMap rawGroupNoticeRefs)
      : (more.foldl successGroupStep acc).2.2.newGroups.map Execution.DeliveryNode.ref
        = (more.foldl successGroupStep acc).2.1.flatMap rawGroupNoticeRefs := by
    induction more generalizing acc with
    | nil => exact same
    | cons group rest ih =>
        apply ih
        dsimp only [successGroupStep]
        split
        · exact same
        · split
          · simp only [List.map_append, List.flatMap_append, same,
              State.finishGroupSuccess_groupNotices]
          · exact same
  exact loop groups (queue, [], {}) rfl

/-- Task failure emits no group-announcement carrier. -/
theorem State.taskFailure_groupNotices (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).2.flatMap rawGroupNoticeRefs = [] := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      : (groups.foldl (failureGroupStep errors) acc).2.flatMap rawGroupNoticeRefs
        = acc.2.flatMap rawGroupNoticeRefs := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih]
        obtain ⟨current, output⟩ := acc
        dsimp only [failureGroupStep]
        split
        · rfl
        · split
          · simp [State.finishGroupFailure, List.flatMap_append, rawGroupNoticeRefs]
          · rfl
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found]
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact loop _ (_, [])

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
