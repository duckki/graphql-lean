import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MissingParentHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureNotices

/-! Carried group notices preserve the health of their entire defer ancestry. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every announced group in `events` has healthy ancestry under accepted failures `failed`.
The child itself may have a cached failure. This is derived source-boundary evidence,
not a host-source law or a claim that all dependencies have already published.
-/
def GroupNoticeAncestorsHealthy (work : Execution.Work) (failed : List Occurrence)
    (events : List WorkQueueEvent)
    : Prop :=
  ∀ key ∈ events.flatMap rawGroupNoticeKeys, GroupAncestorsHealthy work failed key

/-- An output segment with no group notices has no ancestor-health obligation.
Witness: every notice-key membership would belong to one of the empty projections.
-/
theorem GroupNoticeAncestorsHealthy.of_noNotices {work failed events}
    (absent : ∀ event ∈ events, rawGroupNoticeKeys event = [])
    : GroupNoticeAncestorsHealthy work failed events := by
  intro key member
  obtain ⟨event, included, noticed⟩ := List.mem_flatMap.mp member
  rw [absent event included] at noticed
  cases noticed

/-- Fixed-inventory ancestry health composes in the original output order.
Witness: each notice belongs to one of the two output segments.
-/
theorem GroupNoticeAncestorsHealthy.append {work failed first later}
    (left : GroupNoticeAncestorsHealthy work failed first)
    (right : GroupNoticeAncestorsHealthy work failed later)
    : GroupNoticeAncestorsHealthy work failed (first ++ later) := by
  intro key member
  rw [List.flatMap_append] at member
  exact (List.mem_append.mp member).elim (left key) (right key)

/-- Successful release emits exactly the frontier whose ancestor health was established.
Witness: the key projection of the actual pruned release list equals its notice output.
-/
theorem State.finishGroupSuccess_noticeAncestorHealth {queue : State} {work failed node}
    (healthy
      : ∀ child ∈ (queue.finishGroupSuccess node).2.2.newGroups,
          GroupAncestorsHealthy work failed child.key)
    : GroupNoticeAncestorsHealthy work failed (queue.finishGroupSuccess node).2.1 := by
  intro key member
  rw [← State.finishGroupSuccess_groupNotices] at member
  obtain ⟨child, included, same⟩ := List.mem_map.mp member
  exact same ▸ healthy child included

/-- The whole owner-fold output shares the health of its exact pending release frontier.
Witness: emitted notice keys and accumulated release keys coincide, without deduplication.
-/
theorem State.successGroupFold_noticeAncestorHealth {queue : State} {work failed}
    {groups : List Execution.DeliveryNode}
    (healthy
      : ∀ child ∈ (groups.foldl successGroupStep (queue, [], {})).2.2.newGroups,
          GroupAncestorsHealthy work failed child.key)
    : GroupNoticeAncestorsHealthy work failed
        (groups.foldl successGroupStep (queue, [], {})).2.1 := by
  intro key member
  rw [← successGroupFold_groupNotices] at member
  obtain ⟨child, included, same⟩ := List.mem_map.mp member
  exact same ▸ healthy child included

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
