import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureNotices

/-! Concrete retirement evidence for the ancestry of carried group notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every group noticed in `events` has its task-bearing ancestors retired in `queue`.
This records structural removal, not successful completion or scheduler admission.
-/
def State.GroupNoticeAncestorsRetired (queue : State) (work : Execution.Work)
    (events : List WorkQueueEvent)
    : Prop :=
  ∀ key ∈ events.flatMap rawGroupNoticeKeys, queue.AncestorsRetired work key

/-- An output with no group notices has no ancestor-retirement obligation.
Witness: each candidate notice would belong to an empty event projection.
-/
theorem State.GroupNoticeAncestorsRetired.of_noNotices {queue : State} {work events}
    (absent : ∀ event ∈ events, rawGroupNoticeKeys event = [])
    : queue.GroupNoticeAncestorsRetired work events := by
  intro key member
  obtain ⟨event, included, noticed⟩ := List.mem_flatMap.mp member
  rw [absent event included] at noticed
  cases noticed

/-- Notice ancestry survives any transition preserving permanent retirement.
Witness: transport each notice's ancestor certificate to the later queue.
-/
theorem State.GroupNoticeAncestorsRetired.mono {before after : State} {work events}
    (prior : before.GroupNoticeAncestorsRetired work events)
    (preserved : ∀ key, before.RetiredGroup key → after.RetiredGroup key)
    : after.GroupNoticeAncestorsRetired work events :=
  fun key member => (prior key member).mono preserved

/-- Certificates at the same queue compose over successive output segments.
Witness: a noticed key belongs to one of the two segments.
-/
theorem State.GroupNoticeAncestorsRetired.append {queue : State} {work first later}
    (left : queue.GroupNoticeAncestorsRetired work first)
    (right : queue.GroupNoticeAncestorsRetired work later)
    : queue.GroupNoticeAncestorsRetired work (first ++ later) := by
  intro key member
  rw [List.flatMap_append] at member
  exact (List.mem_append.mp member).elim (left key) (right key)

/-- A bounded drain cannot recreate an already retired group.
Witness: both closure branches preserve retirement, as does child activation.
-/
theorem State.RetiredGroup.drainReadyGroups_go {queue : State} {key}
    (retired : queue.RetiredGroup key) (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.RetiredGroup key := by
  apply State.drainReadyGroups_go_preserves (fun state => state.RetiredGroup key)
    (fun _ node prior _ _ _ _ => (prior.finishGroupSuccess node).startNewWork _)
    (fun _ node _ prior _ _ _ => prior.removeGroup node.group.node.key) retired

/-- Successful release's exact notice list inherits the pruned frontier's certificates.
Witness: the actual output and release list have the same group-key projection.
-/
theorem State.finishGroupSuccess_noticeAncestorRetirement {queue : State} {work node}
    (protectedRoots
      : ∀ child ∈ (queue.finishGroupSuccess node).2.2.newGroups,
          (queue.finishGroupSuccess node).1.AncestorsRetired work child.key)
    : (queue.finishGroupSuccess node).1.GroupNoticeAncestorsRetired work
        (queue.finishGroupSuccess node).2.1 := by
  intro key member
  rw [← State.finishGroupSuccess_groupNotices] at member
  obtain ⟨child, included, same⟩ := List.mem_map.mp member
  exact same ▸ protectedRoots child included

/-- Owner-fold notices have the same retired ancestry as its accumulated release frontier.
Witness: the exact key-list identity retains silent pruning and repeated descriptors.
-/
theorem State.successGroupFold_noticeAncestorRetirement {queue : State} {work}
    {groups : List Execution.DeliveryNode}
    (protectedRoots
      : ∀ child ∈ (groups.foldl successGroupStep (queue, [], {})).2.2.newGroups,
          (groups.foldl successGroupStep (queue, [], {})).1.AncestorsRetired work
            child.key)
    : (groups.foldl successGroupStep (queue, [], {})).1.GroupNoticeAncestorsRetired work
        (groups.foldl successGroupStep (queue, [], {})).2.1 := by
  intro key member
  rw [← successGroupFold_groupNotices] at member
  obtain ⟨child, included, same⟩ := List.mem_map.mp member
  exact same ▸ protectedRoots child included

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
