import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthFrame
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebtBound

/-! The successful owner fold derives healthy closures from its actual pending debt. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics
namespace ReleaseHealth

/-- One owner step preserves health and the exact remaining decrement budget.
Witness: a zero counter bounds every flushed membership by successful settlements;
source disjointness therefore excludes failed contributors without a runtime guard.
-/
theorem HealthFrame.contributor {acc : State × List WorkQueueEvent × NewWork}
    {work parents failed settled remaining}
    (prior : HealthFrame acc.1 work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (safe : ∀ occurrence ∈ settled, occurrence ∉ failed)
    (released : ∀ group ∈ acc.2.2.newGroups, GroupAncestorsHealthy work failed group.ref)
    (output : SuccessfulGroupsHealthy work failed acc.2.1)
    (group : Execution.DeliveryNode) (fresh : group.ref ∉ remaining)
    (debt : acc.1.PendingDebtBound (fun _ => True) settled (group.ref :: remaining))
    : HealthFrame (successGroupStep acc group).1 work parents failed
      ∧ (∀ child ∈ (successGroupStep acc group).2.2.newGroups,
          GroupAncestorsHealthy work failed child.ref)
      ∧ SuccessfulGroupsHealthy work failed (successGroupStep acc group).2.1
      ∧ (successGroupStep acc group).1.PendingDebtBound (fun _ => True) settled
          remaining := by
  obtain ⟨current, events, newWork⟩ := acc
  dsimp only [successGroupStep]
  split
  · rename_i missing
    exact ⟨prior, released, output, debt.skipMissing missing⟩
  · rename_i node found
    let updated := { node with pending := node.pending - 1 }
    let next := current.putGroupNode updated
    have member := List.mem_of_find?_eq_some found
    have nextFrame : HealthFrame next work parents failed :=
      ⟨prior.groups.putGroupNode _ (prior.groups node member),
        prior.links.putGroupNode _ (prior.links node member),
        prior.counts.putGroupNodeSameTasks prior.refs node member _ rfl rfl,
        prior.retired.putGroupNode _, prior.roots, prior.refs.putGroupNode _,
        prior.sound.putGroupNode _ (prior.sound node member), prior.tasks.putGroupNode _,
        prior.live.putGroupNode _ (prior.live node member)⟩
    have nextDebt := debt.decrement prior.refs fresh found
    split
    · rename_i finishes
      have flags := Bool.and_eq_true_iff.mp finishes
      have active : updated.group.node.ref ∈ next.rootGroups := by
        change node.group.node.ref ∈ current.rootGroups
        rw [current.groupNode?_ref found]
        simpa only [State.putGroupNode, List.contains_iff_mem] using flags.1
      have zero : updated.pending = 0 := by simpa using flags.2
      have updatedMember : updated ∈ next.groupNodes :=
        List.mem_map.mpr ⟨node, member, by simp [updated]⟩
      have all := nextDebt.allSettled updatedMember trivial zero
      have notFailed : ∀ occurrence ∈ updated.tasks, occurrence ∉ failed :=
        fun occurrence member => safe occurrence (all occurrence member)
      have closed := nextFrame.finishGroupSuccess generated canonical failedKnown
        updatedMember active notFailed
      refine ⟨closed.1, ?_, output.append closed.2.2,
        nextDebt.finishGroupSuccess updated all⟩
      intro child included
      exact (List.mem_append.mp included).elim (released child) (closed.2.1 child)
    · exact ⟨nextFrame, released, output, nextDebt⟩

/-- The full single-pass owner fold preserves state health, releases, and success carriers.
Witness: each owner consumes one pending token; unique owner refs retain the remaining
budget. No rejected-task or ancestor-health test is inserted into executable settlement.
-/
theorem HealthFrame.successGroupFold {queue work parents failed settled}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (safe : ∀ occurrence ∈ settled, occurrence ∉ failed)
    (groups : List Execution.DeliveryNode)
    (unique : (groups.map Execution.DeliveryNode.ref).Nodup)
    (debt
      : queue.PendingDebtBound (fun _ => True) settled
          (groups.map Execution.DeliveryNode.ref))
    : let final := groups.foldl successGroupStep (queue, [], {})
      HealthFrame final.1 work parents failed
      ∧ (∀ child ∈ final.2.2.newGroups, GroupAncestorsHealthy work failed child.ref)
      ∧ SuccessfulGroupsHealthy work failed final.2.1
      ∧ final.1.PendingBound (fun _ => True) settled := by
  have loop (more : List Execution.DeliveryNode)
      (unique : (more.map Execution.DeliveryNode.ref).Nodup)
      (acc : State × List WorkQueueEvent × NewWork)
      (frame : HealthFrame acc.1 work parents failed)
      (released : ∀ group ∈ acc.2.2.newGroups, GroupAncestorsHealthy work failed group.ref)
      (output : SuccessfulGroupsHealthy work failed acc.2.1)
      (debt : acc.1.PendingDebtBound (fun _ => True) settled
        (more.map Execution.DeliveryNode.ref))
      : HealthFrame (more.foldl successGroupStep acc).1 work parents failed
        ∧ (∀ child ∈ (more.foldl successGroupStep acc).2.2.newGroups,
            GroupAncestorsHealthy work failed child.ref)
        ∧ SuccessfulGroupsHealthy work failed (more.foldl successGroupStep acc).2.1
        ∧ (more.foldl successGroupStep acc).1.PendingBound (fun _ => True) settled := by
    induction more generalizing acc with
    | nil => exact ⟨frame, released, output, debt.toBound⟩
    | cons group rest ih =>
        have next := frame.contributor generated canonical failedKnown safe released output
          group (List.nodup_cons.mp unique).1 debt
        exact ih (List.nodup_cons.mp unique).2 _ next.1 next.2.1 next.2.2.1 next.2.2.2
  exact loop groups unique (queue, [], {}) prior (by simp) (.nil work failed) debt

end ReleaseHealth
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
