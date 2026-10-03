import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorRootCoverage

/-! Failure cleanup preserves coverage of every surviving healthy task contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An operation that cannot recreate absent refs has no new surviving lookup.
Witness: case-split the earlier lookup; absence preservation rules out the missing case.
-/
private theorem earlier_lookup {before after : State} {ref}
    (noRevival : before.groupNode? ref = none → after.groupNode? ref = none)
    (survives : ∃ node, after.groupNode? ref = some node)
    : ∃ node, before.groupNode? ref = some node := by
  cases found : before.groupNode? ref with
  | some node => exact ⟨node, rfl⟩
  | none =>
      obtain ⟨node, lookup⟩ := survives
      rw [noRevival found] at lookup
      contradiction

-----------------------------------------------------------------------------------------
-- Pointwise root coverage through the original sequential failure fold
-----------------------------------------------------------------------------------------

/-- A failed task cannot disconnect a root-covered group that survives its cleanup.
Witness: the fold preserves its removal forest; immediate failure removes whole subtrees,
whereas cached failure changes only counters. The proof needs no semantic health premise.
-/
theorem State.taskFailure_root_coverage {queue : State} {parents target}
    (unique : queue.GroupRefsUnique) (forest : queue.RemovalForest parents)
    (occurrence : Occurrence) (errors : Nat)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    (survives
      : ∃ node, (queue.taskFailure occurrence errors).1.groupNode? target = some node)
    : ∃ root ∈ (queue.taskFailure occurrence errors).1.rootGroups,
        (queue.taskFailure occurrence errors).1.LiveDescendant root target := by
  let property (current : State) := current.GroupRefsUnique ∧ current.RemovalForest parents
    ∧ ((∃ node, current.groupNode? target = some node)
      → ∃ root ∈ current.rootGroups, current.LiveDescendant root target)
  have step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (prior : property acc.1) : property (failureGroupStep errors acc group).1 := by
    obtain ⟨current, events⟩ := acc
    dsimp only [failureGroupStep]
    split
    · exact prior
    · rename_i node found
      split
      · refine ⟨prior.1.finishGroupFailure node errors,
          prior.2.1.removeGroup node.group.node.ref, ?_⟩
        intro live
        have earlier := earlier_lookup
          (fun absent => State.removeGroup_groupNodeAbsent absent node.group.node.ref) live
        exact State.removeGroup_root_coverage prior.2.1 _ (prior.2.2 earlier) live
      · refine ⟨prior.1.putGroupNode _,
          prior.2.1.putCounters prior.1 found _ _, ?_⟩
        intro live
        have earlier := earlier_lookup
          (fun absent => State.putCounters_groupNodeAbsent absent
            (node.pending - 1) (some (node.failure.getD 0 + errors))) live
        obtain ⟨root, active, path⟩ := prior.2.2 earlier
        exact ⟨root, active, path.putCounters prior.1 found _ _⟩
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : property acc.1)
      : property (groups.foldl (failureGroupStep errors) acc).1 := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih => exact ih _ (step acc group prior)
  have removedCoverage : ∃ root ∈ (queue.removeTask occurrence).rootGroups,
      (queue.removeTask occurrence).LiveDescendant root target := by
    obtain ⟨root, active, path⟩ := covered
    exact ⟨root, active, path.removeTask occurrence⟩
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using covered
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found] at survives ⊢
      split
      · exact removedCoverage
      · rename_i guarded
        simp only [guarded] at survives
        exact (loop node.task.groups (queue.removeTask occurrence, [])
          ⟨unique.removeTask occurrence, forest.removeTask occurrence,
            fun _ => removedCoverage⟩).2.2 survives

-----------------------------------------------------------------------------------------
-- Contributor coverage across failures and stream completion
-----------------------------------------------------------------------------------------

/-- Task failure preserves root coverage for healthy surviving permanent contributors.
Witness: task registration is unchanged, absent groups cannot revive, and pointwise
failure-fold coverage applies. Additional accepted failures may subsequently narrow health.
-/
theorem State.HealthyContributorsCovered.taskFailure {queue : State} {work failed parents}
    (covered : queue.HealthyContributorsCovered work failed)
    (unique : queue.GroupRefsUnique) (forest : queue.RemovalForest parents)
    (registered : queue.TaskGroupsRegistered)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.HealthyContributorsCovered work failed := by
  intro task member ref contributes healthy survives
  rw [State.taskFailure_tasks] at member
  have earlier := earlier_lookup
    (fun absent => ((State.RetiredGroup.of_lookup_none
      (registered task member ref contributes) absent).taskFailure occurrence errors).lookup_none)
    survives
  exact State.taskFailure_root_coverage unique forest occurrence errors
    (covered task member ref contributes healthy earlier) survives

/-- Stream exhaustion does not alter group contributor coverage.
Witness: only the active stream-ref list changes; the same group roots and paths remain.
-/
theorem State.HealthyContributorsCovered.streamSuccess {queue : State} {work failed}
    (covered : queue.HealthyContributorsCovered work failed)
    (stream : Execution.DeliveryNode)
    : (queue.streamSuccess stream).1.HealthyContributorsCovered work failed := by
  unfold State.streamSuccess
  split
  · intro task member ref contributes healthy live
    obtain ⟨root, active, path⟩ := covered task member ref contributes healthy live
    exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩
  · exact covered

/-- Stream failure does not alter group contributor coverage.
Witness: the handler closes only the stream, preserving every concrete group-root path.
-/
theorem State.HealthyContributorsCovered.streamFailure {queue : State} {work failed}
    (covered : queue.HealthyContributorsCovered work failed)
    (stream : Execution.DeliveryNode) (errors : Nat)
    : (queue.streamFailure stream errors).1.HealthyContributorsCovered work failed := by
  unfold State.streamFailure
  split
  · intro task member ref contributes healthy live
    obtain ⟨root, active, path⟩ := covered task member ref contributes healthy live
    exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩
  · exact covered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
