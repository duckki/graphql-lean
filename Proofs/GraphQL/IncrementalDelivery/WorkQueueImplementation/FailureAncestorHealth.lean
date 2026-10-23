import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthFrame
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureOutput

/-! Observable failed completions retain healthy ancestry at their actual closure cut. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every failed group completion has healthy full ancestry under the fixed inventory. -/
def GroupFailureAncestorsHealthy (work : Execution.Work) (failed : List Occurrence)
    (events : List WorkQueueEvent)
    : Prop :=
  ∀ group errors,
    .groupFailure group errors ∈ events → GroupAncestorsHealthy work failed group.ref

/-- Concatenated failure outputs preserve ancestry health under one inventory. -/
theorem GroupFailureAncestorsHealthy.append {work failed before after}
    (first : GroupFailureAncestorsHealthy work failed before)
    (last : GroupFailureAncestorsHealthy work failed after)
    : GroupFailureAncestorsHealthy work failed (before ++ after) := by
  intro group errors member
  exact (List.mem_append.mp member).elim (first group errors) (last group errors)

/-- Output without group failures satisfies failure ancestry health vacuously. -/
theorem GroupFailureAncestorsHealthy.of_noFailures {work failed events}
    (absent : ∀ group errors, .groupFailure group errors ∉ events)
    : GroupFailureAncestorsHealthy work failed events := by
  intro group errors member
  exact False.elim (absent group errors member)

/-- The successful owner fold adds no failed group completions. -/
theorem GroupFailureAncestorsHealthy.successGroupFold {work failed}
    (groups : List Execution.DeliveryNode)
    (acc : State × List WorkQueueEvent × NewWork)
    (prior : GroupFailureAncestorsHealthy work failed acc.2.1)
    : GroupFailureAncestorsHealthy work failed
        (groups.foldl successGroupStep acc).2.1 := by
  induction groups generalizing acc with
  | nil => exact prior
  | cons group rest ih =>
      apply ih
      obtain ⟨queue, events, newWork⟩ := acc
      dsimp only [successGroupStep]
      split
      · exact prior
      · split
        · exact prior.append (.of_noFailures
            ((queue.putGroupNode _).finishGroupSuccess_groupFailure_absent _))
        · exact prior

/-- A rejection reports only active owners, whose ancestry is certified before each cut.
Witness: owner cleanup only shrinks the active ref set; task replacement changes no roots.
-/
theorem State.taskFailure_failureAncestorHealth {queue : State} {work failed}
    (roots : queue.RootAncestorsHealthy work failed) (occurrence : Occurrence)
    (errors : Nat)
    : GroupFailureAncestorsHealthy work failed
        (queue.taskFailure occurrence errors).2 := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (rooted : acc.1.RootAncestorsHealthy work failed)
      (output : GroupFailureAncestorsHealthy work failed acc.2)
      : GroupFailureAncestorsHealthy work failed
        (groups.foldl (failureGroupStep errors) acc).2 := by
    induction groups generalizing acc with
    | nil => exact output
    | cons group rest ih =>
        obtain ⟨current, events⟩ := acc
        dsimp only [List.foldl_cons, failureGroupStep]
        split
        · exact ih _ rooted output
        · rename_i node found
          split
          · rename_i active
            apply ih
            · exact fun ref member => rooted ref (current.removeGroup_rootsSubset _ member)
            · apply output.append
              intro reported count member
              have same := List.mem_singleton.mp member
              cases same
              apply rooted
              change node.group.node.ref ∈ current.rootGroups
              rw [current.groupNode?_ref found]
              exact List.contains_iff_mem.mp active
          · exact ih _ rooted output
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found, GroupFailureAncestorsHealthy]
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      exact loop task.task.groups _ roots
        (GroupFailureAncestorsHealthy.of_noFailures (by simp))

namespace ReleaseHealth

/-- Immediate drain output contains no failed group completion.
Startup failures occupy the separate queued channel, so this statement needs no health
assumption beyond the existing frame parameter retained for the handler interface.
-/
theorem HealthFrame.drainReadyGroups_go_failureAncestorHealth {queue work parents failed}
    (_prior : HealthFrame queue work parents failed) (_generated : ExecutedWork work)
    (_canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (_failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (fuel : Nat) (available : List (Occurrence × Nat) := [])
    : GroupFailureAncestorsHealthy work failed
        (State.drainReadyGroups.go available fuel queue).2.1 := by
  apply GroupFailureAncestorsHealthy.of_noFailures
  intro group errors
  clear _prior
  induction fuel generalizing queue with
  | zero => simp [State.drainReadyGroups.go]
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · simp
      · intro member
        rcases List.mem_append.mp member with first | later
        · exact queue.finishGroupSuccess_groupFailure_absent _ group errors first
        · exact ih later

/-- Full immediate draining specializes its actual live-record budget. -/
theorem HealthFrame.drainReadyGroups_failureAncestorHealth {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (available : List (Occurrence × Nat) := [])
    : GroupFailureAncestorsHealthy work failed (queue.drainReadyGroups available).2.1 :=
  prior.drainReadyGroups_go_failureAncestorHealth generated canonical failedKnown
    queue.groupNodes.length available

end ReleaseHealth
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
