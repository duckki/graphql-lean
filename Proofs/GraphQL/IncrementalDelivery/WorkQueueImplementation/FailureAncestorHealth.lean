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

/-- A bounded rejection drain emits failures only at groups with healthy ancestors.
Witness: each success activates certified release ancestry; rejection visits active owners
under the same fixed health frame, even when one replay closes several owners.
-/
theorem HealthFrame.drainReadyGroups_go_failureAncestorHealth {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (fuel : Nat)
    : GroupFailureAncestorsHealthy work failed
        (State.drainReadyGroups.go fuel queue).2 := by
  induction fuel generalizing queue with
  | zero => exact .of_noFailures (by simp [State.drainReadyGroups.go])
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact .of_noFailures (by simp)
      · rename_i node selected
        obtain ⟨found, active, _⟩ := State.readyGroup_sound selected
        cases rejected : queue.rejectedTask? node with
        | none =>
            have member := List.mem_of_find?_eq_some found
            have safe := prior.counts.unrejected_tasks_notFailed prior.sound prior.tasks
              member rejected
            have closed := prior.finishGroupSuccess generated canonical failedKnown member active safe
            exact (GroupFailureAncestorsHealthy.of_noFailures
              (queue.finishGroupSuccess_groupFailure_absent node)).append
              (ih (closed.1.startNewWork _ closed.2.1))
        | some rejection =>
            obtain ⟨occurrence, errors⟩ := rejection
            exact (queue.taskFailure_failureAncestorHealth prior.roots occurrence errors).append
              (ih (prior.taskFailure occurrence errors))

/-- Full draining uses its actual live-record budget for failure ancestry health. -/
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
    : GroupFailureAncestorsHealthy work failed queue.drainReadyGroups.2 :=
  prior.drainReadyGroups_go_failureAncestorHealth generated canonical failedKnown
    queue.groupNodes.length

end ReleaseHealth
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
