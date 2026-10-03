import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthClosure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication

/-! Successful output carriers retain the record health proved at their closure boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Health is relative to the accepted failure inventory at the source-handler boundary
-----------------------------------------------------------------------------------------

/-- Every successful group carrier in `events` has a known healthy record under `failed`.
This is derived proof evidence, not an added admission rule or executable state field.
-/
def SuccessfulGroupsHealthy (work : Execution.Work) (failed : List Occurrence)
    (events : List WorkQueueEvent)
    : Prop :=
  ∀ group groups streams,
    Execution.WorkQueueEvent.groupSuccess group groups streams ∈ events
    → ∃ dependencies,
        GroupRecordAt work group dependencies
        ∧ ¬GroupRecordInvalidated work failed group.ref

/-- Empty output has no successful carrier requiring a health witness.
Witness: the membership premise is impossible. -/
theorem SuccessfulGroupsHealthy.nil (work : Execution.Work) (failed : List Occurrence)
    : SuccessfulGroupsHealthy work failed [] := by
  intro group groups streams impossible
  cases impossible

/-- Concatenation preserves carrier health under one fixed failure inventory.
Witness: split the carrier's membership between the two output segments. -/
theorem SuccessfulGroupsHealthy.append {work failed left right}
    (before : SuccessfulGroupsHealthy work failed left)
    (after : SuccessfulGroupsHealthy work failed right)
    : SuccessfulGroupsHealthy work failed (left ++ right) := by
  intro group groups streams member
  rcases List.mem_append.mp member with earlier | later
  · exact before group groups streams earlier
  · exact after group groups streams later

/-- Output with no successful group carrier needs no health certificate.
Witness: any such carrier would contradict its exclusion. -/
theorem SuccessfulGroupsHealthy.of_noGroupSuccess {work failed events}
    (absent
      : ∀ group groups streams,
          Execution.WorkQueueEvent.groupSuccess group groups streams ∉ events)
    : SuccessfulGroupsHealthy work failed events := by
  intro group groups streams member
  exact False.elim (absent group groups streams member)

-----------------------------------------------------------------------------------------
-- Exact errors and healthy ancestry justify each individual successful flush
-----------------------------------------------------------------------------------------

/-- A successful flush emits only its supplied healthy group as a success carrier.
Witness: exact error accounting excludes direct failure of an uncached group; healthy
ancestry excludes inherited failure. The flush output has just this one success carrier.
-/
theorem State.finishGroupSuccess_successfulGroupsHealthy {queue : State}
    {work failed dependencies} (generated : ExecutedWork work)
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {group : GroupNode} (live : group ∈ queue.groupNodes)
    (known : GroupRecordAt work group.group.node dependencies)
    (uncached : group.failure = none)
    (ancestors : GroupAncestorsHealthy work failed group.group.node.ref)
    : SuccessfulGroupsHealthy work failed (queue.finishGroupSuccess group).2.1 := by
  have healthy := counts.recordHealthy_of_ancestors generated live uncached known ancestors
    failedKnown
  intro carrier groups streams member
  obtain ⟨_, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications group
  rw [output] at member
  have same : carrier = group.group.node
      ∧ groups = (queue.finishGroupSuccess group).2.2.newGroups
      ∧ streams = (queue.finishGroupSuccess group).2.2.newStreams := by
    split at member <;> simpa using member
  exact ⟨dependencies, same.1 ▸ known, same.1 ▸ healthy⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
