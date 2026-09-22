import Proofs.GraphQL.IncrementalDelivery.WorkScheduler
import Tests.GraphQL.IncrementalDelivery.WorkScheduler

/-! Node-key lifecycle proofs for declarative work, without importing query/wire correctness. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkLifecycle

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkScheduler

/-! The work proof surface does not bring in wire correctness definitions. -/

#guard_msgs (drop info) in
#check_failure ExecutionObservation

/-- Every admitted prefix has unique node notices and completions, even for arbitrary raw
work.
-/
example (work : Work) (history : History) (h : AdmissiblePrefix work history)
    : history.UniqueKeys :=
  h.uniqueKeys

/-- Terminal histories close each initial/later key exactly once, using the general count
witness.
-/
example (work : Work) (history : History) (h : AdmissibleRun work history)
    : ∀ key ∈
        (history.initialGroups ++ history.initialStreams).map DeliveryNode.key
        ++ pendingKeys history.batches.flatten,
        (completedKeys history.batches.flatten).count key = 1 :=
  h.keysCompleteExactlyOnce

/-- Output accounting applies directly to a permitted atom, without internal progress
states.
-/
example (work : Work) (initial : Keys) (matching : PublicationMatching)
    (before : List WorkEvent) (failed : List Occurrence) (event : WorkEvent)
    (allowed : EventAllowed work initial matching before failed event)
    : (eventPending event).Nodup ∧ (eventCompleted event).Nodup :=
  ⟨allowed.accounting.pendingUnique, allowed.accounting.completedUnique⟩

def completed : History :=
  {
    initialGroups := [WorkScheduler.node],
    initialStreams := [],
    batches :=
      [[
        .groupValues WorkScheduler.node [{ path := [], data := [] }],
        .groupSuccess WorkScheduler.node [] [],
        .workQueueTermination
      ]]
  }

/-- The concrete terminal fixture satisfies the universal key-identity witness. -/
example : completed.UniqueKeys := WorkScheduler.completedRun.uniqueKeys

/-- Its initially announced key has one completion, by terminal liveness and uniqueness.
-/
example : (completedKeys completed.batches.flatten).count 0 = 1 :=
  WorkScheduler.completedRun.keysCompleteExactlyOnce 0 (by simp [WorkScheduler.node])

/-- Causal failure/cancellation retains the same terminal exactly-once guarantee. -/
example
    : (completedKeys [[WorkScheduler.failure, .workQueueTermination]].flatten).count 0
      = 1 :=
  WorkScheduler.failedRun.keysCompleteExactlyOnce 0 (by simp [WorkScheduler.node])

def stalled : History :=
  { initialGroups := [WorkScheduler.node], initialStreams := [], batches := [] }

/-- A stalled prefix is genuinely admitted, by valid initialization and an empty output
history.
-/
theorem stalledAdmitted : AdmissiblePrefix WorkScheduler.work stalled :=
  WorkScheduler.emptyHistory

/-- Prefix admission supplies uniqueness but does not imply terminal liveness. -/
example : stalled.UniqueKeys := stalledAdmitted.uniqueKeys

/-- The terminal count theorem rules out declaring this unfinished prefix a complete run.
-/
example : ¬AdmissibleRun WorkScheduler.work stalled := by
  intro done
  have count := done.keysCompleteExactlyOnce 0 (by simp [stalled, WorkScheduler.node])
  simp [stalled, completedKeys] at count

def duplicateCompletion : History :=
  {
    initialGroups := [WorkScheduler.node],
    initialStreams := [],
    batches :=
      [[.groupSuccess WorkScheduler.node [] [], .streamFailure WorkScheduler.node 2]]
  }

/-- Changing completion kind cannot hide duplicate keys in a prefix, by the general Nodup
witness.
-/
example (work : Work) : ¬AdmissiblePrefix work duplicateCompletion := by
  intro admitted
  have unique := admitted.uniqueKeys.2
  simp [duplicateCompletion, completedKeys, eventCompleted] at unique

/-- The same duplicate is also forbidden in any terminal history, independently of its
work metadata.
-/
example (work : Work) : ¬AdmissibleRun work duplicateCompletion := by
  intro admitted
  have unique := admitted.uniqueKeys.2
  simp [duplicateCompletion, completedKeys, eventCompleted] at unique

/-- A failure notification already in the prefix excludes a second closure of that key. -/
example (work : Work) (initial : Keys) (matching : PublicationMatching)
    (failed : List Occurrence) (event : WorkEvent)
    (allowed
      : EventAllowed work initial matching
          [.groupFailure WorkScheduler.node 2] failed event)
    : 0 ∉ eventCompleted event := by
  intro member
  exact (allowed.accounting.completion 0 member).2
    (by simp [completedKeys, eventCompleted, WorkScheduler.node])

def first : WorkEvent :=
  .streamValues WorkScheduler.node [{ item := .null }]
    [{ key := 1, path := [] }] [{ key := 2, path := [] }]

def second : WorkEvent :=
  .streamValues WorkScheduler.node [{ item := .null }]
    [{ key := 3, path := [] }] [{ key := 4, path := [] }]

def combined : WorkEvent :=
  .streamValues WorkScheduler.node [{ item := .null }, { item := .null }]
    [{ key := 1, path := [] }, { key := 3, path := [] }]
    [{ key := 2, path := [] }, { key := 4, path := [] }]

/-! Stream coalescing groups defer notices before stream notices, so exact list equality
is too strong.
-/

#guard pendingKeys [first, second] == [1, 2, 3, 4]
#guard pendingKeys [combined] == [1, 3, 2, 4]

/-- The permitted grouping still preserves every occurrence, by the relational grouping
theorem.
-/
example : (pendingKeys [combined]).Perm (pendingKeys [first, second]) :=
  (ValueGrouping.keyPermutation (.combine first (.separate second .nil) rfl)).pending

/-- Coalescing cannot deduplicate repeated announcements; occurrence preservation retains
both copies.
-/
example {merged : WorkEvent} (compatible : combineValues first first = some merged)
    : (pendingKeys [merged]).count 1 = 2 := by
  have preserved := (combineValues_keyPermutation compatible).pending
  rw [preserved.count_eq]
  decide

end GraphQL.IncrementalDelivery.Tests.WorkLifecycle
