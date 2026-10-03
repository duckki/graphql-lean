import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics
import Tests.GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! Node-ref lifecycle proofs for declarative work, without importing query/wire correctness. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkLifecycle

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! The work proof surface does not bring in wire correctness definitions. -/

#guard_msgs (drop info) in
#check_failure ExecutionObservation

/-- Every admitted prefix has unique node notices and completions, even for arbitrary raw
work.
-/
example (work : Work) (history : History) (h : AdmissiblePrefix work history)
    : history.UniqueRefs :=
  h.uniqueRefs

/-- Terminal histories close each initial/later ref exactly once, using the general count
witness.
-/
example (work : Work) (history : History) (h : AdmissibleRun work history)
    : ∀ ref ∈
        (history.initialGroups ++ history.initialStreams).map DeliveryNode.ref
        ++ pendingRefs history.batches.flatten,
        (completedRefs history.batches.flatten).count ref = 1 :=
  h.refsCompleteExactlyOnce

/-- Output accounting applies directly to a permitted atom, without internal progress
states.
-/
example (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (before : List WorkQueueEvent) (failed : FailureCuts) (event : WorkQueueEvent)
    (allowed : EventAllowed work initial matching before failed event)
    : (eventPending event).Nodup ∧ (eventCompleted event).Nodup :=
  ⟨allowed.accounting.pendingUnique, allowed.accounting.completedUnique⟩

def completed : History :=
  {
    initialGroups := [WorkQueueSemantics.node],
    initialStreams := [],
    batches :=
      [[
        .groupValues WorkQueueSemantics.node [{ path := [], data := [] }],
        .groupSuccess WorkQueueSemantics.node [] [],
        .workQueueTermination
      ]]
  }

/-- The concrete terminal fixture satisfies the universal ref-identity witness. -/
example : completed.UniqueRefs := WorkQueueSemantics.completedRun.uniqueRefs

/-- Its initially announced ref has one completion, by terminal liveness and uniqueness.
-/
example : (completedRefs completed.batches.flatten).count 0 = 1 :=
  WorkQueueSemantics.completedRun.refsCompleteExactlyOnce 0
    (by simp [WorkQueueSemantics.node])

/-- Causal failure/cancellation retains the same terminal exactly-once guarantee. -/
example
    : (completedRefs [[WorkQueueSemantics.failure, .workQueueTermination]].flatten).count
        0
      = 1 :=
  WorkQueueSemantics.failedRun.refsCompleteExactlyOnce 0
    (by simp [WorkQueueSemantics.node])

def stalled : History :=
  { initialGroups := [WorkQueueSemantics.node], initialStreams := [], batches := [] }

/-- A stalled prefix is genuinely admitted, by valid initialization and an empty output
history.
-/
theorem stalledAdmitted : AdmissiblePrefix WorkQueueSemantics.work stalled :=
  WorkQueueSemantics.emptyHistory

/-- Prefix admission supplies uniqueness but does not imply terminal liveness. -/
example : stalled.UniqueRefs := stalledAdmitted.uniqueRefs

/-- The terminal count theorem rules out declaring this unfinished prefix a complete run.
-/
example : ¬AdmissibleRun WorkQueueSemantics.work stalled := by
  intro done
  have count := done.refsCompleteExactlyOnce 0 (by simp [stalled, WorkQueueSemantics.node])
  simp [stalled, completedRefs] at count

def duplicateCompletion : History :=
  {
    initialGroups := [WorkQueueSemantics.node],
    initialStreams := [],
    batches :=
      [[
        .groupSuccess WorkQueueSemantics.node [] [],
        .streamFailure WorkQueueSemantics.node 2
      ]]
  }

/-- Changing completion kind cannot hide duplicate refs in a prefix, by the general Nodup
witness.
-/
example (work : Work) : ¬AdmissiblePrefix work duplicateCompletion := by
  intro admitted
  have unique := admitted.uniqueRefs.2
  simp [duplicateCompletion, completedRefs, eventCompleted] at unique

/-- The same duplicate is also forbidden in any terminal history, independently of its
work metadata.
-/
example (work : Work) : ¬AdmissibleRun work duplicateCompletion := by
  intro admitted
  have unique := admitted.uniqueRefs.2
  simp [duplicateCompletion, completedRefs, eventCompleted] at unique

/-- A failure notification already in the prefix excludes a second closure of that ref. -/
example (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (failed : FailureCuts) (event : WorkQueueEvent)
    (allowed
      : EventAllowed work initial matching
          [.groupFailure WorkQueueSemantics.node 2] failed event)
    : 0 ∉ eventCompleted event := by
  intro member
  exact (allowed.accounting.completion 0 member).2
    (by simp [completedRefs, eventCompleted, WorkQueueSemantics.node])

def first : WorkQueueEvent :=
  .streamValues WorkQueueSemantics.node [{ item := .null }]
    [{ ref := 1, path := [] }] [{ ref := 2, path := [] }]

def second : WorkQueueEvent :=
  .streamValues WorkQueueSemantics.node [{ item := .null }]
    [{ ref := 3, path := [] }] [{ ref := 4, path := [] }]

def combined : WorkQueueEvent :=
  .streamValues WorkQueueSemantics.node [{ item := .null }, { item := .null }]
    [{ ref := 1, path := [] }, { ref := 3, path := [] }]
    [{ ref := 2, path := [] }, { ref := 4, path := [] }]

/-! Stream coalescing groups defer notices before stream notices, so exact list equality
is too strong.
-/

#guard pendingRefs [first, second] == [1, 2, 3, 4]
#guard pendingRefs [combined] == [1, 3, 2, 4]

/-- The permitted grouping still preserves every occurrence, by the relational grouping
theorem.
-/
example : (pendingRefs [combined]).Perm (pendingRefs [first, second]) :=
  (ValueGrouping.refPermutation (.combine first (.separate second .nil) rfl)).pending

/-- Coalescing cannot deduplicate repeated announcements; occurrence preservation retains
both copies.
-/
example {merged : WorkQueueEvent} (compatible : combineValues first first = some merged)
    : (pendingRefs [merged]).count 1 = 2 := by
  have preserved := (combineValues_refPermutation compatible).pending
  rw [preserved.count_eq]
  decide

end GraphQL.IncrementalDelivery.Tests.WorkLifecycle
