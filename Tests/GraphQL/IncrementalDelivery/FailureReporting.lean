import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FailureReporting
import Tests.GraphQL.IncrementalDelivery.Execution
import Tests.GraphQL.IncrementalDelivery.WorkScheduler

/-! Regression for the silent deferred failure found during public-definition review. -/

namespace GraphQL.IncrementalDelivery.Tests.FailureReporting
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkScheduler

def a : DeliveryNode := { key := 0, path := [] }
def b : DeliveryNode := { key := 1, path := [] }

def good : Work :=
  .deferred [{ node := a }] [] (.ok ([("a", .scalar "a")], 0)) (.append .empty .empty)

def bad : Work := .deferred [{ node := b }] [] (.error 1) .empty
def wk : Work := .append .empty (.append good (.append bad .empty))
def goodID : Occurrence := .deferred [1, 0]
def badID : Occurrence := .deferred [1, 1, 0]

def op : GraphQL.IncrementalDelivery.Operation :=
  {
    selectionSet := [Tests.defer [Tests.field "a"], Tests.defer [Tests.field "required"]]
  }

/-- Actual query execution produces the review counterexample's work, by reduction. -/
theorem prepared
    : ((executeRootSelectionSetCore Tests.schema Tests.resolvers [] 10 "Query"
          (.object "Query" 0) op.selectionSet).run
        0).1
      = ({ result := .ok ([], 0), work := wk }
          : Completion (List (Name × ResponseValue))) := by
  cbv

/-- The fixture's structural locations, by induction on address navigation. -/
private theorem locations {address current producer owners}
    (h : Located wk address current producer owners)
    : current = .empty
      ∨ (address = [] ∧ current = wk ∧ producer = none ∧ owners = [])
      ∨ (address = [1]
          ∧ current = .append good (.append bad .empty)
          ∧ producer = none
          ∧ owners = [])
      ∨ (address = [1, 0] ∧ current = good ∧ producer = none ∧ owners = [])
      ∨ (address = [1, 0, 0]
          ∧ current = .append .empty .empty
          ∧ producer = some goodID
          ∧ owners = [0])
      ∨ (address = [1, 1] ∧ current = .append bad .empty ∧ producer = none ∧ owners = [])
      ∨ (address = [1, 1, 0] ∧ current = bad ∧ producer = none ∧ owners = []) := by
  replace h := StructuralEquivalence.located_of_current h
  induction h with
  | root => simp
  | left _ ih | right _ ih | deferred _ ih | item _ _ ih =>
      rcases ih with ih | ih | ih | ih | ih | ih | ih <;>
        simp_all [wk, good, bad, a, b, goodID]

/-- Only the successful first task and the failing second task occur in this work. -/
private theorem tasks {occurrence owners producer payload}
    (h : TaskAt wk occurrence owners producer payload)
    : (occurrence = goodID
        ∧ owners = [0]
        ∧ producer = none
        ∧ payload = .object [] (.ok ([("a", .scalar "a")], 0)))
      ∨ (occurrence = badID
          ∧ owners = [1]
          ∧ producer = none
          ∧ payload = .object [] (.error 1)) := by
  cases occurrence with
  | deferred address =>
      obtain ⟨groups, path, result, children, enclosing, located, rfl, rfl⟩ := h
      rcases locations located with h | h | h | h | h | h | h <;>
        simp_all [wk, good, bad, a, b, goodID, badID]
  | item address index =>
      obtain ⟨node, items, enclosing, result, children, located, entry, rfl, rfl⟩ := h
      rcases locations located with h | h | h | h | h | h | h <;>
        simp_all [wk, good, bad]

/-- The second query group is the actual failing occurrence in the prepared work. -/
theorem badTask : TaskAt wk badID [1] none (.object [] (.error 1)) :=
  .deferred (.left (.right (.right .root)))

/-- Reject the original cut: only group zero is announced, but group one fails. -/
example (events : List WorkEvent) : ¬FailureWitness wk [0] events [(0, badID)] := by
  intro witness
  obtain ⟨key, member, opened⟩ := witness.open_owner (cut := 0) (by simp) badTask
  have same : key = 1 := by simpa using member
  subst key
  simpa [Open, announcedKeys, pendingKeys] using opened.1

def silentHistory : History :=
  {
    initialGroups := [a],
    initialStreams := [],
    batches :=
      [[
        .groupValues a [{ path := [], data := [("a", .scalar "a")] }],
        .groupSuccess a [] [],
        .workQueueTermination
      ]]
  }

/-- The fixture has no artificial zero-count failures; inspect its two task outcomes. -/
private theorem positive {occurrence owners producer payload}
    (known : TaskAt wk occurrence owners producer payload)
    (fails : payload.failure.isSome = true)
    : 0 < payload.failure.getD 0 := by
  rcases tasks known with success | failure
  · simp [success.2.2.2, Payload.failure] at fails
  · simp [failure.2.2.2, Payload.failure]

/-- No explanation or batching can admit the formerly successful-looking terminal
history. Failure accounting would force its genuinely failing task to succeed.
-/
theorem silentFailureRejected : ¬AdmissibleRun wk silentHistory := by
  intro run
  have impossible := run.tasks_succeed_of_no_failure_errors
    (fun _ _ _ _ => positive) (by decide) badTask
  cases impossible

/-- A closed owner cannot license a newly recorded failure, even when previously
announced. This prevents reporting the error only after its completion has passed.
-/
example
    : ¬FailureWitness WorkScheduler.failingWork [0]
        [WorkScheduler.failure] [(1, .deferred [])] := by
  intro witness
  have known : TaskAt WorkScheduler.failingWork (.deferred []) [0] none
      (.object [] (.error 2)) := .deferred .root
  obtain ⟨key, member, opened⟩ := witness.open_owner (cut := 1) (by simp) known
  have same : key = 0 := by simpa using member
  subst key
  exact opened.2
    (by simp [completedKeys, eventCompleted,
      WorkScheduler.failure, WorkScheduler.node])

def sharedFailure : Work :=
  .deferred [{ node := a }, { node := b }] [] (.error 1) .empty

/-- One open contributing owner suffices; shared work need not announce every owner,
and its error notification may still be delayed.
-/
example : FailureWitness sharedFailure [1] [] [(0, .deferred [])] := by
  intro before cut occurrence after equal
  cases before with
  | nil =>
      have same : cut = 0 ∧ occurrence = .deferred [] ∧ after = [] := by
        simpa [Prod.mk.injEq, and_assoc] using equal.symm
      rcases same with ⟨rfl, rfl, rfl⟩
      have known : TaskAt sharedFailure (.deferred []) [0, 1] none
          (.object [] (.error 1)) := .deferred .root
      exact ⟨
        by simp,
        by simp,
        ⟨
          _,
          _,
          _,
          known,
          rfl,
          .root ⟨_, _, known⟩,
          1,
          by simp,
          by simp [Open, announcedKeys, pendingKeys, completedKeys]
        ⟩,
        WorkScheduler.noCancellation _ _
      ⟩
  | cons first rest =>
      have impossible := congrArg List.length equal
      simp at impossible

/-- The established failed-run fixture still accounts for its reported errors under
the stronger rule; this also exercises the batching witness.
-/
example
    : ∃ events matching failures,
        Explains WorkScheduler.failingWork [WorkScheduler.node] [] events matching
          failures
        ∧ Terminal WorkScheduler.failingWork [0] matching events
            (failedBefore failures events.length)
        ∧ WorkBatching (events ++ [.workQueueTermination])
            [[WorkScheduler.failure, .workQueueTermination]]
        ∧ ∀ cut occurrence owners producer payload,
            (cut, occurrence) ∈ failures
            → TaskAt WorkScheduler.failingWork occurrence owners producer payload
            → payload.failure.getD 0 ≤ 2 := by
  simpa [WorkScheduler.node, WorkScheduler.failure, failureErrors]
    using WorkScheduler.failedRun.failure_accounting

end GraphQL.IncrementalDelivery.Tests.FailureReporting
