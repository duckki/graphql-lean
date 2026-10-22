import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledErrors

/-! Proof-only originating-error annotations. Primitive failures allocate references
at a structural call route; aggregation and bubbling reuse those references. Initial
results, deferred tasks and stream items retain separate reports. These are inventories
of pure outcomes, not a native error-recording history or timestamps. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open ScheduledErrors (countedErrors countedErrors_combine)

-----------------------------------------------------------------------------------------
-- Primitive origins and exact counted reports
-----------------------------------------------------------------------------------------

/-- A call-tree route and local primitive-error index, independent of delivery keys. -/
abbrev Origin := List Nat × Nat

def primitiveOrigins (route : List Nat) (errors : Nat) : List Origin :=
  (List.range errors).map (fun index => (route, index))

/-- Existing references are propagated through parent results, never minted from
an aggregate count. The count certificate is also retained at every future task. -/
structure Report (α : Type) where
  outcome : Result α
  origins : List Origin
  accounts : origins.length = countedErrors outcome
deriving Repr

namespace Report

def pure (value : α) : Report α := ⟨.ok (value, 0), [], rfl⟩

/-- Use only at primitive failure branches, not when propagating a child failure. -/
def fault (route : List Nat) (outcome : Result α) : Report α :=
  ⟨
    outcome,
    primitiveOrigins route (countedErrors outcome),
    by
      simp [primitiveOrigins]
  ⟩

def combine (f : α → β → γ) (left : Report α) (right : Report β) : Report γ :=
  ⟨
    Result.combine f left.outcome right.outcome,
    left.origins ++ right.origins,
    by
      rw [List.length_append, left.accounts, right.accounts, countedErrors_combine]
  ⟩

def map (f : α → β) (report : Report α) : Report β :=
  ⟨
    match report.outcome with
    | .error errors => .error errors
    | .ok (value, errors) => .ok (f value, errors),
    report.origins,
    by
      cases h : report.outcome <;> simpa [h, countedErrors] using report.accounts
  ⟩

def catchNull (wrap : α → ResponseValue) (report : Report α) : Report ResponseValue :=
  ⟨
    match report.outcome with
    | .error errors => .ok (.null, errors)
    | .ok (value, errors) => .ok (wrap value, errors),
    report.origins,
    by cases h : report.outcome <;> simpa [h, countedErrors] using report.accounts
  ⟩

/-- A null with no child error introduces one local fault. Positive child errors
already explain the null and bubble with their original identities unchanged. -/
def nonNull (route : List Nat) : Report ResponseValue → Report ResponseValue
  | ⟨.ok (.null, 0), _, _⟩ => fault route (.error 1)
  | ⟨.error errors, origins, accounts⟩ => ⟨.error errors, origins, accounts⟩
  | ⟨.ok (.null, errors + 1), origins, accounts⟩ =>
      ⟨.error (errors + 1), origins, accounts⟩
  | ⟨.ok (.scalar value, errors), origins, accounts⟩ =>
      ⟨.ok (.scalar value, errors), origins, accounts⟩
  | ⟨.ok (.object fields, errors), origins, accounts⟩ =>
      ⟨.ok (.object fields, errors), origins, accounts⟩
  | ⟨.ok (.list values, errors), origins, accounts⟩ =>
      ⟨.ok (.list values, errors), origins, accounts⟩

theorem nonNull_outcome (route : List Nat) (report : Report ResponseValue)
    : (report.nonNull route).outcome = nonNullCompletion report.outcome := by
  obtain ⟨outcome, origins, accounts⟩ := report
  cases outcome with
  | error errors => rfl
  | ok value =>
      obtain ⟨value, errors⟩ := value
      cases value <;> cases errors <;> rfl

end Report

-----------------------------------------------------------------------------------------
-- Keep reports at their original initial/task/item scopes
-----------------------------------------------------------------------------------------

/-- A task retains both its full diagnostic inventory and its boundary cause. -/
structure RecordedOutcome (α : Type) extends Report α where
  cause : Option Nat := none
deriving Repr

/-- Erasure preserves the selected cause without changing collected diagnostics. -/
def RecordedOutcome.erase (outcome : RecordedOutcome α) : TaskOutcome α :=
  ⟨outcome.outcome, outcome.cause⟩

inductive RecordedWork where
  | empty
  | combine (left right : RecordedWork)
  | executionGroup (groups : List DeferredFragment) (path : ResponsePath)
    (report : RecordedOutcome (List (Name × ResponseValue))) (children : RecordedWork)
  | stream (node : DeliveryNode)
    (items : List (RecordedOutcome ResponseValue × RecordedWork))
deriving Repr

def RecordedWork.erase : RecordedWork → Work
  | .empty => .empty
  | .combine left right => .combine left.erase right.erase
  | .executionGroup groups path report children =>
      .executionGroup groups path report.erase children.erase
  | .stream node items =>
      .stream node (items.map (fun item => (item.1.erase, item.2.erase)))
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have := List.sizeOf_lt_of_mem ‹item ∈ items›; cases item; simp_all; omega

/-- Retained task/item inventories, not a history of already-recorded native errors.
Discarded future Work is absent; parent reports retain completed initial errors. -/
def RecordedWork.origins : RecordedWork → List Origin
  | .empty => []
  | .combine left right => left.origins ++ right.origins
  | .executionGroup _ _ report children => report.origins ++ children.origins
  | .stream _ items => items.flatMap (fun item => item.1.origins ++ item.2.origins)
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have := List.sizeOf_lt_of_mem ‹item ∈ items›; cases item; simp_all; omega

structure RecordedCompletion (α : Type) where
  report : Report α
  work : RecordedWork := .empty
  /-- Selected boundary explanation; `report` still inventories every diagnostic. -/
  cause : Option Nat := none
deriving Repr

namespace RecordedCompletion

/-- Retain a completion at a future task boundary, including its selected cause. -/
def outcome (completed : RecordedCompletion α) : RecordedOutcome α :=
  ⟨completed.report, completed.cause⟩

def erase (completed : RecordedCompletion α) : Completion α :=
  ⟨completed.report.outcome, completed.work.erase, completed.cause⟩

def origins (completed : RecordedCompletion α) : List Origin :=
  completed.report.origins ++ completed.work.origins

def pure (value : α) : RecordedCompletion α := { report := .pure value }

def fault (route : List Nat) (outcome : Result α) (cause : Option Nat := none)
    : RecordedCompletion α :=
  {
    report := .fault route outcome,
    cause :=
      match outcome with
      | .error errors => some errors
      | .ok _ => cause
  }

def combine (f : α → β → γ) (left : RecordedCompletion α) (right : RecordedCompletion β)
    : RecordedCompletion γ :=
  let report := Report.combine f left.report right.report
  match report.outcome with
  | .error _ =>
      {
        report,
        cause :=
          match left.report.outcome with
          | .error _ => left.cause
          | .ok _ => right.cause
      }
  | .ok _ => { report, work := .combine left.work right.work }

def map (f : α → β) (completed : RecordedCompletion α) : RecordedCompletion β :=
  ⟨
    completed.report.map f,
    match completed.report.outcome with
    | .error _ => .empty
    | .ok _ => completed.work,
    match completed.report.outcome with
    | .error _ => completed.cause
    | .ok _ => none
  ⟩

def catchNull (wrap : α → ResponseValue) (completed : RecordedCompletion α)
    : RecordedCompletion ResponseValue :=
  ⟨
    completed.report.catchNull wrap,
    match completed.report.outcome with
    | .error _ => .empty
    | .ok _ => completed.work,
    match completed.report.outcome with
    | .error _ => completed.cause
    | .ok _ => none
  ⟩

def nonNull (route : List Nat) (completed : RecordedCompletion ResponseValue)
    : RecordedCompletion ResponseValue :=
  let report := completed.report.nonNull route
  ⟨
    report,
    match report.outcome with
    | .error _ => .empty
    | .ok _ => completed.work,
    completed.erase.nonNull.cause
  ⟩

theorem erase_pure (value : α) : (pure value).erase = Completion.pure value := by
  simp [pure, erase, Report.pure, Completion.pure, RecordedWork.erase]

theorem erase_fault (route : List Nat) (outcome : Result α) (cause : Option Nat := none)
    : (fault route outcome cause).erase
      = {
        result := outcome,
        cause :=
          match outcome with
          | .error errors => some errors
          | .ok _ => cause
      } := by
  simp [fault, erase, Report.fault, RecordedWork.erase]

theorem erase_combine (f : α → β → γ) (left : RecordedCompletion α)
    (right : RecordedCompletion β)
    : (combine f left right).erase = Completion.combine f left.erase right.erase := by
  cases hl : left.report.outcome <;> cases hr : right.report.outcome <;>
    simp [combine, Report.combine, erase, Completion.combine, hl, hr,
      Result.combine, Completion.error, RecordedWork.erase]

theorem erase_map (f : α → β) (completed : RecordedCompletion α)
    : (completed.map f).erase = completed.erase.map f := by
  cases h : completed.report.outcome <;>
    simp [map, Report.map, erase, Completion.map, h, Completion.error, RecordedWork.erase]

theorem erase_catchNull (wrap : α → ResponseValue) (completed : RecordedCompletion α)
    : (completed.catchNull wrap).erase = completed.erase.catchNull wrap := by
  cases h : completed.report.outcome <;>
    simp [catchNull, Report.catchNull, erase, Completion.catchNull, h, RecordedWork.erase]

theorem erase_nonNull (route : List Nat) (completed : RecordedCompletion ResponseValue)
    : (completed.nonNull route).erase = completed.erase.nonNull := by
  simp only [nonNull, erase, Report.nonNull_outcome, Completion.nonNull]
  cases nonNullCompletion completed.report.outcome <;>
    simp [RecordedWork.erase, Completion.error]

end RecordedCompletion

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
