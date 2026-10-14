import GraphQL.IncrementalDelivery.Execution

/-! Counted-error accounting for a finite sibling start/settlement/cancellation history.
Fixed public Result outcomes are reused; this is not a second query executor. Recursive
execution, actual native error recording and acquired-resource completeness remain separate.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors

open GraphQL.Execution (Result)

-----------------------------------------------------------------------------------------
-- Public counted results and eager sibling aggregation
-----------------------------------------------------------------------------------------

def countedErrors : Result α → Nat
  | .ok (_, errors) | .error errors => errors

def isFatal : Result α → Bool
  | .ok _ => false
  | .error _ => true

/-- A ghost response-position identity with its fixed pure completion outcome. -/
structure Sibling (α : Type) where
  id : Nat
  outcome : Result α

def errorTotal (siblings : List (Sibling α)) : Nat :=
  (siblings.map (fun sibling => countedErrors sibling.outcome)).sum

/-- The existing eager Result.combine policy, abstracted from field/list traversal. -/
def eager : List (Sibling α) → Result (List α)
  | [] => .ok ([], 0)
  | sibling :: rest => Result.combine List.cons sibling.outcome (eager rest)

theorem countedErrors_combine (combine : α → β → γ) (left : Result α) (right : Result β)
    : countedErrors (Result.combine combine left right)
      = countedErrors left + countedErrors right := by
  cases left <;> cases right <;> rfl

theorem isFatal_combine (combine : α → β → γ) (left : Result α) (right : Result β)
    : isFatal (Result.combine combine left right) = (isFatal left || isFatal right) := by
  cases left <;> cases right <;> rfl

theorem errorTotal_append (before after : List (Sibling α))
    : errorTotal (before ++ after) = errorTotal before + errorTotal after := by
  simp [errorTotal]

theorem eager_errors (siblings : List (Sibling α))
    : countedErrors (eager siblings) = errorTotal siblings := by
  induction siblings with
  | nil => rfl
  | cons sibling rest ih =>
      simp only [eager, countedErrors_combine, ih, errorTotal, List.map_cons, List.sum_cons]

theorem eager_fatal (siblings : List (Sibling α))
    : isFatal (eager siblings)
      = siblings.any (fun sibling => isFatal sibling.outcome) := by
  induction siblings with
  | nil => rfl
  | cons sibling rest ih => simp only [eager, isFatal_combine, ih, List.any_cons]

-----------------------------------------------------------------------------------------
-- Settlement can continue after the cut; new starts cannot
-----------------------------------------------------------------------------------------

inductive Action where
  | start (id : Nat)
  | settle (id : Nat)
  | cancel (id : Nat)
  | bubble
deriving DecidableEq

/-- All lists are proof observations. Cancellation records unfinished response positions,
not a claim that their acquired resources have already been released.
-/
structure Scope (α : Type) where
  pending : List (Sibling α)
  started : List Nat := []
  settled : List (Sibling α) := []
  cancelled : List (Sibling α) := []
  fatal : Bool := false
  actions : List Action := []

def Scope.start (scope : Scope α) (id : Nat) : Scope α :=
  { scope with started := scope.started ++ [id], actions := scope.actions ++ [.start id] }

def Scope.settle (scope : Scope α) (before : List (Sibling α))
    (sibling : Sibling α) (after : List (Sibling α))
    : Scope α :=
  {
    scope with
      pending := before ++ after,
      settled := scope.settled ++ [sibling],
      fatal := scope.fatal || isFatal sibling.outcome,
      actions := scope.actions ++ [.settle sibling.id]
  }

def Scope.cancel (scope : Scope α) (before : List (Sibling α))
    (sibling : Sibling α) (after : List (Sibling α))
    : Scope α :=
  {
    scope with
      pending := before ++ after,
      cancelled := scope.cancelled ++ [sibling],
      actions := scope.actions ++ [.cancel sibling.id]
  }

def Scope.bubble (scope : Scope α) : Scope α :=
  { scope with actions := scope.actions ++ [.bubble] }

/-- Report every settled outcome's counted errors, including completed nullable siblings.
No reduction to one escaping fatal error is licensed by this observation.
-/
def Scope.reportedErrors (scope : Scope α) : Nat := errorTotal scope.settled

/-- Completion observation in original response-position order. Only a fully settled or
cancelled scope has an outcome; a fatal cut discards its data, not its recorded errors.
-/
def Scope.observe (scope : Scope α) (plan : List (Sibling α))
    : Option (Result (List α)) :=
  if scope.pending.isEmpty then
    if scope.fatal then
      some (.error scope.reportedErrors)
    else
      some
        (.ok
          (
            plan.filterMap
              (fun sibling =>
                match sibling.outcome with
                | .ok (value, _) => some value
                | .error _ => none),
            scope.reportedErrors
          ))
  else
    none

theorem Scope.settle_recorded (scope : Scope α) (before after : List (Sibling α))
    (sibling : Sibling α)
    : (scope.settle before sibling after).reportedErrors
      = scope.reportedErrors + countedErrors sibling.outcome := by
  simp [Scope.settle, Scope.reportedErrors, errorTotal]

theorem Scope.cancel_recorded (scope : Scope α) (before after : List (Sibling α))
    (sibling : Sibling α)
    : (scope.cancel before sibling after).reportedErrors = scope.reportedErrors :=
  rfl

/-- Explicit permitted execution policy. A started sibling may settle after another
fatal result, and its recorded errors remain required. Cancellation affects only pending
positions. Bubbling changes no error inventory and must not count the same error again.
-/
inductive History (plan : List (Sibling α)) : Scope α → Prop where
  | initial : History plan { pending := plan }
  | start {scope} (history : History plan scope) (sibling : Sibling α)
    (pending : sibling ∈ scope.pending) (running : scope.fatal = false)
    (fresh : sibling.id ∉ scope.started)
    : History plan (scope.start sibling.id)
  | settle {scope} (history : History plan scope) (before after : List (Sibling α))
    (sibling : Sibling α) (pending : scope.pending = before ++ sibling :: after)
    (started : sibling.id ∈ scope.started)
    : History plan (scope.settle before sibling after)
  | cancel {scope} (history : History plan scope) (before after : List (Sibling α))
    (sibling : Sibling α) (pending : scope.pending = before ++ sibling :: after)
    (cut : scope.fatal = true)
    : History plan (scope.cancel before sibling after)
  | bubble {scope} (history : History plan scope) (cut : scope.fatal = true)
    : History plan scope.bubble

-----------------------------------------------------------------------------------------
-- Identity conservation and exact recorded/cancelled/pending error accounting
-----------------------------------------------------------------------------------------

private theorem move_to_settled (before after settled cancelled : List (Sibling α))
    (sibling : Sibling α)
    : ((before ++ after) ++ (settled ++ [sibling]) ++ cancelled).Perm
        ((before ++ sibling :: after) ++ settled ++ cancelled) := by
  have old : ((before ++ sibling :: after) ++ settled ++ cancelled).Perm
      (sibling :: ((before ++ after) ++ settled ++ cancelled)) := by
    simpa only [List.append_assoc, List.cons_append]
      using (List.perm_middle (a := sibling) (l₁ := before) (l₂ := after)).append_right
        (settled ++ cancelled)
  have next : ((before ++ after) ++ (settled ++ [sibling]) ++ cancelled).Perm
      (sibling :: ((before ++ after) ++ settled ++ cancelled)) := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append]
      using (List.perm_middle (a := sibling)
              (l₁ := (before ++ after) ++ settled) (l₂ := cancelled))
  exact next.trans old.symm

private theorem move_to_cancelled (before after settled cancelled : List (Sibling α))
    (sibling : Sibling α)
    : ((before ++ after) ++ settled ++ (cancelled ++ [sibling])).Perm
        ((before ++ sibling :: after) ++ settled ++ cancelled) := by
  have old : ((before ++ sibling :: after) ++ settled ++ cancelled).Perm
      (sibling :: ((before ++ after) ++ settled ++ cancelled)) := by
    simpa only [List.append_assoc, List.cons_append]
      using (List.perm_middle (a := sibling) (l₁ := before) (l₂ := after)).append_right
        (settled ++ cancelled)
  have next : ((before ++ after) ++ settled ++ (cancelled ++ [sibling])).Perm
      (sibling :: ((before ++ after) ++ settled ++ cancelled)) := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append,
      List.append_nil]
      using (List.perm_middle (a := sibling)
              (l₁ := (before ++ after) ++ settled ++ cancelled) (l₂ := []))
  exact next.trans old.symm

/-- Every response position remains pending, settled or cancelled in the same history. -/
theorem History.partition {plan : List (Sibling α)} {scope} (history : History plan scope)
    : (scope.pending ++ scope.settled ++ scope.cancelled).Perm plan := by
  induction history with
  | initial => simp
  | start history sibling pending running fresh ih => exact ih
  | settle history before after sibling pending started ih =>
      apply List.Perm.trans (move_to_settled before after _ _ sibling)
      simpa only [pending, Scope.settle] using ih
  | cancel history before after sibling pending cut ih =>
      apply List.Perm.trans (move_to_cancelled before after _ _ sibling)
      simpa only [pending, Scope.cancel] using ih
  | bubble history cut ih => exact ih

/-- The fatal flag has exactly one cause: at least one recorded fatal completion. -/
theorem History.fatal {plan : List (Sibling α)} {scope} (history : History plan scope)
    : scope.fatal = scope.settled.any (fun sibling => isFatal sibling.outcome) := by
  induction history with
  | initial => rfl
  | start history sibling pending running fresh ih => exact ih
  | settle history before after sibling pending started ih =>
      simp only [Scope.settle, List.any_append, List.any_cons, List.any_nil,
        Bool.or_false, ih]
  | cancel history before after sibling pending cut ih => exact ih
  | bubble history cut ih => exact ih

/-- Fresh starts are once-only; settling after a fatal cut does not replenish permission. -/
theorem History.starts_unique {plan : List (Sibling α)} {scope}
    (history : History plan scope)
    : scope.started.Nodup := by
  induction history with
  | initial => simp
  | start history sibling pending running fresh ih =>
      simp only [Scope.start, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro first member second single same
      simp only [List.mem_singleton] at single
      exact fresh ((same.trans single) ▸ member)
  | settle history before after sibling pending started ih => exact ih
  | cancel history before after sibling pending cut ih => exact ih
  | bubble history cut ih => exact ih

/-- Unique original positions cannot be settled or cancelled twice. This does not impose
an arbitrary settlement order or identify response positions with native error objects.
-/
theorem History.positions_unique {plan : List (Sibling α)} {scope}
    (history : History plan scope) (unique : (plan.map Sibling.id).Nodup)
    : ((scope.pending ++ scope.settled ++ scope.cancelled).map Sibling.id).Nodup := by
  exact (history.partition.map _).nodup_iff.mpr unique

/-- Exact accounting: only errors in unfinished/cancelled positions can differ from eager
aggregation. No recorded count is clamped or dropped, and bubbling adds nothing.
-/
theorem History.error_accounting {plan : List (Sibling α)} {scope}
    (history : History plan scope)
    : scope.reportedErrors + errorTotal scope.pending + errorTotal scope.cancelled
      = countedErrors (eager plan) := by
  have same := (history.partition.map (fun sibling => countedErrors sibling.outcome)).sum_nat
  change errorTotal (scope.pending ++ scope.settled ++ scope.cancelled) = errorTotal plan at same
  rw [errorTotal_append, errorTotal_append] at same
  rw [eager_errors]
  unfold Scope.reportedErrors
  omega

theorem History.reported_le_eager {plan : List (Sibling α)} {scope}
    (history : History plan scope)
    : scope.reportedErrors ≤ countedErrors (eager plan) := by
  have exactCount := history.error_accounting
  omega

/-- Every completed error-free-or-nullable-only schedule reports the exact eager total.
Cancellation is impossible when every fixed sibling outcome is nonfatal, even if nullable
siblings have counted errors. An `.error 0` is still fatal and is not covered by this premise.
-/
theorem History.nonfatal_no_cancel {plan : List (Sibling α)} {scope}
    (history : History plan scope)
    (healthy : ∀ sibling ∈ plan, isFatal sibling.outcome = false)
    : scope.fatal = false ∧ scope.cancelled = [] := by
  induction history with
  | initial => exact ⟨rfl, rfl⟩
  | start history sibling pending running fresh ih => exact ih
  | settle history before after sibling pending started ih =>
      have member : sibling ∈ plan := history.partition.subset
        (List.mem_append_left _ (List.mem_append_left _
          (by rw [pending]; exact List.mem_append_right _ List.mem_cons_self)))
      exact ⟨
        by simp only [Scope.settle, ih.1, healthy sibling member, Bool.false_or],
        ih.2
      ⟩
  | cancel history before after sibling pending cut ih =>
      rw [ih.1] at cut
      cases cut
  | bubble history cut ih => exact ih

theorem History.complete_nonfatal_errors {plan : List (Sibling α)} {scope}
    (history : History plan scope)
    (healthy : ∀ sibling ∈ plan, isFatal sibling.outcome = false)
    (complete : scope.pending = [])
    : scope.reportedErrors = countedErrors (eager plan) := by
  have cancelled := (history.nonfatal_no_cancel healthy).2
  simpa only [complete, cancelled, errorTotal, List.map_nil, List.sum_nil, Nat.add_zero]
    using history.error_accounting

private theorem eager_nonfatal (plan : List (Sibling α))
    (healthy : ∀ sibling ∈ plan, isFatal sibling.outcome = false)
    : eager plan
      = .ok
          (
            plan.filterMap
              (fun sibling =>
                match sibling.outcome with
                | .ok (value, _) => some value
                | .error _ => none),
            errorTotal plan
          ) := by
  induction plan with
  | nil => rfl
  | cons sibling rest ih =>
      have first := healthy sibling List.mem_cons_self
      cases outcome : sibling.outcome with
      | error errors => simp [outcome, isFatal] at first
      | ok result =>
          obtain ⟨value, errors⟩ := result
          rw [eager, outcome, ih (fun later member => healthy later
            (List.mem_cons_of_mem _ member))]
          simp [Result.combine, outcome, errorTotal, countedErrors]

/-- Every complete all-nonfatal schedule has the exact eager data and error total,
regardless of settlement order. Nullable counted errors need not be zero.
-/
theorem History.complete_nonfatal_agrees {plan : List (Sibling α)} {scope}
    (history : History plan scope)
    (healthy : ∀ sibling ∈ plan, isFatal sibling.outcome = false)
    (complete : scope.pending = [])
    : scope.observe plan = some (eager plan) := by
  have running := (history.nonfatal_no_cancel healthy).1
  simp only [Scope.observe, complete, List.isEmpty_nil, ↓reduceIte, running,
    Bool.false_eq_true, history.complete_nonfatal_errors healthy complete,
    eager_nonfatal plan healthy, countedErrors]

/-- A nonfatal boundary has never cancelled a sibling; fatal status cannot be reset. -/
theorem History.nonfatal_cancelled_nil {plan : List (Sibling α)} {scope}
    (history : History plan scope) (running : scope.fatal = false)
    : scope.cancelled = [] := by
  induction history with
  | initial => rfl
  | start history sibling pending startOpen fresh ih => exact ih running
  | settle history before after sibling pending started ih =>
      exact ih (Bool.or_eq_false_iff.mp running).1
  | cancel history before after sibling pending cut ih =>
      simp only [Scope.cancel, cut, Bool.true_eq_false] at running
  | bubble history cut ih => exact ih running

/-- Data/status equality leaves counted errors separate: both fatal outcomes bubble,
while successful outcomes carry the same response-position-ordered value.
-/
def SameData : Result α → Result α → Prop
  | .ok (left, _), .ok (right, _) => left = right
  | .error _, .error _ => True
  | _, _ => False

/-- Every complete permitted scope has the eager data/status and exactly its own
recorded error count. The difference from eager counts is explained by cancellation,
not by assuming independent native executions have equal error totals.
-/
theorem History.complete_observation {plan : List (Sibling α)} {scope}
    (history : History plan scope) (complete : scope.pending = [])
    : ∃ observed,
        scope.observe plan = some observed
        ∧ SameData observed (eager plan)
        ∧ countedErrors observed = scope.reportedErrors
        ∧ countedErrors observed + errorTotal scope.cancelled
          = countedErrors (eager plan) := by
  have accounting := history.error_accounting
  simp only [complete, errorTotal, List.map_nil, List.sum_nil, Nat.add_zero] at accounting
  cases fatal : scope.fatal with
  | false =>
      have noneCancelled := history.nonfatal_cancelled_nil fatal
      have healthy : ∀ sibling ∈ plan, isFatal sibling.outcome = false := by
        intro sibling member
        have present := history.partition.symm.subset member
        simp only [complete, noneCancelled, List.nil_append, List.append_nil] at present
        exact Bool.eq_false_iff.mpr
          (List.any_eq_false.mp (history.fatal.symm.trans fatal) sibling present)
      refine ⟨eager plan, history.complete_nonfatal_agrees healthy complete, ?_, ?_, ?_⟩
      · rw [eager_nonfatal plan healthy]
        exact Eq.refl _
      · exact (history.complete_nonfatal_errors healthy complete).symm
      · simp only [noneCancelled, errorTotal, List.map_nil, List.sum_nil, Nat.add_zero]
  | true =>
      obtain ⟨sibling, member, failed⟩ := List.any_eq_true.mp (history.fatal.symm.trans fatal)
      have present : sibling ∈ plan := history.partition.subset
        (List.mem_append_left _ (List.mem_append_right _ member))
      have failedEager : isFatal (eager plan) = true := by
        rw [eager_fatal]
        exact List.any_eq_true.mpr ⟨sibling, present, failed⟩
      refine ⟨.error scope.reportedErrors, ?_, ?_, rfl, accounting⟩
      · simp only [Scope.observe, complete, List.isEmpty_nil, ↓reduceIte, fatal]
      · cases outcome : eager plan with
        | error errors => trivial
        | ok value => simp only [outcome, isFatal, Bool.false_eq_true] at failedEager

-----------------------------------------------------------------------------------------
-- Existing completion wrappers preserve recorded errors and discard failed child work
-----------------------------------------------------------------------------------------

theorem catchNull_errors (wrap : α → GraphQL.Execution.ResponseValue)
    (completion : Execution.Completion α)
    : countedErrors (completion.catchNull wrap).result
      = countedErrors completion.result := by
  cases outcome : completion.result <;>
    simp only [Execution.Completion.catchNull, outcome, countedErrors]

theorem fatal_combine_work (combine : α → β → γ)
    (left : Execution.Completion α) (right : Execution.Completion β)
    (fatal
      : isFatal (GraphQL.Execution.Result.combine combine left.result right.result)
        = true)
    : (Execution.Completion.combine combine left right).work = .empty := by
  unfold Execution.Completion.combine
  cases outcome : GraphQL.Execution.Result.combine combine left.result right.result with
  | error errors => rfl
  | ok value => simp [outcome, isFatal] at fatal

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors
