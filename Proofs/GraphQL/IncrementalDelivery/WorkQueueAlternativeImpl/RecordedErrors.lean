import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ExecutionSiblingPlans

/-! Errors can be recorded before a sibling settles. One coupled history retains those
occurrences across cancellation and bubbling; settled-result counts alone cannot do so.
Error slots are ghost names for the fixed eager counted outcomes, not native error objects.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors

abbrev ErrorSlot := Nat × Nat

def Sibling.errorSlots (sibling : Sibling α) : List ErrorSlot :=
  (List.range (countedErrors sibling.outcome)).map (fun index => (sibling.id, index))

def errorSlots (plan : List (Sibling α)) : List ErrorSlot :=
  plan.flatMap Sibling.errorSlots

theorem errorSlots_length (plan : List (Sibling α))
    : (errorSlots plan).length = errorTotal plan := by
  induction plan with
  | nil => rfl
  | cons sibling rest ih =>
      simp only [errorSlots, List.flatMap_cons, List.length_append, Sibling.errorSlots,
        List.length_map, List.length_range, errorTotal, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]

private theorem Sibling.errorSlots_origin {sibling : Sibling α} {slot : ErrorSlot}
    (member : slot ∈ sibling.errorSlots)
    : slot.1 = sibling.id := by
  obtain ⟨index, _, same⟩ := List.mem_map.mp member
  rw [← same]

theorem errorSlots_unique (plan : List (Sibling α)) (unique : (plan.map Sibling.id).Nodup)
    : (errorSlots plan).Nodup := by
  induction plan with
  | nil => simp [errorSlots]
  | cons sibling rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [errorSlots, List.flatMap_cons, List.nodup_append]
      refine ⟨?_, ih unique.2, ?_⟩
      · apply List.Pairwise.map (R := fun (first second : Nat) => first ≠ second)
          (fun index => (sibling.id, index))
        · intro first second different same
          exact different (congrArg Prod.snd same)
        · exact List.nodup_range
      · intro slot recorded otherSlot available same
        obtain ⟨other, member, origin⟩ := List.mem_flatMap.mp available
        have sameId := (Sibling.errorSlots_origin recorded).symm.trans
          ((congrArg Prod.fst same).trans (Sibling.errorSlots_origin origin))
        have repeated : sibling.id ∈ rest.map Sibling.id := by
          rw [sameId]
          exact List.mem_map_of_mem member
        exact unique.1 repeated

inductive RecordingAction where
  | scope (action : Action)
  | record (slot : ErrorSlot)
  | omit (slot : ErrorSlot)
deriving DecidableEq

/-- A single history couples scope execution with originating-error observations.
`available` means not yet recorded or omitted, not permission to fabricate an error.
-/
structure Recording (α : Type) where
  scope : Scope α
  available : List ErrorSlot
  recorded : List ErrorSlot := []
  omitted : List ErrorSlot := []
  actions : List RecordingAction := []

def Recording.scopeStep (state : Recording α) (next : Scope α) (action : Action)
    : Recording α :=
  { state with scope := next, actions := state.actions ++ [.scope action] }

def Recording.record (state : Recording α) (before : List ErrorSlot) (slot : ErrorSlot)
    (after : List ErrorSlot)
    : Recording α :=
  {
    state with
      available := before ++ after,
      recorded := state.recorded ++ [slot],
      actions := state.actions ++ [.record slot]
  }

def Recording.omit (state : Recording α) (before : List ErrorSlot) (slot : ErrorSlot)
    (after : List ErrorSlot)
    : Recording α :=
  {
    state with
      available := before ++ after,
      omitted := state.omitted ++ [slot],
      actions := state.actions ++ [.omit slot]
  }

/-- Actual recording can precede settlement; settlement requires all its originating
errors recorded. Only an unrecorded slot of a cancelled sibling can be omitted. A later
cancel/bubble never removes earlier records, even from an unfinished sibling.
-/
inductive RecordingHistory (plan : List (Sibling α)) : Recording α → Prop where
  | initial
    : RecordingHistory plan { scope := { pending := plan }, available := errorSlots plan }
  | start {state} (history : RecordingHistory plan state) (sibling : Sibling α)
    (pending : sibling ∈ state.scope.pending) (running : state.scope.fatal = false)
    (fresh : sibling.id ∉ state.scope.started)
    : RecordingHistory plan
        (state.scopeStep (state.scope.start sibling.id) (.start sibling.id))
  | record {state} (history : RecordingHistory plan state)
    (before after : List ErrorSlot) (slot : ErrorSlot)
    (available : state.available = before ++ slot :: after)
    (started : slot.1 ∈ state.scope.started)
    (live : slot.1 ∉ state.scope.cancelled.map Sibling.id)
    : RecordingHistory plan (state.record before slot after)
  | settle {state} (history : RecordingHistory plan state)
    (before after : List (Sibling α)) (sibling : Sibling α)
    (pending : state.scope.pending = before ++ sibling :: after)
    (started : sibling.id ∈ state.scope.started)
    (recorded : ∀ slot ∈ sibling.errorSlots, slot ∈ state.recorded)
    : RecordingHistory plan
        (state.scopeStep (state.scope.settle before sibling after) (.settle sibling.id))
  | cancel {state} (history : RecordingHistory plan state)
    (before after : List (Sibling α)) (sibling : Sibling α)
    (pending : state.scope.pending = before ++ sibling :: after)
    (cut : state.scope.fatal = true)
    : RecordingHistory plan
        (state.scopeStep (state.scope.cancel before sibling after) (.cancel sibling.id))
  | omitError {state} (history : RecordingHistory plan state)
    (before after : List ErrorSlot) (slot : ErrorSlot)
    (available : state.available = before ++ slot :: after)
    (cancelled : slot.1 ∈ state.scope.cancelled.map Sibling.id)
    : RecordingHistory plan (state.omit before slot after)
  | bubble {state} (history : RecordingHistory plan state)
    (cut : state.scope.fatal = true)
    : RecordingHistory plan (state.scopeStep state.scope.bubble .bubble)

-----------------------------------------------------------------------------------------
-- Compatible scope/record traces and monotone originating-error inventories
-----------------------------------------------------------------------------------------

/-- The scope derivation comes from this same interleaved history, not a separate witness. -/
theorem RecordingHistory.scope_history {plan : List (Sibling α)} {state}
    (history : RecordingHistory plan state)
    : History plan state.scope := by
  induction history with
  | initial => exact .initial
  | start history sibling pending running fresh ih =>
      exact .start ih sibling pending running fresh
  | record history before after slot available started live ih => exact ih
  | settle history before after sibling pending started recorded ih =>
      exact .settle ih before after sibling pending started
  | cancel history before after sibling pending cut ih =>
      exact .cancel ih before after sibling pending cut
  | omitError history before after slot available cancelled ih => exact ih
  | bubble history cut ih => exact .bubble ih cut

private theorem move_slot (before after recorded omitted : List ErrorSlot)
    (slot : ErrorSlot)
    : ((before ++ after) ++ (recorded ++ [slot]) ++ omitted).Perm
        ((before ++ slot :: after) ++ recorded ++ omitted) := by
  have old := (List.perm_middle (a := slot) (l₁ := before) (l₂ := after)).append_right
    (recorded ++ omitted)
  have next := List.perm_middle (a := slot) (l₁ := (before ++ after) ++ recorded) (l₂ := omitted)
  simp only [List.append_assoc, List.cons_append] at old next
  exact (by simpa only [List.append_assoc, List.cons_append, List.singleton_append,
          List.nil_append] using next.trans old.symm)

private theorem omit_slot (before after recorded omitted : List ErrorSlot)
    (slot : ErrorSlot)
    : ((before ++ after) ++ recorded ++ (omitted ++ [slot])).Perm
        ((before ++ slot :: after) ++ recorded ++ omitted) := by
  have old := (List.perm_middle (a := slot) (l₁ := before) (l₂ := after)).append_right
    (recorded ++ omitted)
  have next := List.perm_middle (a := slot)
    (l₁ := (before ++ after) ++ recorded ++ omitted) (l₂ := [])
  simp only [List.append_assoc, List.cons_append, List.append_nil] at old next
  exact (by simpa only [List.append_assoc, List.cons_append, List.singleton_append,
          List.append_nil] using next.trans old.symm)

/-- Recorded/omitted/available errors partition the fixed eager inventory exactly. -/
theorem RecordingHistory.partition {plan : List (Sibling α)} {state}
    (history : RecordingHistory plan state)
    : (state.available ++ state.recorded ++ state.omitted).Perm (errorSlots plan) := by
  induction history with
  | initial => simp
  | start history sibling pending running fresh ih => exact ih
  | record history before after slot available started live ih =>
      apply List.Perm.trans (move_slot before after _ _ slot)
      simpa only [available, Recording.record] using ih
  | settle history before after sibling pending started recorded ih => exact ih
  | cancel history before after sibling pending cut ih => exact ih
  | omitError history before after slot available cancelled ih =>
      apply List.Perm.trans (omit_slot before after _ _ slot)
      simpa only [available, Recording.omit] using ih
  | bubble history cut ih => exact ih

/-- Counts can differ only for unrecorded errors; cancellation never drops early records. -/
theorem RecordingHistory.error_accounting {plan : List (Sibling α)} {state}
    (history : RecordingHistory plan state)
    : state.recorded.length + state.available.length + state.omitted.length
      = countedErrors (eager plan) := by
  have same := history.partition.length_eq
  rw [List.length_append, List.length_append, errorSlots_length] at same
  rw [eager_errors]
  omega

/-- Each originating slot is recorded/omitted at most once, and never in both lists. -/
theorem RecordingHistory.slots_unique {plan : List (Sibling α)} {state}
    (history : RecordingHistory plan state) (unique : (plan.map Sibling.id).Nodup)
    : (state.available ++ state.recorded ++ state.omitted).Nodup :=
  history.partition.nodup_iff.mpr (errorSlots_unique plan unique)

/-- Omission is licensed only by this same history's cancelled response positions. -/
theorem RecordingHistory.omitted_cancelled {plan : List (Sibling α)} {state}
    (history : RecordingHistory plan state)
    : ∀ slot ∈ state.omitted, slot.1 ∈ state.scope.cancelled.map Sibling.id := by
  induction history with
  | initial => simp
  | start history sibling pending running fresh ih => exact ih
  | record history before after slot available started live ih => exact ih
  | settle history before after sibling pending started recorded ih => exact ih
  | cancel history before after sibling pending cut ih =>
      intro slot member
      simp only [Recording.scopeStep, Scope.cancel, List.map_append, List.map_singleton]
      exact List.mem_append_left _ (ih slot member)
  | omitError history before after slot available cancelled ih =>
      intro selected member
      rcases List.mem_append.mp member with old | latest
      · exact ih selected old
      · have same := List.mem_singleton.mp latest
        subst selected
        exact cancelled
  | bubble history cut ih => exact ih

/-- Recorded errors are precisely the ordered record observations; no cancellation or
propagation action can drop an earlier originating error from the report inventory.
-/
theorem RecordingHistory.recorded_trace {plan : List (Sibling α)} {state}
    (history : RecordingHistory plan state)
    : state.recorded
      = state.actions.filterMap
          (fun action =>
            match action with
            | .record slot => some slot
            | _ => none) := by
  induction history with
  | initial => rfl
  | start history sibling pending running fresh ih =>
      simp [Recording.scopeStep, List.filterMap_append, ih]
  | record history before after slot available started live ih =>
      simp [Recording.record, List.filterMap_append, ih]
  | settle history before after sibling pending started recorded ih =>
      simp [Recording.scopeStep, List.filterMap_append, ih]
  | cancel history before after sibling pending cut ih =>
      simp [Recording.scopeStep, List.filterMap_append, ih]
  | omitError history before after slot available cancelled ih =>
      simp [Recording.omit, List.filterMap_append, ih]
  | bubble history cut ih => simp [Recording.scopeStep, List.filterMap_append, ih]

def withCount (result : GraphQL.Execution.Result α) (count : Nat)
    : GraphQL.Execution.Result α :=
  match result with
  | .ok (value, _) => .ok (value, count)
  | .error _ => .error count

/-- The completed report uses the error-occurrence inventory, not settled-sibling totals.
Native code must construct this inventory; this is not an adapter that clamps error counts.
-/
def Recording.observe (state : Recording α) (plan : List (Sibling α))
    : Option (GraphQL.Execution.Result (List α)) :=
  if state.available.isEmpty then
    (state.scope.observe plan).map (fun result => withCount result state.recorded.length)
  else
    none

/-- Complete coupled histories preserve eager data/status and report exactly the recorded
originating errors. The omitted remainder belongs to cancelled positions; earlier records
inside those positions survive their cancellation.
-/
theorem RecordingHistory.complete_observation {plan : List (Sibling α)} {state}
    (history : RecordingHistory plan state) (complete : state.scope.pending = [])
    (accounted : state.available = [])
    : ∃ observed,
        state.observe plan = some observed
        ∧ SameData observed (eager plan)
        ∧ countedErrors observed = state.recorded.length
        ∧ countedErrors observed + state.omitted.length = countedErrors (eager plan) := by
  obtain ⟨result, observed, data, _, _⟩ := history.scope_history.complete_observation complete
  have sameData : SameData (withCount result state.recorded.length) (eager plan) := by
    cases result <;> cases outcome : eager plan <;>
      simp only [SameData, withCount, outcome] at data ⊢
    all_goals exact data
  have count : countedErrors (withCount result state.recorded.length)
      = state.recorded.length := by cases result <;> rfl
  refine ⟨withCount result state.recorded.length, ?_, sameData, count, ?_⟩
  · simp only [Recording.observe, accounted, List.isEmpty_nil, ↓reduceIte, observed,
      Option.map_some]
  · rw [count]
    simpa only [accounted, List.length_nil, Nat.add_zero] using history.error_accounting

/-- The full action trace retains exactly this scope's ordered start/settle/cancel/bubble
observations, with recording/omission interleaved rather than chosen independently.
-/
theorem RecordingHistory.scope_actions {plan : List (Sibling α)} {state}
    (history : RecordingHistory plan state)
    : state.actions.filterMap
        (fun action =>
          match action with
          | .scope observed => some observed
          | _ => none)
      = state.scope.actions := by
  induction history with
  | initial => rfl
  | start history sibling pending running fresh ih =>
      simp [Recording.scopeStep, Scope.start, List.filterMap_append, ih]
  | record history before after slot available started live ih =>
      simp [Recording.record, List.filterMap_append, ih]
  | settle history before after sibling pending started recorded ih =>
      simp [Recording.scopeStep, Scope.settle, List.filterMap_append, ih]
  | cancel history before after sibling pending cut ih =>
      simp [Recording.scopeStep, Scope.cancel, List.filterMap_append, ih]
  | omitError history before after slot available cancelled ih =>
      simp [Recording.omit, List.filterMap_append, ih]
  | bubble history cut ih =>
      simp [Recording.scopeStep, Scope.bubble, List.filterMap_append, ih]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors
