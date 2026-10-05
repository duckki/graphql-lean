import Proofs.GraphQL.IncrementalDelivery.Correctness.EntryCoverageRetention
import Proofs.GraphQL.IncrementalDelivery.Correctness.ValueFailureCoverage

/-! Successful ordinary results have covered mixed completions, even with nullable errors. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics.MixedPaths

-----------------------------------------------------------------------------------------
-- Proof-only comparison targets for recursive value and collected-field execution
-----------------------------------------------------------------------------------------

/-- Every ordinary successful field result has a successful covered initial completion.
Initial data and error counts may differ; actual child work supplies future data/failures.
-/
def FieldsCompletionCovered (containers : Bool) (path : ResponsePath)
    (ordinary : Result (List (Name × ResponseValue)))
    (completed : Completion (List (Name × ResponseValue)))
    : Prop :=
  ∀ reference errors,
    ordinary = .ok (reference, errors)
    → ∃ initial count,
        completed.result = .ok (initial, count)
        ∧ EntriesCovered containers (TypedResponse.fields path reference)
            (preparedFieldPositions containers path initial completed.work) completed.work

/-- Every ordinary successful value has a successful covered initial completion.
This does not require initial/reference value equality or zero counted errors.
-/
def ValueCompletionCovered (containers : Bool) (path : ResponsePath)
    (ordinary : Result ResponseValue) (completed : Completion ResponseValue)
    : Prop :=
  ∀ reference errors,
    ordinary = .ok (reference, errors)
    → ∃ initial count,
        completed.result = .ok (initial, count)
        ∧ EntriesCovered containers (TypedResponse.value path reference)
            (preparedValuePositions containers path initial completed.work) completed.work

/-- Every ordinary successful retained partition is covered by actual work positions.
Its payload-seeded source inventory is independent of an external initial response.
-/
def WorkFieldsCovered (containers : Bool) (path : ResponsePath)
    (ordinary : Result (List (Name × ResponseValue))) (work : Work)
    : Prop :=
  ∀ reference errors,
    ordinary = .ok (reference, errors)
    → ∀ cursors,
        EntriesCovered containers (TypedResponse.fields path reference)
          ((sourceTasks [] none cursors work).flatMap (SourceTask.positions containers))
          work

-----------------------------------------------------------------------------------------
-- Exact or bubbling ordinary results need no recursive comparison
-----------------------------------------------------------------------------------------

/-- Equal field results are covered initially, regardless of their child work or errors.
Witness: ordinary success identifies the actual initial fields and their visible paths.
-/
theorem FieldsCompletionCovered.of_result_eq {containers path ordinary completed}
    (same : completed.result = ordinary)
    : FieldsCompletionCovered containers path ordinary completed := by
  intro reference errors success
  refine ⟨reference, errors, same.trans success, ?_⟩
  apply EntriesCovered.of_visiblePaths_subset
  rw [visibleEntryPaths_fields]
  exact fun _ member => List.mem_append_left _ member

/-- Equal value results are covered initially, including nullable values with errors.
Witness: visible typed paths project to the actual initial value inventory.
-/
theorem ValueCompletionCovered.of_result_eq {containers path ordinary completed}
    (same : completed.result = ordinary)
    : ValueCompletionCovered containers path ordinary completed := by
  intro reference errors success
  refine ⟨reference, errors, same.trans success, ?_⟩
  apply EntriesCovered.of_visiblePaths_subset
  rw [visibleEntryPaths_value]
  exact fun _ member => List.mem_append_left _ member

/-- A bubbling ordinary field result imposes no nonbubbling coverage obligation.
Witness: ordinary error/success constructor disjointness; actual work is unrestricted.
-/
theorem FieldsCompletionCovered.error (containers : Bool) (path : ResponsePath)
    (errors : Nat) (completed : Completion (List (Name × ResponseValue)))
    : FieldsCompletionCovered containers path (.error errors) completed := by
  intro reference count success
  cases success

/-- A bubbling ordinary value imposes no successful-value coverage obligation.
Witness: constructor disjointness; mixed initial data need not be inspected.
-/
theorem ValueCompletionCovered.error (containers : Bool) (path : ResponsePath)
    (errors : Nat) (completed : Completion ResponseValue)
    : ValueCompletionCovered containers path (.error errors) completed := by
  intro reference count success
  cases success

/-- Permuting ordinary reference entries preserves the same completion's coverage.
Witness: a supplied successful ordinary-result comparison and typed-entry membership.
No initial-data permutation or failure-scope lookup is required.
-/
theorem FieldsCompletionCovered.of_referenceComparison
    {containers path ordinary other completed}
    (covered : FieldsCompletionCovered containers path ordinary completed)
    (compared
      : ∀ reference errors,
          other = .ok (reference, errors)
          → ∃ prior count,
              ordinary = .ok (prior, count)
              ∧ (TypedResponse.fields path prior).Perm
                  (TypedResponse.fields path reference))
    : FieldsCompletionCovered containers path other completed := by
  intro reference errors success
  obtain ⟨prior, count, priorSuccess, permuted⟩ := compared reference errors success
  obtain ⟨initial, count, initialSuccess, covered⟩ := covered prior count priorSuccess
  exact ⟨initial, count, initialSuccess, covered.perm permuted⟩

/-- An initially bubbling covered partition rules out successful combined ordinary fields.
Witness: joint ordinary success would demand an actual successful initial partition,
contradicting the given error. This handles a plan that cancels unstarted deferred work.
-/
theorem FieldsCompletionCovered.append_when_error {containers path ordinary completed}
    (covered : FieldsCompletionCovered containers path ordinary completed)
    (errors : Nat) (failed : completed.result = .error errors)
    (right : Result (List (Name × ResponseValue)))
    : FieldsCompletionCovered containers path (Result.combine List.append ordinary right)
        completed := by
  intro reference count success
  cases first : ordinary <;> cases last : right <;>
    simp only [first, last, Result.combine, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
      at success
  obtain ⟨initial, initialCount, initialSuccess, _⟩ := covered _ _ first
  simp [failed] at initialSuccess

-----------------------------------------------------------------------------------------
-- Successful field composition retains actual source coordinates
-----------------------------------------------------------------------------------------

/-- A covered completed value becomes a covered singleton response-name field.
Witness: the same value attachment, singleton initial positions/cursors, and unchanged
child work. Failed ordinary values impose no successful-field coverage obligation.
-/
theorem ValueCompletionCovered.field {containers path name ordinary completed}
    (covered
      : ValueCompletionCovered containers (path ++ [.field name]) ordinary completed)
    : FieldsCompletionCovered containers path (singleFieldResult name ordinary)
        (completed.map (fun value => [(name, value)])) := by
  intro reference errors success
  cases outcome : ordinary with
  | error count =>
      simp [outcome, singleFieldResult, GraphQL.Execution.singleFieldResult] at success
  | ok pair =>
      have referenceEq : reference = [(name, pair.1)] := by
        simp only [outcome, singleFieldResult, GraphQL.Execution.singleFieldResult,
          Except.ok.injEq, Prod.mk.injEq] at success
        exact success.1.symm
      subst reference
      obtain ⟨initial, count, initialSuccess, covered⟩ := covered _ _ outcome
      refine ⟨[(name, initial)], count, ?_, ?_⟩
      · simp [Completion.map, initialSuccess]
      · simp only [Completion.map, initialSuccess, TypedResponse.fields,
          List.append_nil, preparedFieldPositions_singleton]
        exact covered

/-- Coverage of two field completions composes through the actual result/work combination.
Witness: ordinary success identifies two successful parts; their covered initial parts
retain work. Seed and uniqueness evidence prevents cursor shadowing during assembly.
-/
theorem FieldsCompletionCovered.append
    {containers path ordinaryLeft ordinaryRight left right leftSlices rightSlices}
    (leftCovered : FieldsCompletionCovered containers path ordinaryLeft left)
    (rightCovered : FieldsCompletionCovered containers path ordinaryRight right)
    (leftSeed
      : WorkCursorSeed (resultCursors (ResponsePositions.fieldCursors path) left.result)
          left.work leftSlices)
    (rightSeed
      : WorkCursorSeed (resultCursors (ResponsePositions.fieldCursors path) right.result)
          right.work rightSlices)
    (unique
      : ∀ initial count,
          (Completion.combine List.append left right).result = .ok (initial, count)
          → (ResponsePositions.fields true path initial).Nodup)
    : FieldsCompletionCovered containers path
        (Result.combine List.append ordinaryLeft ordinaryRight)
        (Completion.combine List.append left right) := by
  intro reference errors success
  cases first : ordinaryLeft <;> cases last : ordinaryRight <;>
    simp only [first, last, Result.combine, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
      at success
  rename_i head tail
  obtain ⟨rfl, _⟩ := success
  obtain ⟨initialLeft, leftErrors, leftSuccess, coversLeft⟩ := leftCovered _ _ first
  obtain ⟨initialRight, rightErrors, rightSuccess, coversRight⟩ := rightCovered _ _ last
  have combined : (Completion.combine List.append left right).result
      = .ok (initialLeft ++ initialRight, leftErrors + rightErrors) := by
    simp [Completion.combine, leftSuccess, rightSuccess, Result.combine]
  refine ⟨initialLeft ++ initialRight, leftErrors + rightErrors, combined, ?_⟩
  simp only [Completion.combine, leftSuccess, rightSuccess, Result.combine,
    List.append_eq, TypedResponse.fields_append]
  exact EntriesCovered.append_fields initialLeft initialRight coversLeft coversRight
    (by simpa only [leftSuccess, resultCursors] using leftSeed)
    (by simpa only [rightSuccess, resultCursors] using rightSeed)
    (unique _ _ combined)

/-- Retaining a covered field completion makes a covered deferred-work partition.
Witness: ordinary success selects the actual successful payload, then exact retention
preserves its initial/source inventory and any failed descendant tasks.
-/
theorem FieldsCompletionCovered.executionGroup {containers path ordinary completed}
    (covered : FieldsCompletionCovered containers path ordinary completed)
    (groups : List DeferredFragment)
    : WorkFieldsCovered containers path ordinary
        (.executionGroup groups path completed.result completed.work) := by
  intro reference errors success cursors
  obtain ⟨initial, count, initialSuccess, covered⟩ := covered reference errors success
  rw [initialSuccess]
  exact covered.executionGroup initial count groups cursors

/-- Covered deferred partitions combine at the same actual ambient cursor environment.
Witness: ordinary-success result inversion and source-only partition composition.
-/
theorem WorkFieldsCovered.append {containers path ordinaryLeft ordinaryRight left right}
    (leftCovered : WorkFieldsCovered containers path ordinaryLeft left)
    (rightCovered : WorkFieldsCovered containers path ordinaryRight right)
    : WorkFieldsCovered containers path
        (Result.combine List.append ordinaryLeft ordinaryRight)
        (.combine left right) := by
  intro reference errors success cursors
  cases first : ordinaryLeft <;> cases last : ordinaryRight <;>
    simp only [first, last, Result.combine, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
      at success
  obtain ⟨rfl, _⟩ := success
  simp only [List.append_eq]
  rw [TypedResponse.fields_append]
  exact EntriesCovered.combine_sources (leftCovered _ _ first cursors)
    (rightCovered _ _ last cursors)

/-- Combining immediate and retained fields covers their joint ordinary result.
Witness: the initial completion keeps its data and work; the retained partition's source
inventory uses the same initial cursors. No synthetic initial slice is introduced.
-/
theorem FieldsCompletionCovered.withWork
    {containers path ordinaryInitial ordinaryTasks initial work}
    (initialCovered : FieldsCompletionCovered containers path ordinaryInitial initial)
    (tasksCovered : WorkFieldsCovered containers path ordinaryTasks work)
    : FieldsCompletionCovered containers path
        (Result.combine List.append ordinaryInitial ordinaryTasks)
        { initial with work := .combine initial.work work } := by
  intro reference errors success
  cases first : ordinaryInitial <;> cases last : ordinaryTasks <;>
    simp only [first, last, Result.combine, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
      at success
  obtain ⟨rfl, _⟩ := success
  obtain ⟨data, count, initialSuccess, covered⟩ := initialCovered _ _ first
  refine ⟨data, count, initialSuccess, ?_⟩
  simp only [List.append_eq]
  rw [TypedResponse.fields_append]
  unfold preparedFieldPositions
  rw [sourcePositions_combine]
  apply EntriesCovered.append_iff.mpr
  refine ⟨(covered.combine_left work).available_mono ?_,
    ((tasksCovered _ _ last (ResponsePositions.fieldCursors path data)).combine_right
      initial.work).available_mono ?_⟩
  · intro position member
    simp only [preparedFieldPositions, List.mem_append] at member ⊢
    exact member.imp_right Or.inl
  · exact fun _ member => List.mem_append_right _ (List.mem_append_right _ member)

end GraphQL.IncrementalDelivery.Correctness
