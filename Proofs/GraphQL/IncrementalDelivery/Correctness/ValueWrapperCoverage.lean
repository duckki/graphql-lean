import Proofs.GraphQL.IncrementalDelivery.Correctness.FieldExecutionCoverage

/-! Nullable object catching and non-null wrappers preserve mixed failure-aware coverage. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Nullable object bubbling is explained by actual null data or retained descendant failure
-----------------------------------------------------------------------------------------

/-- Catching covered ordinary object fields preserves value coverage, including bubbles.
Witness: successful fields wrap using the same cursors. An ordinary bubble either catches
an actual initial bubble as null or is explained by a real failed task beneath the partial
initial object. Ordinary and initial counted errors need not agree.
-/
theorem FieldsCompletionCovered.catchObject {containers path ordinary completed}
    (covered : FieldsCompletionCovered containers path ordinary completed)
    (reflected : OrdinaryFailures.BubblesExplained path ordinary completed)
    : ValueCompletionCovered containers path
        (GraphQL.Execution.catchBubbleAsNull ResponseValue.object ordinary)
        (completed.catchNull ResponseValue.object) := by
  intro reference errors success
  cases outcome : ordinary with
  | error count =>
      have referenceEq : reference = .null := by
        simp only [outcome, GraphQL.Execution.catchBubbleAsNull, Except.ok.injEq,
          Prod.mk.injEq] at success
        exact success.1.symm
      subst reference
      cases actual : completed.result with
      | error count =>
          refine ⟨.null, count, ?_, ?_⟩
          · simp [Completion.catchNull, actual]
          · simp only [Completion.catchNull, actual]
            apply EntriesCovered.of_visiblePaths_subset
            rw [visibleEntryPaths_value]
            exact fun _ member => List.mem_append_left _ member
      | ok pair =>
          obtain ⟨initial, count⟩ := pair
          refine ⟨.object initial, count, ?_, ?_⟩
          · simp [Completion.catchNull, actual]
          · rcases reflected _ outcome with initiallyFailed | retained
            · obtain ⟨count, failed⟩ := initiallyFailed
              simp [actual] at failed
            · obtain ⟨occurrence, owners, producer, payload, known, fails, below⟩ := retained
              intro entry member _
              obtain rfl := List.mem_singleton.mp member
              simp only [Completion.catchNull, actual]
              exact Or.inr ⟨occurrence, owners, producer, payload, known, fails,
                Or.inr ⟨rfl, below⟩⟩
  | ok pair =>
      have referenceEq : reference = .object pair.1 := by
        simp only [outcome, GraphQL.Execution.catchBubbleAsNull, Except.ok.injEq,
          Prod.mk.injEq] at success
        exact success.1.symm
      subst reference
      obtain ⟨initial, count, initialSuccess, covered⟩ := covered _ _ outcome
      refine ⟨.object initial, count, ?_, ?_⟩
      · simp [Completion.catchNull, initialSuccess]
      · simpa only [Completion.catchNull, initialSuccess] using covered.object pair.1 initial

-----------------------------------------------------------------------------------------
-- A successful ordinary non-null wrapper cannot null or discard the actual covered value
-----------------------------------------------------------------------------------------

/-- A non-null wrapper preserves coverage of every successful ordinary value.
Witness: forward value-failure preservation excludes an initial null against ordinary
non-null success; both wrappers then retain the same covered value and child work.
-/
theorem ValueCompletionCovered.nonNull {containers path ordinary completed}
    (covered : ValueCompletionCovered containers path ordinary completed)
    (preserved : InitialFailures.ValueFailuresPreserved ordinary completed.result)
    : ValueCompletionCovered containers path (nonNullCompletion ordinary)
        completed.nonNull := by
  intro reference errors success
  cases outcome : ordinary with
  | error count =>
      simp [outcome, nonNullCompletion, GraphQL.Execution.nonNullCompletion] at success
  | ok pair =>
      obtain ⟨data, count⟩ := pair
      by_cases isNull : data = .null
      · simp [outcome, isNull, nonNullCompletion, GraphQL.Execution.nonNullCompletion] at success
      · have ordinarySuccess : nonNullCompletion ordinary = .ok (data, count) := by
          rw [outcome]
          cases data <;> first | contradiction | rfl
        rw [ordinarySuccess] at success
        obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj success)
        obtain ⟨initial, count, actualSuccess, covered⟩ := covered _ _ outcome
        obtain ⟨guarded, guardedCount, guardSuccess, notNull⟩ :=
          preserved.initial_nonNull _ _ outcome isNull
        have equal : initial = guarded := (Prod.mk.inj
          (Except.ok.inj (actualSuccess.symm.trans guardSuccess))).1
        have initialNotNull : initial ≠ .null := equal ▸ notNull
        have actualNonNull : nonNullCompletion completed.result = .ok (initial, count) := by
          rw [actualSuccess]
          cases initial <;> first | contradiction | rfl
        refine ⟨initial, count, ?_, ?_⟩
        · simp [Completion.nonNull, actualNonNull]
        · simpa only [Completion.nonNull, actualNonNull] using covered

-----------------------------------------------------------------------------------------
-- Actual named-type completion reduces the object branch to covered response fields
-----------------------------------------------------------------------------------------

/-- Actual non-null completion is covered from the same-fuel inner-type comparison.
Witness: actual monadic value completion plus forward failure preservation discharges
the non-null wrapper's initial-value guard. Only the inner type decreases recursively.
-/
theorem completeValue_nonNull_entriesCovered_of_inner (containers : Bool)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (inner : TypeRef) (selected : List FieldDetails)
    (resolved : ResolverValue ObjectRef)
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool)
    (innerCovered
      : RunEnsures
          (ValueCompletionCovered containers path
            (GraphQL.Execution.completeValue schema resolvers variables (fuel + 1) inner
              (selected.map eraseField) resolved))
          (completeValue schema resolvers variables (fuel + 1) inner selected resolved
            path usages deferMap allowStream))
    : RunEnsures
        (ValueCompletionCovered containers path
          (GraphQL.Execution.completeValue schema resolvers variables (fuel + 1)
            (.nonNull inner) (selected.map eraseField) resolved))
        (completeValue schema resolvers variables (fuel + 1) (.nonNull inner) selected
          resolved path usages deferMap allowStream) := by
  simp only [completeValue, GraphQL.Execution.completeValue]
  refine runEnsures_bind
    (fun completed => ValueCompletionCovered containers path
      (GraphQL.Execution.completeValue schema resolvers variables (fuel + 1) inner
        (selected.map eraseField) resolved) completed
      ∧ InitialFailures.ValueFailuresPreserved
        (GraphQL.Execution.completeValue schema resolvers variables (fuel + 1) inner
          (selected.map eraseField) resolved) completed.result) _ _ _ ?_ ?_
  · intro state
    exact ⟨innerCovered state, InitialFailures.completeValue_preserves_failures schema resolvers
      variables (fuel + 1) inner selected resolved valid path usages deferMap allowStream state⟩
  · intro completed compared
    exact runEnsures_pure _ _ (compared.1.nonNull compared.2)

/-- Actual named-type value completion is covered from its recursive object-field witness.
Witness: actual scalar/type/null branches agree exactly. Composite completion collects
valid unique subfields, executes the covered plan, and catches nullable bubbling using
the independently proved mixed failure-reflection witness.
-/
theorem completeValue_named_entriesCovered_of_fields (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (selected : List FieldDetails)
    (resolved : ResolverValue ObjectRef)
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (fieldsCovered
      : ∀ runtimeType ref,
          ResponseFieldCoverage containers schema resolvers variables fuel runtimeType
            (.object runtimeType ref))
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool)
    : RunEnsures
        (ValueCompletionCovered containers path
          (GraphQL.Execution.completeValue schema resolvers variables (fuel + 1)
            (.named parentType) (selected.map eraseField) resolved))
        (completeValue schema resolvers variables (fuel + 1) (.named parentType) selected
          resolved path usages deferMap allowStream) := by
  cases resolved with
  | null | list _ =>
      intro state
      apply ValueCompletionCovered.of_result_eq
      simp [completeValue, GraphQL.Execution.completeValue, Completion.pure, Completion.error]
  | scalar scalar =>
      intro state
      apply ValueCompletionCovered.of_result_eq
      simp only [completeValue, GraphQL.Execution.completeValue]
      split <;> simp [Completion.pure, Completion.error]
  | object runtimeType ref =>
      cases applies : schema.typeIncludesObjectBool parentType runtimeType <;>
        simp only [completeValue, GraphQL.Execution.completeValue, applies,
          Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · intro state
        apply ValueCompletionCovered.of_result_eq
        simp [Completion.error]
      · refine runEnsures_bind
          (fun collection =>
            eraseGroups collection.collectedFieldsMap
              = GraphQL.Execution.collectSubfields schema variables runtimeType
                (.object runtimeType ref) (selected.map eraseField)
            ∧ GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables)
                collection.collectedFieldsMap
            ∧ GroupsUnique collection.collectedFieldsMap) _ _ _ ?_ ?_
        · intro state
          exact ⟨collectSubfields_erase schema variables runtimeType (.object runtimeType ref)
              selected state,
            ArgumentValidity.collectSubfields_valid schema variables runtimeType
              (.object runtimeType ref) selected valid state,
            collectSubfields_unique schema variables runtimeType (.object runtimeType ref)
              selected state⟩
        · intro collection collected
          refine runEnsures_bind
            (fun completed =>
              FieldsCompletionCovered containers path
                (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                  runtimeType (.object runtimeType ref)
                  (eraseGroups collection.collectedFieldsMap)) completed
              ∧ OrdinaryFailures.BubblesExplained path
                (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                  runtimeType (.object runtimeType ref)
                  (eraseGroups collection.collectedFieldsMap)) completed) _ _ _ ?_ ?_
          · intro state
            exact ⟨executePlan_entriesCovered_of_fields containers schema resolvers variables
                fuel runtimeType (.object runtimeType ref) collection collected.2.1 collected.2.2
                (fieldsCovered runtimeType ref) path usages deferMap state,
              OrdinaryFailures.executePlan_explains_failures schema resolvers variables fuel
                runtimeType (.object runtimeType ref) collection collected.2.1 path usages
                deferMap state⟩
          · intro completed compared
            apply runEnsures_pure
            simpa only [collected.1] using compared.1.catchObject compared.2

-----------------------------------------------------------------------------------------
-- Named-type recursion depends only on strictly smaller execution fuel
-----------------------------------------------------------------------------------------

/-- Named-type completion at fuel one has covered subfields without a recursive premise.
Witness: response-field fuel zero is already proved; nullable object catching explains
any resulting ordinary bubble using actual initial null data or retained failed work.
-/
theorem completeValue_named_entriesCovered_one (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (parentType : Name)
    (selected : List FieldDetails) (resolved : ResolverValue ObjectRef)
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool)
    : RunEnsures
        (ValueCompletionCovered containers path
          (GraphQL.Execution.completeValue schema resolvers variables 1
            (.named parentType) (selected.map eraseField) resolved))
        (completeValue schema resolvers variables 1 (.named parentType) selected resolved
          path usages deferMap allowStream) :=
  completeValue_named_entriesCovered_of_fields containers schema resolvers variables 0
    parentType selected resolved valid
    (fun runtimeType ref =>
      responseFieldCoverage_zero containers schema resolvers variables
        runtimeType (.object runtimeType ref)) path usages deferMap allowStream

/-- Named-type completion reduces to value coverage two execution-fuel levels earlier.
Witness: the intervening response-field step resolves its value at the smaller fuel, while
the actual object collection/plan/wrapper comparison is already checked.
-/
theorem completeValue_named_entriesCovered_of_values (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (valuesCovered : ValueCompletionCoverage containers schema resolvers variables fuel)
    (parentType : Name) (selected : List FieldDetails)
    (resolved : ResolverValue ObjectRef)
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool)
    : RunEnsures
        (ValueCompletionCovered containers path
          (GraphQL.Execution.completeValue schema resolvers variables (fuel + 1 + 1)
            (.named parentType) (selected.map eraseField) resolved))
        (completeValue schema resolvers variables (fuel + 1 + 1) (.named parentType)
          selected resolved path usages deferMap allowStream) :=
  completeValue_named_entriesCovered_of_fields containers schema resolvers variables
    (fuel + 1) parentType selected resolved valid
    (fun runtimeType ref =>
      responseFieldCoverage_of_values containers schema resolvers variables
        fuel valuesCovered runtimeType (.object runtimeType ref))
    path usages deferMap allowStream

end GraphQL.IncrementalDelivery.Correctness
