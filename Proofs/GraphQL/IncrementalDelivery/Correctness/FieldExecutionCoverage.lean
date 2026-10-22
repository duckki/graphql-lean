import Proofs.GraphQL.IncrementalDelivery.Correctness.CompletionCoverageAlgebra
import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicFieldErrors
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedCursorSeeds

/-! Actual collected-field and deferred-partition coverage from response-field comparison. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics
open Semantics.MixedPaths

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Per-response-field comparison isolates the recursive value dependency
-----------------------------------------------------------------------------------------

/-- Every valid selected response field is covered at its actual completion state.
This proof-only dependency ranges over paths, enclosing usages, and defer maps because
partitioning changes those contexts; it asserts no scheduler or response equivalence law.
-/
def ResponseFieldCoverage (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    : Prop :=
  ∀ name selected,
    (∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    → ∀ path usages deferMap,
        RunEnsures
          (FieldsCompletionCovered containers path
            (GraphQL.Execution.executeField schema resolvers variables fuel parentType
              source name (selected.map eraseField)))
          (executeResponseField schema resolvers variables fuel parentType source name
            selected path usages deferMap)

/-- Valid value completion is covered for every actual path, enclosing context, and state.
This is the recursive value target that discharges response-field coverage; it does not
assert agreement of initial/reference data or counted errors.
-/
def ValueCompletionCoverage (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    : Prop :=
  ∀ fieldType selected resolved,
    (∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    → ∀ path usages deferMap allowStream,
        RunEnsures
          (ValueCompletionCovered containers path
            (GraphQL.Execution.completeValue schema resolvers variables fuel fieldType
              (selected.map eraseField) resolved))
          (completeValue schema resolvers variables fuel fieldType selected resolved path
            usages deferMap allowStream)

-----------------------------------------------------------------------------------------
-- Resolving a response field reduces only its recursive value-completion branch
-----------------------------------------------------------------------------------------

/-- Exhausted value fuel has no ordinary successful-value coverage obligation.
Witness: identical ordinary/mixed bubbling results, for every field type and context.
-/
theorem valueCompletionCoverage_zero (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    : ValueCompletionCoverage containers schema resolvers variables 0 := by
  intro fieldType selected resolved _ path usages deferMap allowStream state
  apply ValueCompletionCovered.of_result_eq
  simp [completeValue, GraphQL.Execution.completeValue, Completion.error,
    GraphQL.Execution.outOfFuel]

/-- Exhausted field fuel has no ordinary successful-field obligation.
Witness: the identical ordinary/mixed bubbling result; no resolver is run.
-/
theorem responseFieldCoverage_zero (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    : ResponseFieldCoverage containers schema resolvers variables 0 parentType
        source := by
  intro name selected _ path usages deferMap state
  apply FieldsCompletionCovered.of_result_eq
  cases selected <;> simp [executeResponseField, GraphQL.Execution.executeField,
    Completion.error, GraphQL.Execution.outOfFuel]

/-- Response-field execution is covered when its recursive value completion is covered.
Witness: actual schema/coercion/resolver branching, exact modeled failure results, and
singleton alias mapping. Only the resolved-value branch uses the recursive premise.
-/
theorem responseFieldCoverage_of_values (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (valuesCovered : ValueCompletionCoverage containers schema resolvers variables fuel)
    (parentType : Name) (source : ResolverValue ObjectRef)
    : ResponseFieldCoverage containers schema resolvers variables (fuel + 1) parentType
        source := by
  intro name selected valid path usages deferMap
  cases selected with
  | nil =>
      intro state
      apply FieldsCompletionCovered.of_result_eq
      simp [executeResponseField, GraphQL.Execution.executeField, Completion.error]
  | cons field rest =>
      cases lookup : schema.lookupField parentType field.fieldName with
      | none =>
          intro state
          apply FieldsCompletionCovered.of_result_eq
          simp [executeResponseField, GraphQL.Execution.executeField, eraseField, lookup,
            Completion.error]
      | some definition =>
          cases coercion
                : coerceArgumentValues schema variables definition.arguments
                    field.arguments with
          | error =>
              intro state
              apply FieldsCompletionCovered.of_result_eq
              simp [executeResponseField, eraseField, lookup,
                coercion]
          | success arguments =>
              cases resolved
                    : resolveFieldValue resolvers parentType field.fieldName arguments
                        source with
              | none =>
                  intro state
                  apply FieldsCompletionCovered.of_result_eq
                  simp [executeResponseField, eraseField, lookup,
                    coercion, resolved]
              | some value =>
                  simp only [executeResponseField, GraphQL.Execution.executeField, List.map_cons,
                    eraseField, lookup, coercion, resolved]
                  refine runEnsures_bind
                    (ValueCompletionCovered containers (path ++ [.field name])
                      (GraphQL.Execution.completeValue schema resolvers variables fuel
                        definition.outputType ((field :: rest).map eraseField) value))
                    _ _ _ ?_ ?_
                  · exact valuesCovered definition.outputType (field :: rest) value valid
                      (path ++ [.field name]) usages deferMap true
                  · intro completed covered
                    apply runEnsures_pure
                    simpa only [List.map_cons, eraseField] using covered.field

/-- Actual field seeding also supplies unique initial field positions, even with errors.
Witness: the initial part of the generated ownership inventory's Nodup certificate.
-/
private theorem initial_fields_unique {path scope completed}
    (seeded
      : SeedOwnsCompletion (DeliveryPaths.fields true path)
          (ResponsePositions.fieldCursors path) scope completed)
    (initial : List (Name × ResponseValue)) (errors : Nat)
    (success : completed.result = .ok (initial, errors))
    : (ResponsePositions.fields true path initial).Nodup := by
  obtain ⟨slices, _, owned⟩ := seeded
  have unique := (List.nodup_append.mp owned.1).1
  simpa only [success, DeliveryPaths.result, source_fields_eq_positions] using unique

-----------------------------------------------------------------------------------------
-- Collected fields: actual threaded head/tail states and initial cursor uniqueness
-----------------------------------------------------------------------------------------

/-- Actual collected-field coverage follows from the per-field recursive comparison.
Witness: field-list descent, actual threaded completion states, and generated cursor/
uniqueness certificates. Counted nullable errors are allowed throughout.
This checked dependency edge is discharged by `RecursiveValueCoverage`'s value witness.
-/
theorem executeCollectedFields_entriesCovered_of_fields (containers : Bool)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (groups : CollectedFieldsMap)
    (valid : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables) groups)
    (unique : GroupsUnique groups)
    (fieldsCovered
      : ResponseFieldCoverage containers schema resolvers variables fuel
          parentType source)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    : RunEnsures
        (FieldsCompletionCovered containers path
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source (eraseGroups groups)))
        (executeCollectedFields schema resolvers variables fuel parentType source groups
          path usages deferMap) := by
  induction groups with
  | nil =>
      intro state
      apply FieldsCompletionCovered.of_result_eq
      simp [executeCollectedFields_nil, eraseGroups, GraphQL.Execution.executeCollectedFields,
        Completion.pure]
  | cons group rest ih =>
      obtain ⟨name, selected⟩ := group
      have validHead : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field :=
        valid (name, selected) (by simp)
      have validTail : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables) rest :=
        fun group member => valid group (List.mem_cons_of_mem _ member)
      have uniqueTail : GroupsUnique rest := (List.nodup_cons.mp unique).2
      intro state
      let headAction := executeResponseField schema resolvers variables fuel parentType source
        name selected path usages deferMap
      let head := (headAction.run state).1
      let next := (headAction.run state).2
      let tail := ((executeCollectedFields schema resolvers variables fuel parentType source rest
        path usages deferMap).run next).1
      have coversHead := fieldsCovered name selected validHead path usages deferMap state
      have coversTail := ih validTail uniqueTail next
      obtain ⟨headSlices, headSeed, _⟩ := MixedPaths.executeResponseField_seeded schema resolvers
        variables fuel parentType source name selected path usages deferMap state
      obtain ⟨tailSlices, tailSeed, _⟩ := MixedPaths.executeCollectedFields_seeded schema resolvers
        variables fuel parentType source rest uniqueTail path usages deferMap next
      have assembled := MixedPaths.executeCollectedFields_seeded schema resolvers variables
        fuel parentType source ((name, selected) :: rest) unique path usages deferMap state
      simp only [executeCollectedFields_cons, run_bind, StateT.run_pure, id_pure_eq] at assembled ⊢
      change SeedOwnsCompletion _ _ _ (Completion.combine List.append head tail) at assembled
      simp only [eraseGroups, List.map_cons, eraseGroup, GraphQL.Execution.executeCollectedFields]
      change FieldsCompletionCovered containers path
        (Result.combine List.append
          (GraphQL.Execution.executeField schema resolvers variables fuel parentType source
            name (selected.map eraseField))
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType
            source (eraseGroups rest))) (Completion.combine List.append head tail)
      exact FieldsCompletionCovered.append coversHead coversTail headSeed tailSeed
        (initial_fields_unique assembled)

-----------------------------------------------------------------------------------------
-- Deferred partitions: successful local fields become covered retained work
-----------------------------------------------------------------------------------------

/-- Actual deferred execution groups preserve the coverage of every ordinary partition.
Witness: partition-list descent at actual threaded states, local collected-field coverage,
and exact group retention. Every ambient cursor table is allowed for this work-only target.
-/
theorem collectExecutionGroups_entriesCovered_of_fields (containers : Bool)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (partitions : List (WorkQueueSemantics.NodeRefs × CollectedFieldsMap))
    (valid
      : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables)
          (partitions.flatMap Prod.snd))
    (unique : GroupsUnique (partitions.flatMap Prod.snd))
    (fieldsCovered
      : ResponseFieldCoverage containers schema resolvers variables fuel
          parentType source)
    (path : ResponsePath) (deferMap : DeferMap)
    : RunEnsures
        (WorkFieldsCovered containers path
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source (eraseGroups (partitions.flatMap Prod.snd))))
        (collectExecutionGroups schema resolvers variables fuel parentType source
          partitions path deferMap) := by
  induction partitions with
  | nil =>
      intro state
      simp only [collectExecutionGroups, StateT.run_pure, id_pure_eq]
      intro reference errors success cursors entry member _
      have empty : reference = [] := by
        simp only [List.flatMap_nil, eraseGroups, List.map_nil,
          GraphQL.Execution.executeCollectedFields, Except.ok.injEq, Prod.mk.injEq] at success
        exact success.1.symm
      simp [empty, TypedResponse.fields] at member
  | cons partition rest ih =>
      obtain ⟨usages, groups⟩ := partition
      have validHead : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables) groups :=
        fun group member => valid group (List.mem_append_left _ member)
      have validTail : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables)
          (rest.flatMap Prod.snd) :=
        fun group member => valid group (List.mem_append_right _ member)
      have uniqueParts : (groups.map Prod.fst ++ (rest.flatMap Prod.snd).map Prod.fst).Nodup := by
        simpa only [GroupsUnique, List.flatMap_cons, List.map_append] using unique
      intro state
      let headAction := executeCollectedFields schema resolvers variables fuel parentType source
        groups path usages deferMap
      let completed := (headAction.run state).1
      let next := (headAction.run state).2
      let tail := ((collectExecutionGroups schema resolvers variables fuel parentType source rest
        path deferMap).run next).1
      have coversHead := executeCollectedFields_entriesCovered_of_fields containers schema
        resolvers variables fuel parentType source groups validHead
        (List.nodup_append.mp uniqueParts).1 fieldsCovered path usages deferMap state
      have coversTail := ih validTail (List.nodup_append.mp uniqueParts).2.1 next
      simp only [collectExecutionGroups, executeExecutionGroup, run_bind, StateT.run_pure,
        id_pure_eq]
      change WorkFieldsCovered containers path
        (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType
          source (eraseGroups (groups ++ rest.flatMap Prod.snd)))
        (.combine (.executionGroup (usages.filterMap (lookupDeferredFragment? deferMap))
          path completed.outcome completed.work) tail)
      rw [eraseGroups, List.map_append, TypedResponse.basicFields_append_result]
      exact (coversHead.executionGroup _).append coversTail

-----------------------------------------------------------------------------------------
-- Execution plans: immediate and retained partitions cover the original collection
-----------------------------------------------------------------------------------------

/-- Actual plan execution covers all ordinary fields from its original collected map.
Witness: valid/unique plan partitioning, covered immediate/deferred execution, and exact
typed ordinary-entry permutation with arbitrary errors. The cancelled-work branch is
impossible under ordinary success, not justified by assuming success of future work.
-/
theorem executePlan_entriesCovered_of_fields (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (collection : FieldCollection)
    (valid
      : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables)
          collection.collectedFieldsMap)
    (unique : GroupsUnique collection.collectedFieldsMap)
    (fieldsCovered
      : ResponseFieldCoverage containers schema resolvers variables fuel
          parentType source)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    : RunEnsures
        (FieldsCompletionCovered containers path
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source (eraseGroups collection.collectedFieldsMap)))
        (executeExecutionPlan schema resolvers variables fuel parentType source
          collection.newDeferUsages
          (buildExecutionPlan collection.collectedFieldsMap usages) path usages
          deferMap) := by
  let plan := buildExecutionPlan collection.collectedFieldsMap usages
  have partitionValid := ArgumentValidity.buildExecutionPlan_valid variables
    collection.collectedFieldsMap usages valid
  have tasksValid : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables)
      (plan.newCollectedFieldsMaps.flatMap Prod.snd) := by
    intro group member
    obtain ⟨partition, member, inPartition⟩ := List.mem_flatMap.mp member
    exact partitionValid.2 partition member group inPartition
  have uniqueParts : (plan.collectedFieldsMap.map Prod.fst
      ++ (plan.newCollectedFieldsMaps.flatMap Prod.snd).map Prod.fst).Nodup := by
    have permuted := (buildExecutionPlan_perm collection.collectedFieldsMap usages).map Prod.fst
    simpa only [executionPlanGroups, List.map_append] using permuted.nodup_iff.mpr unique
  let ordinaryInitial := GraphQL.Execution.executeCollectedFields schema resolvers variables
    fuel parentType source (eraseGroups plan.collectedFieldsMap)
  let ordinaryTasks := GraphQL.Execution.executeCollectedFields schema resolvers variables
    fuel parentType source (eraseGroups (plan.newCollectedFieldsMaps.flatMap Prod.snd))
  have reordered : ∀ completed,
      FieldsCompletionCovered containers path (Result.combine List.append ordinaryInitial
        ordinaryTasks) completed
      → FieldsCompletionCovered containers path
        (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType
          source (eraseGroups collection.collectedFieldsMap)) completed := by
    intro completed covered
    apply covered.of_referenceComparison
    intro reference errors success
    obtain ⟨ordered, outcome, permuted⟩ := TypedResponse.basicFields_perm_entries_withErrors
      schema resolvers variables fuel parentType source path
      (buildExecutionPlan_erasure_perm collection.collectedFieldsMap usages).symm success
    have erased : eraseGroups (executionPlanGroups plan)
        = eraseGroups plan.collectedFieldsMap
          ++ eraseGroups (plan.newCollectedFieldsMaps.flatMap Prod.snd) := by
      simp [eraseGroups, executionPlanGroups]
    rw [erased, TypedResponse.basicFields_append_result] at outcome
    exact ⟨ordered, errors, outcome, permuted.symm⟩
  simp only [executeExecutionPlan]
  refine runEnsures_bind (FieldsCompletionCovered containers path ordinaryInitial)
    _ _ _ ?_ ?_
  · exact executeCollectedFields_entriesCovered_of_fields containers schema resolvers variables
      fuel parentType source plan.collectedFieldsMap partitionValid.1
      (List.nodup_append.mp uniqueParts).1 fieldsCovered path usages _
  · intro initial covered
    split
    · rename_i errors failed
      exact runEnsures_pure _ _ (reordered initial
        (covered.append_when_error errors failed ordinaryTasks))
    · refine runEnsures_bind (WorkFieldsCovered containers path ordinaryTasks)
        _ _ _ ?_ ?_
      · exact collectExecutionGroups_entriesCovered_of_fields containers schema resolvers
          variables fuel parentType source plan.newCollectedFieldsMaps tasksValid
          (List.nodup_append.mp uniqueParts).2.1 fieldsCovered path _
      · intro tasks tasksCovered
        exact runEnsures_pure _ _ (reordered _ (covered.withWork tasksCovered))

-----------------------------------------------------------------------------------------
-- Root collection connects the checked plan comparison to actual prepared query work
-----------------------------------------------------------------------------------------

/-- Prepared root coverage reduces to response-field coverage for the same execution.
Witness: actual collection preserves directive erasure, valid arguments, and response-name
uniqueness; the checked plan witness then covers the ordinary root's successful fields.
-/
theorem executeRoot_entriesCovered_of_fields (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (valid : SelectionSet.hasValidIncrementalArguments variables selections = true)
    (fieldsCovered
      : ResponseFieldCoverage containers schema resolvers variables fuel
          parentType source)
    : RunEnsures
        (FieldsCompletionCovered containers []
          (GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
            parentType source (SelectionSet.eraseIncrementalDirectives selections)))
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) := by
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind
    (fun collection =>
      eraseGroups collection.collectedFieldsMap
        = GraphQL.Execution.collectFields schema variables parentType source
          (SelectionSet.eraseIncrementalDirectives selections)
      ∧ GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables)
        collection.collectedFieldsMap
      ∧ GroupsUnique collection.collectedFieldsMap) _ _ _ ?_ ?_
  · intro state
    exact ⟨collectFields_erase schema variables parentType source selections none state,
      ArgumentValidity.collectFields_valid schema variables parentType source selections
        valid none state,
      collectFields_unique schema variables parentType source selections none state⟩
  · intro collection collected
    simpa only [GraphQL.Execution.executeRootSelectionSet, collected.1]
      using executePlan_entriesCovered_of_fields containers schema resolvers variables
        fuel parentType source collection collected.2.1 collected.2.2 fieldsCovered [] []
        []

end GraphQL.IncrementalDelivery.Correctness
