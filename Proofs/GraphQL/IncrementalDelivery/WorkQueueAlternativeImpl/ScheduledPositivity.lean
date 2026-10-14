import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledExecutor
import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskErrors

/-! Positive failure accounting for the genuinely recursive sequential cut policy.
The graph root is `RecursiveScheduledPositivity`; `PlanPositivity` is its checked
decomposition. All certificates are constructed from actual recursion, without assuming
a correspondence to eager/native outcomes. Existing completion/work predicates and
constructor proofs are reused. This rules out raw zero-count fatal cuts for generated
scheduled execution, including retained deferred/streamed descendants; it does not prove
recursive data/work/key correspondence or native error-object identity. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledExecution

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Correctness.ExecutionErrors
  (
  WorkPositive ItemsPositive Positive pure error combine map catchNull nonNull failedField
  )

variable {ObjectRef : Type}

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

/-- Root certificate for the actual recursively cut completion and every retained task. -/
def RecursiveScheduledPositivity : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    selections,
    RunEnsures Positive
      (executeRootSelectionSetCore schema resolvers variables fuel parentType source
        selections)

/-- Plan certificate at each generated object/root boundary, with arbitrary context. -/
def PlanPositivity : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    (collection : FieldCollection) path usages context,
    RunEnsures Positive
      (executeExecutionPlan schema resolvers variables fuel parentType source
        collection.newDeferUsages
        (buildExecutionPlan collection.collectedFieldsMap usages) path usages context)

/-- Checked root edge: collection passes its actual plan to the recursive certificate. -/
theorem recursiveScheduledPositivity_of_plan (plans : PlanPositivity)
    : RecursiveScheduledPositivity := by
  intro ObjectRef schema resolvers variables fuel parentType source selections
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind (fun _ : FieldCollection => True) _ _ _ (fun _ => trivial) ?_
  intro collection _
  exact plans ObjectRef schema resolvers variables fuel parentType source collection
    [] [] []

mutual
  /-- Plan execution retains certified immediate and deferred work, by mutual induction.
  -/
  theorem executePlan_positive (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures Positive
          (executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages
            (buildExecutionPlan collection.collectedFieldsMap usages) path usages
            deferMap) := by
    simp only [executeExecutionPlan]
    refine runEnsures_bind Positive _ _ _ ?_ ?_
    · exact executeCollectedFields_positive schema resolvers variables fuel parentType source
        _ path usages _
    · intro completed hc
      split
      · exact runEnsures_pure _ _ hc
      · refine runEnsures_bind WorkPositive _ _ _ ?_ ?_
        · exact collectExecutionGroups_positive schema resolvers variables fuel parentType
            source _ path _
        · intro work hw
          exact runEnsures_pure _ _ ⟨hc.1, hc.2, hw⟩
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Every deferred group and its children retain positivity, by group-list induction. -/

  theorem collectExecutionGroups_positive (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap))
      (path : ResponsePath)
      (deferMap : DeferMap)
      : RunEnsures WorkPositive
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap) := by
    cases partitions with
    | nil => simp [collectExecutionGroups, RunEnsures, WorkPositive]
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        simp only [collectExecutionGroups]
        refine runEnsures_bind Positive _ _ _ ?_ ?_
        · exact executeCollectedFields_positive schema resolvers variables fuel parentType
            source groups path usages deferMap
        · intro completed hc
          refine runEnsures_bind WorkPositive _ _ _ ?_ ?_
          · exact collectExecutionGroups_positive schema resolvers variables fuel parentType
              source rest path deferMap
          · intro work hw
            exact runEnsures_pure _ _ ⟨hc, hw⟩
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Collected fields preserve positivity when combined, by field-list induction. -/

  theorem executeCollectedFields_positive (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap)
      : RunEnsures Positive
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages deferMap) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields] using runEnsures_pure _ _ (pure ([] : List
          (Name × ResponseValue)))
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        simp only [executeCollectedFields]
        refine runEnsures_bind Positive _ _ _ ?_ ?_
        · exact executeResponseField_positive schema resolvers variables fuel parentType source name
            fields path usages deferMap
        · intro head hh
          split
          · exact runEnsures_pure _ _ hh
          · refine runEnsures_bind Positive _ _ _ ?_ ?_
            · exact executeCollectedFields_positive schema resolvers variables fuel parentType
                source rest path usages deferMap
            · intro tail ht
              exact runEnsures_pure _ _ (combine List.append head tail hh ht)
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Field execution preserves positivity through lookup and completion cases. -/

  theorem executeResponseField_positive (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (fields : List FieldDetails) (path : ResponsePath)
      (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures Positive
          (executeResponseField schema resolvers variables fuel parentType source name
            fields path usages deferMap) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField]
          using runEnsures_pure _ _
            (error (α := List (Name × ResponseValue)) 1 (by decide))
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField]
              using runEnsures_pure _ _
                (error (α := List (Name × ResponseValue)) 1 (by decide))
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact runEnsures_pure _ _ (error 1 (by decide))
            · split
              · exact runEnsures_pure _ _ (failedField _ _)
              · split
                · exact runEnsures_pure _ _ (failedField _ _)
                · refine runEnsures_bind Positive _ _ _ ?_ ?_
                  · exact completeValue_positive schema resolvers variables fuel _ _ _
                      (path ++ [.field name]) usages deferMap true
                  · intro completed hc
                    exact runEnsures_pure _ _ (map _ completed hc)
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Value completion preserves positivity for every type, by mutual fuel induction. -/

  theorem completeValue_positive (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures Positive
          (completeValue schema resolvers variables fuel fieldType fields value path
            usages deferMap allowStream) := by
    cases fuel with
    | zero =>
        simpa only [completeValue]
          using runEnsures_pure _ _ (error (α := ResponseValue) 1 (by decide))
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simp only [completeValue]
            refine runEnsures_bind Positive _ _ _ ?_ ?_
            · exact completeValue_positive schema resolvers variables (fuel + 1) inner fields
                value path usages deferMap allowStream
            · intro completed hc
              exact runEnsures_pure _ _ (nonNull completed hc)
        | named parentType =>
            cases value with
            | null =>
                simpa only [completeValue] using runEnsures_pure _ _ (pure ResponseValue.null)
            | scalar scalar =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (error 1 (by decide))
                · exact runEnsures_pure _ _ (pure _)
            | list items =>
                simpa only [completeValue]
                  using runEnsures_pure _ _ (error (α := ResponseValue) 1 (by decide))
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (error 1 (by decide))
                · refine runEnsures_bind (fun _ : FieldCollection => True) _ _ _
                    (fun _ => trivial) ?_
                  intro collection _
                  refine runEnsures_bind Positive _ _ _ ?_ ?_
                  · exact executePlan_positive schema resolvers variables fuel runtimeType
                      (.object runtimeType ref) collection path usages deferMap
                  · intro completed hv
                    exact runEnsures_pure _ _ (catchNull _ completed hv)
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue] using runEnsures_pure _ _ (pure ResponseValue.null)
            | scalar scalar =>
                simpa only [completeValue]
                  using runEnsures_pure _ _ (error (α := ResponseValue) 1 (by decide))
            | object runtimeType ref =>
                simpa only [completeValue]
                  using runEnsures_pure _ _ (error (α := ResponseValue) 1 (by decide))
            | list items =>
                simpa only [completeValue] using completeListValueWithStream_positive
                  schema resolvers variables fuel inner fields items path usages deferMap
                  allowStream
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- The stream hook preserves positive failures in both the initial prefix and tail;
  witness: ordinary completion and item-tail certificates.
  -/
  theorem completeListValueWithStream_positive (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath)
      (usages : List Nat) (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures Positive
          (completeListValueWithStream schema resolvers variables fuel inner fields
            values path usages deferMap allowStream) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact runEnsures_pure _ _ ⟨by simp [BasicErrors.PositiveFailure], trivial⟩
    · refine runEnsures_bind Positive _ _ _ ?_ ?_
      · exact completeListValue_positive schema resolvers variables fuel inner fields
          values path 0 usages deferMap
      · intro completed hc
        exact runEnsures_pure _ _ (catchNull _ completed hc)
    · rename_i usage _
      refine runEnsures_bind Positive _ _ _ ?_ ?_
      · exact completeListValue_positive schema resolvers variables fuel inner fields
          (values.take usage.initialCount) path 0 usages deferMap
      · intro initial hi
        split
        · exact runEnsures_pure _ _ (catchNull _ initial hi)
        · split
          · exact runEnsures_pure _ _ (catchNull _ initial hi)
          · refine runEnsures_bind (fun _ : Nat => True) _ _ _ (fun _ => trivial) ?_
            intro key _
            refine runEnsures_bind ItemsPositive _ _ _ ?_ ?_
            · exact completeStreamItems_positive schema resolvers variables fuel inner
                _ _ path usage.initialCount
            · intro tail ht
              exact runEnsures_pure _ _ ⟨(catchNull _ initial hi).1,
                (catchNull _ initial hi).2, ht⟩
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary list completion preserves positivity, by item-list induction. -/

  theorem completeListValue_positive (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures Positive
          (completeListValue schema resolvers variables fuel itemType fields values path
            index usages deferMap) := by
    cases values with
    | nil =>
        simpa only [completeListValue] using runEnsures_pure _ _ (pure ([] : List ResponseValue))
    | cons value rest =>
        simp only [completeListValue]
        refine runEnsures_bind Positive _ _ _ ?_ ?_
        · exact completeValue_positive schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) usages deferMap false
        · intro head hh
          split
          · rename_i errors failed
            exact runEnsures_pure _ _ (error errors (hh.1 errors failed))
          · refine runEnsures_bind Positive _ _ _ ?_ ?_
            · exact completeListValue_positive schema resolvers variables fuel itemType fields
                rest path (index + 1) usages deferMap
            · intro tail ht
              exact runEnsures_pure _ _ (combine List.cons head tail hh ht)
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Stream tails retain a positive failing item or recursively certified successful
  items; witness: the exact early-stop branch of completeStreamItems.
  -/
  theorem completeStreamItems_positive (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      : RunEnsures ItemsPositive
          (completeStreamItems schema resolvers variables fuel itemType fields values
            path index) := by
    cases values with
    | nil => simp [completeStreamItems, RunEnsures, ItemsPositive]
    | cons value rest =>
        simp only [completeStreamItems]
        refine runEnsures_bind Positive _ _ _ ?_ ?_
        · exact completeValue_positive schema resolvers variables fuel itemType fields
            value (path ++ [.index index]) [] [] false
        · intro head hh
          split
          · rename_i errors he
            exact runEnsures_pure _ _ ⟨by simpa only [he] using hh.1, trivial, trivial⟩
          · refine runEnsures_bind ItemsPositive _ _ _ ?_ ?_
            · exact completeStreamItems_positive schema resolvers variables fuel itemType
                fields rest path (index + 1)
            · intro tail ht
              exact runEnsures_pure _ _ ⟨hh.1, hh.2, ht⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

end

/-- Discharged recursive plan obligation, not an assumed execution invariant. -/
theorem planPositivity_holds : PlanPositivity :=
  fun _ schema resolvers variables fuel parentType source collection path usages
      context =>
    executePlan_positive schema resolvers variables fuel parentType source collection
      path usages context

/-- Full recursive root certificate obtained through the checked decomposition. -/
theorem recursiveScheduledPositivity_holds : RecursiveScheduledPositivity :=
  recursiveScheduledPositivity_of_plan planPositivity_holds

/-- Task-visible failures inherit the actual root's recursive certificate; callers do
not supply a separate positivity premise or independently selected Work tree. -/
theorem root_task_failure_positive (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (supply : Nat)
    {occurrence owners producer payload errors}
    (task
      : WorkQueueSemantics.TaskAt
          ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            supply).1.work occurrence owners producer payload)
    (failed : payload.failure = some errors)
    : 0 < errors := by
  have positive :=
    recursiveScheduledPositivity_holds ObjectRef schema resolvers variables fuel
      parentType source selections supply
  simpa only [failed, Option.getD_some]
    using positive.2.task task (by simp only [failed, Option.isSome_some])

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledExecution
