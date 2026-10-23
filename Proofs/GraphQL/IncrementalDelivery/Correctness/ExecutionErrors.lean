import Proofs.GraphQL.IncrementalDelivery.Semantics.BasicErrors
import Proofs.GraphQL.IncrementalDelivery.Semantics.CompletionReporting
import Proofs.GraphQL.IncrementalDelivery.Semantics.SingleStreamCompletion
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectionProperties

/-! Every bubbling failure in mixed defer/stream execution carries a positive count.
The structural certificate concerns the actual finite work, not scheduler admission.
-/

namespace GraphQL.IncrementalDelivery.Correctness.ExecutionErrors

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

variable {ObjectRef : Type}

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  /-- Every failing delivery projection in this work and its descendants is positive. -/
  def WorkPositive : Work → Prop
    | .empty => True
    | .declareGroups _ tasks => WorkPositive tasks
    | .combine left right => WorkPositive left ∧ WorkPositive right
    | .executionGroup _ _ result children =>
        BasicErrors.PositiveFailure result.deliveryResult ∧ WorkPositive children
    | .stream _ items => ItemsPositive items

  /-- Each streamed item's result and child work satisfy positive failure accounting. -/
  def ItemsPositive : List (TaskOutcome ResponseValue × Work) → Prop
    | [] => True
    | (result, children) :: rest =>
        BasicErrors.PositiveFailure result.deliveryResult
        ∧ WorkPositive children
        ∧ ItemsPositive rest
end

/-- Collected failures and nested delivery failures are positive; the selected cause
is positive and bounded by the completion's collected diagnostics.
-/

def Positive (completed : Completion α) : Prop :=
  BasicErrors.PositiveFailure completed.result
  ∧ WorkPositive completed.work
  ∧ CompletionReporting.CauseValid completed

theorem deliveryPositive {completed : Completion α} (h : Positive completed)
    : BasicErrors.PositiveFailure completed.deliveryResult :=
  fun _ failed => CompletionReporting.deliveryResult_positive completed h.2.2 failed

/-- Pure completion has no failure or retained cause. -/
theorem pure (value : α) : Positive (Completion.pure value) :=
  ⟨
    by simp [BasicErrors.PositiveFailure, Completion.pure],
    trivial,
    CompletionReporting.pure_valid value
  ⟩

/-- An explicit positive error supplies its own delivery explanation. -/
theorem error {α : Type} (errors : Nat) (h : 0 < errors)
    : Positive (Completion.error errors : Completion α) :=
  ⟨
    by simpa [BasicErrors.PositiveFailure, Completion.error] using h,
    trivial,
    CompletionReporting.error_valid errors h
  ⟩

/-- Combination preserves collected positivity, child work, and the selected cause. -/
theorem combine (f : α → β → γ) (left : Completion α) (right : Completion β)
    (hl : Positive left) (hr : Positive right)
    : Positive (Completion.combine f left right) := by
  refine ⟨?_, ?_, CompletionReporting.combine_valid f left right hl.2.2 hr.2.2⟩
  · simpa only [CompletionReporting.combine_result]
      using BasicErrors.combine f left.result right.result hl.1 hr.1
  · cases he : Result.combine f left.result right.result with
    | error errors => simp [Completion.combine, he, Completion.error, WorkPositive]
    | ok result =>
        simpa only [Completion.combine, he, WorkPositive] using And.intro hl.2.1 hr.2.1

/-- Mapping success preserves diagnostics and clears any caught-null cause. -/
theorem map (f : α → β) (completed : Completion α) (h : Positive completed)
    : Positive (Completion.map f completed) := by
  refine ⟨?_, ?_, CompletionReporting.map_valid f completed h.2.2⟩
  · cases he : completed.result with
    | error errors =>
        simpa [Completion.map, he, Completion.error, BasicErrors.PositiveFailure] using h.1 errors he
    | ok result => simp [Completion.map, he, BasicErrors.PositiveFailure]
  · cases he : completed.result with
    | error errors => simp [Completion.map, he, Completion.error, WorkPositive]
    | ok result => simpa only [Completion.map, he] using h.2.1

/-- Catching a failure retains its cause with null and every collected diagnostic. -/
theorem catchNull (f : α → ResponseValue) (completed : Completion α)
    (h : Positive completed)
    : Positive (Completion.catchNull f completed) := by
  refine ⟨?_, ?_, CompletionReporting.catchNull_valid f completed h.2.2⟩
  · cases he : completed.result <;> simp [Completion.catchNull, he, BasicErrors.PositiveFailure]
  · cases he : completed.result with
    | error errors => simp [Completion.catchNull, he, WorkPositive]
    | ok result => simpa only [Completion.catchNull, he] using h.2.1

/-- Non-null completion propagates an existing positive cause or creates a null violation. -/
theorem nonNull (completed : Completion ResponseValue) (h : Positive completed)
    : Positive (Completion.nonNull completed) := by
  refine ⟨?_, ?_, CompletionReporting.nonNull_valid completed h.2.2⟩
  · have hp := BasicErrors.nonNull completed.result h.1
    cases he : nonNullCompletion completed.result with
    | error errors =>
        simpa [Completion.nonNull, he, Completion.error, BasicErrors.PositiveFailure] using hp errors he
    | ok result => simp [Completion.nonNull, he, BasicErrors.PositiveFailure]
  · unfold Completion.nonNull
    split
    · trivial
    · exact h.2.1

/-- Field errors retain the cause supplied by the field completion boundary. -/
theorem failedField (name : Name) (fieldType : TypeRef)
    : Positive
        ({
            result :=
              GraphQL.Execution.singleFieldResult name
                (GraphQL.Execution.handleFieldError fieldType),
            cause := if fieldType.isNonNull then some 1 else none
          }
          : Completion _) := by
  refine ⟨BasicErrors.field name _ (BasicErrors.handle fieldType), trivial, ?_⟩
  cases fieldType <;>
    simp [CompletionReporting.CauseValid, CompletionReporting.diagnostics,
      GraphQL.Execution.singleFieldResult, GraphQL.Execution.handleFieldError, TypeRef.isNonNull]

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
          apply runEnsures_pure
          refine ⟨hc.1, ⟨hc.2.1, ?_⟩, hc.2.2⟩
          exact hw
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
        simp only [collectExecutionGroups, executeExecutionGroup]
        refine runEnsures_bind Positive _ _ _ ?_ ?_
        · exact executeCollectedFields_positive schema resolvers variables fuel parentType
            source groups path usages deferMap
        · intro completed hc
          refine runEnsures_bind WorkPositive _ _ _ ?_ ?_
          · exact collectExecutionGroups_positive schema resolvers variables fuel parentType
              source rest path deferMap
          · intro work hw
            exact runEnsures_pure _ _ ⟨⟨deliveryPositive hc, hc.2.1⟩, hw⟩
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
        simpa only [executeCollectedFields_nil] using runEnsures_pure _ _ (pure ([] : List
          (Name × ResponseValue)))
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        simp only [executeCollectedFields_cons]
        refine runEnsures_bind Positive _ _ _ ?_ ?_
        · exact executeResponseField_positive schema resolvers variables fuel parentType source name
            fields path usages deferMap
        · intro head hh
          refine runEnsures_bind Positive _ _ _ ?_ ?_
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
    · rename_i errors he
      have count : errors = 1 := by
        split at he
        · exact getStreamUsage_error_count variables _ errors he
        · simp at he
      subst errors
      exact runEnsures_pure _ _ ⟨by simp [BasicErrors.PositiveFailure], trivial,
        by simp [CompletionReporting.CauseValid, CompletionReporting.diagnostics]⟩
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
            intro ref _
            refine runEnsures_bind ItemsPositive _ _ _ ?_ ?_
            · exact completeStreamItems_positive schema resolvers variables fuel inner
                _ _ path usage.initialCount
            · intro tail ht
              exact runEnsures_pure _ _ ⟨(catchNull _ initial hi).1,
                ⟨(catchNull _ initial hi).2.1, ht⟩, (catchNull _ initial hi).2.2⟩
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
          refine runEnsures_bind Positive _ _ _ ?_ ?_
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
            exact runEnsures_pure _ _ ⟨deliveryPositive hh, trivial, trivial⟩
          · refine runEnsures_bind ItemsPositive _ _ _ ?_ ?_
            · exact completeStreamItems_positive schema resolvers variables fuel itemType
                fields rest path (index + 1)
            · intro tail ht
              exact runEnsures_pure _ _ ⟨deliveryPositive hh, hh.2.1, ht⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

end

/-- Every root execution certifies retained failures, by collection then plan execution. -/

theorem executeRootSelectionSetCore_positive (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : RunEnsures Positive
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) := by
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind (fun _ : FieldCollection => True) _ _ _ (fun _ => trivial) ?_
  intro collection _
  exact executePlan_positive schema resolvers variables fuel parentType source collection
    [] [] []

end GraphQL.IncrementalDelivery.Correctness.ExecutionErrors
