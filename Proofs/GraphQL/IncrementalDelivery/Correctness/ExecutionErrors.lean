import Proofs.GraphQL.IncrementalDelivery.Semantics.BasicErrors
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
  /-- Every failing result in this work and its descendants has a positive error count. -/
  def WorkPositive : Work → Prop
    | .empty => True
    | .combine left right => WorkPositive left ∧ WorkPositive right
    | .executionGroup _ _ result children =>
        BasicErrors.PositiveFailure result ∧ WorkPositive children
    | .stream _ items => ItemsPositive items

  /-- Each streamed item's result and child work satisfy positive failure accounting. -/
  def ItemsPositive : List (Result ResponseValue × Work) → Prop
    | [] => True
    | (result, children) :: rest =>
        BasicErrors.PositiveFailure result ∧ WorkPositive children ∧ ItemsPositive rest
end

/-- The initial completion and all nested work have positive failure counts. -/

def Positive (completed : Completion α) : Prop :=
  BasicErrors.PositiveFailure completed.result ∧ WorkPositive completed.work

/-- Pure completion has no failure, by its successful result constructor. -/

theorem pure (value : α) : Positive (Completion.pure value) := by
  simp [Positive, Completion.pure, BasicErrors.PositiveFailure, WorkPositive]

/-- An explicit positive error satisfies the certificate, with empty child work. -/

theorem error {α : Type} (errors : Nat) (h : 0 < errors)
    : Positive (Completion.error errors : Completion α) := by
  simpa [Positive, Completion.error, BasicErrors.PositiveFailure, WorkPositive] using h

/-- Combining certified completions preserves positivity, by result case analysis. -/

theorem combine (f : α → β → γ) (left : Completion α) (right : Completion β)
    (hl : Positive left) (hr : Positive right)
    : Positive (Completion.combine f left right) := by
  have hp := BasicErrors.combine f left.result right.result hl.1 hr.1
  cases he : Result.combine f left.result right.result with
  | error errors => simpa only [Completion.combine, he] using error errors (hp errors he)
  | ok result =>
      simp only [Completion.combine, he]
      exact ⟨by simp [BasicErrors.PositiveFailure], hl.2, hr.2⟩

/-- Mapping success preserves the certificate; failure discards work. -/

theorem map (f : α → β) (completed : Completion α) (h : Positive completed)
    : Positive (Completion.map f completed) := by
  cases he : completed.result with
  | error errors => simpa only [Completion.map, he] using error errors (h.1 errors he)
  | ok result =>
      rcases result with ⟨value, errors⟩
      simpa [Positive, Completion.map, he, BasicErrors.PositiveFailure] using h.2

/-- Catching null removes bubbling failure and retains only successful child work. -/

theorem catchNull (f : α → ResponseValue) (completed : Completion α)
    (h : Positive completed)
    : Positive (Completion.catchNull f completed) := by
  cases he : completed.result <;>
    simp [Positive, Completion.catchNull, he, BasicErrors.PositiveFailure, WorkPositive, h.2]

/-- Non-null completion preserves or introduces a positive error, by result cases. -/

theorem nonNull (completed : Completion ResponseValue) (h : Positive completed)
    : Positive (Completion.nonNull completed) := by
  have hp := BasicErrors.nonNull completed.result h.1
  unfold Completion.nonNull
  split
  · rename_i errors he
    exact error errors (hp errors he)
  · exact ⟨by simp [BasicErrors.PositiveFailure], h.2⟩

/-- A failed field has a counted error, by the inherited field-error rules. -/

theorem failedField (name : Name) (fieldType : TypeRef)
    : Positive
        ({
            result :=
              GraphQL.Execution.singleFieldResult name
                (GraphQL.Execution.handleFieldError fieldType)
          }
          : Completion _) :=
  ⟨BasicErrors.field name _ (BasicErrors.handle fieldType), trivial⟩

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
            collection.newDeferUsages (buildExecutionPlan collection.fields usages) path
            usages deferMap) := by
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
        simp only [collectExecutionGroups, executeExecutionGroup]
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
      (fields : List ExecutableField) (path : ResponsePath)
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
      (fields : List ExecutableField) (value : ResolverValue ObjectRef)
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
      (inner : TypeRef) (fields : List ExecutableField)
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
      (itemType : TypeRef) (fields : List ExecutableField)
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
      (itemType : TypeRef) (fields : List ExecutableField)
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
