import Proofs.GraphQL.IncrementalDelivery.Correctness.ExecutionErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence

/-! Generated delivery failures select one primitive error even when diagnostics accumulate. -/

namespace GraphQL.IncrementalDelivery.Correctness.BoundaryErrorCounts
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

variable {ObjectRef : Type}
attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

/-- A failed delivery outcome selects one primitive execution error. -/
def OneFailure (result : Result α) : Prop := ∀ errors, result = .error errors → errors = 1

mutual
  /-- Deferred and streamed task boundaries select one error throughout generated work. -/
  def WorkCertified : Work → Prop
    | .empty => True
    | .declareGroups _ tasks => WorkCertified tasks
    | .combine left right => WorkCertified left ∧ WorkCertified right
    | .executionGroup _ _ result children =>
        OneFailure result.deliveryResult ∧ WorkCertified children
    | .stream _ items => ItemsCertified items

  /-- Each finite stream entry has a certified boundary and certified child work. -/
  def ItemsCertified : List (TaskOutcome ResponseValue × Work) → Prop
    | [] => True
    | (result, children) :: rest =>
        OneFailure result.deliveryResult ∧ WorkCertified children ∧ ItemsCertified rest
end

/-- Every retained cause is one; collected diagnostics may contain several errors. -/
def CauseOne (completed : Completion α) : Prop :=
  ∀ errors, completed.cause = some errors → errors = 1

/-- An escaping completion failure retains the selected primitive error. -/
def FatalCause (completed : Completion α) : Prop :=
  ∀ errors, completed.result = .error errors → completed.cause = some 1

/-- The certificate tracks selected causes separately from aggregate diagnostics. -/
def Certified (completed : Completion α) : Prop :=
  CauseOne completed ∧ WorkCertified completed.work ∧ FatalCause completed

/-- A certified completion exposes its selected primitive count at a task boundary. -/
theorem delivery_one {completed : Completion α} (certified : Certified completed)
    : OneFailure completed.deliveryResult := by
  intro errors failed
  cases result : completed.result with
  | error diagnostics =>
      have cause := certified.2.2 diagnostics result
      simpa [Completion.deliveryResult, Completion.outcome, TaskOutcome.deliveryResult,
        result, cause] using failed.symm
  | ok value =>
      simp [Completion.deliveryResult, Completion.outcome, TaskOutcome.deliveryResult, result] at failed

/-- Pure values introduce no retained error cause. -/
theorem pure (value : α) : Certified (Completion.pure value) := by
  simp [Certified, CauseOne, FatalCause, Completion.pure, WorkCertified]

/-- A primitive error selects its own count. -/
theorem error {α : Type} (errors : Nat) (one : errors = 1)
    : Certified (Completion.error errors : Completion α) := by
  subst errors
  simp [Certified, CauseOne, FatalCause, Completion.error, WorkCertified]

/-- Combining diagnostics retains the selected escaping branch's unit cause. -/
theorem combine (f : α → β → γ) (left : Completion α) (right : Completion β)
    (hl : Certified left) (hr : Certified right)
    : Certified (Completion.combine f left right) := by
  cases l : left.result with
  | error errors =>
      have cause := hl.2.2 errors l
      cases r : right.result <;>
        simp [Certified, CauseOne, FatalCause, Completion.combine, Result.combine,
          l, r, cause, Completion.error, WorkCertified]
  | ok value =>
      cases r : right.result with
      | error errors =>
          have cause := hr.2.2 errors r
          simp [Certified, CauseOne, FatalCause, Completion.combine, Result.combine,
            l, r, cause, Completion.error, WorkCertified]
      | ok other =>
          simpa [Certified, CauseOne, FatalCause, Completion.combine, Result.combine,
            l, r, WorkCertified] using And.intro hl.2.1 hr.2.1

/-- Successful mapping clears a caught-null cause and preserves child boundaries. -/
theorem map (f : α → β) (completed : Completion α) (h : Certified completed)
    : Certified (Completion.map f completed) := by
  cases result : completed.result with
  | error errors =>
      have cause := h.2.2 errors result
      simp [Certified, CauseOne, FatalCause, Completion.map, Completion.error,
        result, cause, WorkCertified]
  | ok value =>
      simpa [Certified, CauseOne, FatalCause, Completion.map, result] using h.2.1

/-- A caught null retains the selected primitive cause. -/
theorem catchNull (f : α → ResponseValue) (completed : Completion α)
    (h : Certified completed)
    : Certified (Completion.catchNull f completed) := by
  cases result : completed.result with
  | error errors =>
      have cause := h.2.2 errors result
      simp [Certified, CauseOne, FatalCause, Completion.catchNull, result, cause, WorkCertified]
  | ok value =>
      simpa [Certified, CauseOne, FatalCause, Completion.catchNull, result] using h.2.1

/-- Non-null completion rethrows a selected error or introduces one null violation. -/
theorem nonNull (completed : Completion ResponseValue) (h : Certified completed)
    : Certified (Completion.nonNull completed) := by
  cases result : completed.result with
  | error errors =>
      have cause := h.2.2 errors result
      simp [Certified, CauseOne, FatalCause, Completion.nonNull, nonNullCompletion,
        result, cause, Completion.error, WorkCertified]
  | ok pair =>
      obtain ⟨value, errors⟩ := pair
      cases cause : completed.cause with
      | none =>
          cases value with
          | null =>
              simp [Certified, CauseOne, FatalCause, Completion.nonNull,
                nonNullCompletion, result, cause, Completion.error, WorkCertified]
          | scalar value | object value | list value =>
              simpa [Certified, CauseOne, FatalCause, Completion.nonNull,
                nonNullCompletion, result, cause, Completion.error, WorkCertified] using h.2.1
      | some count =>
          have one := h.1 count cause
          subst count
          cases value with
          | null =>
              simp [Certified, CauseOne, FatalCause, Completion.nonNull,
                nonNullCompletion, result, cause, Completion.error, WorkCertified]
          | scalar value | object value | list value =>
              simpa [Certified, CauseOne, FatalCause, Completion.nonNull,
                nonNullCompletion, result, cause, Completion.error, WorkCertified] using h.2.1

/-- Field lookup failures select one primitive cause when they escape non-null completion. -/
theorem failedField (name : Name) (fieldType : TypeRef)
    : Certified
        ({
            result :=
              GraphQL.Execution.singleFieldResult name
                (GraphQL.Execution.handleFieldError fieldType),
            cause := if fieldType.isNonNull then some 1 else none
          }
          : Completion _) := by
  cases fieldType <;>
    simp [Certified, CauseOne, FatalCause, WorkCertified,
      GraphQL.Execution.singleFieldResult, GraphQL.Execution.handleFieldError, TypeRef.isNonNull]

mutual
  /-- Plan execution retains certified immediate and deferred work, by mutual induction.
  -/
  theorem executePlan_counted (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures Certified
          (executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages
            (buildExecutionPlan collection.collectedFieldsMap usages) path usages
            deferMap) := by
    simp only [executeExecutionPlan]
    refine runEnsures_bind Certified _ _ _ ?_ ?_
    · exact executeCollectedFields_counted schema resolvers variables fuel parentType source
        _ path usages _
    · intro completed hc
      split
      · exact runEnsures_pure _ _ hc
      · refine runEnsures_bind WorkCertified _ _ _ ?_ ?_
        · exact collectExecutionGroups_counted schema resolvers variables fuel parentType
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

  /-- Every deferred group and its children retain selected-cause accounting, by group-list induction. -/

  theorem collectExecutionGroups_counted (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap))
      (path : ResponsePath)
      (deferMap : DeferMap)
      : RunEnsures WorkCertified
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap) := by
    cases partitions with
    | nil => simp [collectExecutionGroups, RunEnsures, WorkCertified]
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        simp only [collectExecutionGroups, executeExecutionGroup]
        refine runEnsures_bind Certified _ _ _ ?_ ?_
        · exact executeCollectedFields_counted schema resolvers variables fuel parentType
            source groups path usages deferMap
        · intro completed hc
          refine runEnsures_bind WorkCertified _ _ _ ?_ ?_
          · exact collectExecutionGroups_counted schema resolvers variables fuel parentType
              source rest path deferMap
          · intro work hw
            exact runEnsures_pure _ _ ⟨⟨delivery_one hc, hc.2.1⟩, hw⟩
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Collected fields preserve selected-cause accounting when combined, by field-list induction. -/

  theorem executeCollectedFields_counted (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap)
      : RunEnsures Certified
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages deferMap) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil] using runEnsures_pure _ _ (pure ([] : List
          (Name × ResponseValue)))
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        simp only [executeCollectedFields_cons]
        refine runEnsures_bind Certified _ _ _ ?_ ?_
        · exact executeResponseField_counted schema resolvers variables fuel parentType source name
            fields path usages deferMap
        · intro head hh
          refine runEnsures_bind Certified _ _ _ ?_ ?_
          · exact executeCollectedFields_counted schema resolvers variables fuel parentType
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

  /-- Field execution preserves selected-cause accounting through lookup and completion cases. -/

  theorem executeResponseField_counted (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (fields : List FieldDetails) (path : ResponsePath)
      (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures Certified
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
                · refine runEnsures_bind Certified _ _ _ ?_ ?_
                  · exact completeValue_counted schema resolvers variables fuel _ _ _
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

  /-- Value completion preserves selected-cause accounting for every type, by mutual fuel induction. -/

  theorem completeValue_counted (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures Certified
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
            refine runEnsures_bind Certified _ _ _ ?_ ?_
            · exact completeValue_counted schema resolvers variables (fuel + 1) inner fields
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
                  refine runEnsures_bind Certified _ _ _ ?_ ?_
                  · exact executePlan_counted schema resolvers variables fuel runtimeType
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
                simpa only [completeValue] using completeListValueWithStream_counted
                  schema resolvers variables fuel inner fields items path usages deferMap
                  allowStream
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- The stream hook preserves unit boundary causes in both the initial prefix and tail;
  witness: ordinary completion and item-tail certificates.
  -/
  theorem completeListValueWithStream_counted (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath)
      (usages : List Nat) (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures Certified
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
      exact runEnsures_pure _ _ ⟨by simp [CauseOne], trivial, by simp [FatalCause]⟩
    · refine runEnsures_bind Certified _ _ _ ?_ ?_
      · exact completeListValue_counted schema resolvers variables fuel inner fields
          values path 0 usages deferMap
      · intro completed hc
        exact runEnsures_pure _ _ (catchNull _ completed hc)
    · rename_i usage _
      refine runEnsures_bind Certified _ _ _ ?_ ?_
      · exact completeListValue_counted schema resolvers variables fuel inner fields
          (values.take usage.initialCount) path 0 usages deferMap
      · intro initial hi
        split
        · exact runEnsures_pure _ _ (catchNull _ initial hi)
        · split
          · exact runEnsures_pure _ _ (catchNull _ initial hi)
          · refine runEnsures_bind (fun _ : Nat => True) _ _ _ (fun _ => trivial) ?_
            intro ref _
            refine runEnsures_bind ItemsCertified _ _ _ ?_ ?_
            · exact completeStreamItems_counted schema resolvers variables fuel inner
                _ _ path usage.initialCount
            · intro tail ht
              exact runEnsures_pure _ _ ⟨(catchNull _ initial hi).1,
                ⟨(catchNull _ initial hi).2.1, ht⟩, (catchNull _ initial hi).2.2⟩
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary list completion preserves selected-cause accounting, by item-list induction. -/

  theorem completeListValue_counted (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures Certified
          (completeListValue schema resolvers variables fuel itemType fields values path
            index usages deferMap) := by
    cases values with
    | nil =>
        simpa only [completeListValue] using runEnsures_pure _ _ (pure ([] : List ResponseValue))
    | cons value rest =>
        simp only [completeListValue]
        refine runEnsures_bind Certified _ _ _ ?_ ?_
        · exact completeValue_counted schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) usages deferMap false
        · intro head hh
          refine runEnsures_bind Certified _ _ _ ?_ ?_
          · exact completeListValue_counted schema resolvers variables fuel itemType fields
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

  /-- Stream tails retain a one counted failing item or recursively certified successful
  items; witness: the exact early-stop branch of completeStreamItems.
  -/
  theorem completeStreamItems_counted (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      : RunEnsures ItemsCertified
          (completeStreamItems schema resolvers variables fuel itemType fields values
            path index) := by
    cases values with
    | nil => simp [completeStreamItems, RunEnsures, ItemsCertified]
    | cons value rest =>
        simp only [completeStreamItems]
        refine runEnsures_bind Certified _ _ _ ?_ ?_
        · exact completeValue_counted schema resolvers variables fuel itemType fields
            value (path ++ [.index index]) [] [] false
        · intro head hh
          split
          · rename_i errors he
            exact runEnsures_pure _ _ ⟨delivery_one hh, trivial, trivial⟩
          · refine runEnsures_bind ItemsCertified _ _ _ ?_ ?_
            · exact completeStreamItems_counted schema resolvers variables fuel itemType
                fields rest path (index + 1)
            · intro tail ht
              exact runEnsures_pure _ _ ⟨delivery_one hh, hh.2.1, ht⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

end

/-- Every stream-entry lookup retains its task boundary and child-work certificate. -/
theorem ItemsCertified.member {items : List (TaskOutcome ResponseValue × Work)}
    (certified : ItemsCertified items) {result children}
    (member : (result, children) ∈ items)
    : OneFailure result.deliveryResult ∧ WorkCertified children := by
  induction items with
  | nil => cases member
  | cons entry rest ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst entry; exact ⟨certified.1, certified.2.1⟩
      · exact ih certified.2.2 member

/-- Declaration annotations preserve selected unit causes. -/
theorem WorkCertified.withoutDeclarations {work : Work} (certified : WorkCertified work)
    : WorkCertified work.withoutDeclarations := by
  cases work with
  | declareGroups groups tasks =>
      exact WorkCertified.withoutDeclarations (work := tasks) certified
  | _ => exact certified
termination_by work

/-- Structural navigation preserves unit causes throughout the generated work tree. -/
theorem WorkCertified.located {work address current producer owners}
    (certified : WorkCertified work)
    (located : Located work address current producer owners)
    : WorkCertified current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact certified.withoutDeclarations
  | left _ ih => exact ih.1.withoutDeclarations
  | right _ ih => exact ih.2.withoutDeclarations
  | executionGroup _ ih => exact ih.2.withoutDeclarations
  | item _ entry ih =>
      exact (ih.member (List.mem_of_getElem? entry)).2.withoutDeclarations

/-- Every failing structural task selects one primitive error. -/
theorem WorkCertified.task {work occurrence owners producer payload}
    (certified : WorkCertified work)
    (known : TaskAt work occurrence owners producer payload)
    (fails : payload.failure.isSome = true)
    : payload.failure.getD 0 = 1 := by
  cases StructuralEquivalence.taskAt_of_current known with
  | @executionGroup address groups path result children producer enclosing located =>
      have counted := (certified.located located.toCurrent).1
      cases hr : result.deliveryResult <;> simp_all [Payload.failure, OneFailure]
  | @item address node items producer enclosing index result children located entry =>
      have counted := ((certified.located located.toCurrent).member (List.mem_of_getElem? entry)).1
      cases hr : result.deliveryResult <;> simp_all [Payload.failure, OneFailure]

/-- Every root execution certifies retained failures, by collection then plan execution. -/

theorem executeRootSelectionSetCore_counted (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : RunEnsures Certified
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) := by
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind (fun _ : FieldCollection => True) _ _ _ (fun _ => trivial) ?_
  intro collection _
  exact executePlan_counted schema resolvers variables fuel parentType source collection
    [] [] []

end GraphQL.IncrementalDelivery.Correctness.BoundaryErrorCounts
