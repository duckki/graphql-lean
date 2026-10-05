import Proofs.GraphQL.IncrementalDelivery.Correctness.InitialFailureAlgebra
import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicListErrors
import Proofs.GraphQL.IncrementalDelivery.Correctness.ArgumentValidity

/-! Mixed execution's initial failures remain failures after directive erasure. -/

namespace GraphQL.IncrementalDelivery.Correctness.InitialFailures
open GraphQL.IncrementalDelivery.Execution
open Semantics
open WorkQueueSemantics (NodeRefs)

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  /-- An initial failing plan cannot become successful by executing its deferred fields.
  Witness: immediate-field preservation, ordinary append bubbling, and exact plan
  permutation. Future task outcomes and observation order need no assumptions.
  -/
  theorem executePlan_preserves_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (collection : FieldCollection)
      (valid
        : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables)
            collection.collectedFieldsMap)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures
          (fun completed =>
            BubblesPreserved
              (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                parentType source (eraseGroups collection.collectedFieldsMap))
              completed.result)
          (executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages
            (buildExecutionPlan collection.collectedFieldsMap usages) path usages
            deferMap) := by
    let plan := buildExecutionPlan collection.collectedFieldsMap usages
    have partitionValid := ArgumentValidity.buildExecutionPlan_valid variables
      collection.collectedFieldsMap usages valid
    simp only [executeExecutionPlan]
    refine runEnsures_bind
      (fun completed =>
        BubblesPreserved
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source (eraseGroups plan.collectedFieldsMap)) completed.result)
      _ _ _ ?_ ?_
    · exact executeCollectedFields_preserves_failures schema resolvers variables fuel parentType
        source plan.collectedFieldsMap partitionValid.1 path usages _
    · intro initial preserved
      have ordered := TypedResponse.basicFields_perm_withErrors schema resolvers variables fuel
        parentType source (buildExecutionPlan_erasure_perm collection.collectedFieldsMap usages).symm
      have erased : eraseGroups (executionPlanGroups plan)
          = eraseGroups plan.collectedFieldsMap
            ++ eraseGroups (plan.newCollectedFieldsMaps.flatMap Prod.snd) := by
        simp [executionPlanGroups, eraseGroups]
      rw [erased, TypedResponse.basicFields_append_result] at ordered
      have full := BubblesPreserved.of_fieldEquivalent ordered
        (preserved.appendOrdinary List.append
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType
            source (eraseGroups (plan.newCollectedFieldsMaps.flatMap Prod.snd))))
      split
      · exact runEnsures_pure _ _ full
      · refine runEnsures_bind (fun _ : Work => True) _ _ _ (fun _ => trivial) ?_
        intro tasks _
        exact runEnsures_pure _ _ full
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Initial field bubbling persists in ordinary completion of the same collected groups.
  Witness: field-list induction through the actual state sequence and result combination.
  Validity only excludes enabled stream-count rejection, not ordinary nullable errors.
  -/
  theorem executeCollectedFields_preserves_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (valid : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables) groups)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures
          (fun completed =>
            BubblesPreserved
              (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                parentType source (eraseGroups groups)) completed.result)
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages deferMap) := by
    cases groups with
    | nil =>
        simp only [executeCollectedFields_nil]
        exact runEnsures_pure _ _ (BubblesPreserved.ok _ [] 0)
    | cons head tail =>
        obtain ⟨name, selected⟩ := head
        simp only [executeCollectedFields_cons, eraseGroups, List.map_cons, eraseGroup,
          GraphQL.Execution.executeCollectedFields]
        refine runEnsures_bind
          (fun completed =>
            BubblesPreserved
              (GraphQL.Execution.executeField schema resolvers variables fuel parentType
                source name (selected.map eraseField)) completed.result) _ _ _ ?_ ?_
        · exact executeResponseField_preserves_failures schema resolvers variables fuel parentType
            source name selected (valid (name, selected) (by simp)) path usages deferMap
        · intro head preservedHead
          refine runEnsures_bind
            (fun completed => BubblesPreserved
              (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType
                source (eraseGroups tail)) completed.result) _ _ _ ?_ ?_
          · exact executeCollectedFields_preserves_failures schema resolvers variables fuel
              parentType source tail (fun group member => valid group (by simp [member]))
              path usages deferMap
          · intro tail preservedTail
            exact runEnsures_pure _ _
              (BubblesPreserved.combineCompletions List.append preservedHead preservedTail)
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Resolver/schema failures and nested initial failures persist after field erasure.
  Witness: the actual lookup/coercion/resolution branches and mixed value preservation.
  -/
  theorem executeResponseField_preserves_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (selected : List FieldDetails)
      (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures
          (fun completed =>
            BubblesPreserved
              (GraphQL.Execution.executeField schema resolvers variables fuel parentType
                source name (selected.map eraseField)) completed.result)
          (executeResponseField schema resolvers variables fuel parentType source name
            selected path usages deferMap) := by
    cases fuel with
    | zero =>
        cases selected <;> simp [executeResponseField, GraphQL.Execution.executeField,
          RunEnsures, BubblesPreserved, Completion.error, GraphQL.Execution.outOfFuel]
    | succ fuel =>
        cases selected with
        | nil =>
            simp [executeResponseField, GraphQL.Execution.executeField, RunEnsures,
              BubblesPreserved, Completion.error]
        | cons field rest =>
            cases lookup : schema.lookupField parentType field.fieldName with
            | none =>
                simp [executeResponseField, GraphQL.Execution.executeField, eraseField,
                  lookup, RunEnsures, BubblesPreserved, Completion.error]
            | some definition =>
                cases coercion
                      : coerceArgumentValues schema variables definition.arguments
                          field.arguments with
                | error =>
                    simp only [executeResponseField, GraphQL.Execution.executeField,
                      List.map_cons, eraseField, lookup, coercion]
                    apply runEnsures_pure
                    exact BubblesPreserved.refl _
                | success arguments =>
                    cases resolved
                          : resolveFieldValue resolvers parentType field.fieldName
                              arguments source with
                    | none =>
                        simp only [executeResponseField, GraphQL.Execution.executeField,
                          List.map_cons, eraseField, lookup, coercion, resolved]
                        apply runEnsures_pure
                        exact BubblesPreserved.refl _
                    | some value =>
                        simp only [executeResponseField, GraphQL.Execution.executeField,
                          List.map_cons, eraseField, lookup, coercion, resolved]
                        refine runEnsures_bind
                          (fun completed => ValueFailuresPreserved
                            (GraphQL.Execution.completeValue schema resolvers variables fuel
                              definition.outputType ((field :: rest).map eraseField) value)
                            completed.result) _ _ _ ?_ ?_
                        · exact completeValue_preserves_failures schema resolvers variables fuel
                            definition.outputType (field :: rest) value valid
                            (path ++ [.field name]) usages deferMap true
                        · intro completed preserved
                          apply runEnsures_pure
                          have mapped := preserved.1.map (fun value => [(name, value)])
                          simp only [List.map_cons, eraseField] at mapped
                          cases ordinary : GraphQL.Execution.completeValue schema resolvers
                              variables fuel definition.outputType
                              ({ fieldName := field.fieldName, arguments := field.arguments,
                                  selectionSet := SelectionSet.eraseIncrementalDirectives
                                    field.selectionSet } :: rest.map eraseField) value <;>
                            simpa [GraphQL.Execution.singleFieldResult, ordinary] using mapped
  termination_by (fuel, 3, 0, sizeOf selected)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Mixed completion cannot repair an initial bubble or an initial null after erasure.
  Witness: mutual fuel/type descent through objects, lists, and non-null wrappers, with
  argument validity preserved across merged subfields and execution-plan partitioning.
  -/
  theorem completeValue_preserves_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (fieldType : TypeRef) (selected : List FieldDetails)
      (resolved : ResolverValue ObjectRef)
      (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures
          (fun completed =>
            ValueFailuresPreserved
              (GraphQL.Execution.completeValue schema resolvers variables fuel fieldType
                (selected.map eraseField) resolved) completed.result)
          (completeValue schema resolvers variables fuel fieldType selected resolved path
            usages deferMap allowStream) := by
    cases fuel with
    | zero =>
        simp [completeValue, GraphQL.Execution.completeValue, RunEnsures,
          ValueFailuresPreserved, BubblesPreserved, Completion.error, GraphQL.Execution.outOfFuel]
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simp only [completeValue, GraphQL.Execution.completeValue]
            refine runEnsures_bind
              (fun completed => ValueFailuresPreserved
                (GraphQL.Execution.completeValue schema resolvers variables (fuel + 1) inner
                  (selected.map eraseField) resolved) completed.result) _ _ _ ?_ ?_
            · exact completeValue_preserves_failures schema resolvers variables (fuel + 1)
                inner selected resolved valid path usages deferMap allowStream
            · intro completed preserved
              exact runEnsures_pure _ _ preserved.nonNull
        | named parentType =>
            cases resolved with
            | null =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                exact runEnsures_pure _ _ (ValueFailuresPreserved.refl _)
            | scalar scalar =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                split <;> exact runEnsures_pure _ _ (ValueFailuresPreserved.refl _)
            | list data =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                exact runEnsures_pure _ _ (ValueFailuresPreserved.refl _)
            | object runtimeType ref =>
                cases applies : schema.typeIncludesObjectBool parentType runtimeType <;>
                  simp only [completeValue, GraphQL.Execution.completeValue, applies,
                    Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                · exact runEnsures_pure _ _ (ValueFailuresPreserved.refl _)
                · refine runEnsures_bind
                    (fun collection =>
                      eraseGroups collection.collectedFieldsMap
                        = GraphQL.Execution.collectSubfields schema variables runtimeType
                            (.object runtimeType ref) (selected.map eraseField)
                      ∧ GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables)
                        collection.collectedFieldsMap) _ _ _ ?_ ?_
                  · intro state
                    exact ⟨collectSubfields_erase schema variables runtimeType
                      (.object runtimeType ref) selected state,
                      ArgumentValidity.collectSubfields_valid schema variables runtimeType
                        (.object runtimeType ref) selected valid state⟩
                  · intro collection collected
                    refine runEnsures_bind
                      (fun completed => BubblesPreserved
                        (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                          runtimeType (.object runtimeType ref)
                          (GraphQL.Execution.collectSubfields schema variables runtimeType
                            (.object runtimeType ref) (selected.map eraseField)))
                        completed.result) _ _ _ ?_ ?_
                    · simpa only [collected.1] using executePlan_preserves_failures schema
                        resolvers variables fuel runtimeType (.object runtimeType ref) collection
                        collected.2 path usages deferMap
                    · intro completed preserved
                      exact runEnsures_pure _ _
                        (preserved.catchNull ResponseValue.object (fun _ => by simp))
        | list inner =>
            cases resolved with
            | null | scalar _ | object _ _ =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                exact runEnsures_pure _ _ (ValueFailuresPreserved.refl _)
            | list data =>
                simpa only [completeValue, GraphQL.Execution.completeValue]
                  using completeListValueWithStream_preserves_failures schema resolvers
                    variables fuel inner selected data valid path usages deferMap
                    allowStream
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- A failing streamed prefix also makes ordinary completion of the full list fail.
  Witness: count-argument validity, initial-list preservation, and exact ordinary
  take/drop combination. Successful initial lists need no constraint on later failures.
  -/
  theorem completeListValueWithStream_preserves_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (selected : List FieldDetails)
      (values : List (ResolverValue ObjectRef))
      (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures
          (fun completed =>
            ValueFailuresPreserved
              (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
                (GraphQL.Execution.completeValueList schema resolvers variables fuel
                  itemType (selected.map eraseField) values)) completed.result)
          (completeListValueWithStream schema resolvers variables fuel itemType selected
            values path usages deferMap allowStream) := by
    obtain ⟨usage, usageEq⟩ := ArgumentValidity.fields_getStreamUsage_ok variables selected valid
    have hook : (if allowStream then getStreamUsage variables
        (selected.head?.map FieldDetails.directives |>.getD []) else .ok none)
        = .ok (if allowStream then usage else none) := by cases allowStream <;> simp [usageEq]
    simp only [completeListValueWithStream, hook]
    cases active : (if allowStream then usage else none) with
    | none =>
        refine runEnsures_bind
          (fun completed => BubblesPreserved
            (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
              (selected.map eraseField) values) completed.result) _ _ _ ?_ ?_
        · exact completeListValue_preserves_failures schema resolvers variables fuel itemType
            selected values valid path 0 usages deferMap
        · intro completed preserved
          exact runEnsures_pure _ _
            (preserved.catchNull ResponseValue.list (fun _ => by simp))
    | some usage =>
        refine runEnsures_bind
          (fun completed => BubblesPreserved
            (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
              (selected.map eraseField) (values.take usage.initialCount)) completed.result)
          _ _ _ ?_ ?_
        · exact completeListValue_preserves_failures schema resolvers variables fuel itemType
            selected (values.take usage.initialCount) valid path 0 usages deferMap
        · intro initial preserved
          have full := preserved.appendOrdinary List.append
            (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
              (selected.map eraseField) (values.drop usage.initialCount))
          rw [← SourceReconstruction.basicList_split_result schema resolvers variables fuel
            itemType (selected.map eraseField) values usage.initialCount] at full
          split
          · exact runEnsures_pure _ _
              (full.catchNull ResponseValue.list (fun _ => by simp))
          · split
            · exact runEnsures_pure _ _
                (full.catchNull ResponseValue.list (fun _ => by simp))
            · refine runEnsures_bind (fun _ : NodeRef => True) _ _ _ (fun _ => trivial) ?_
              intro ref _
              refine runEnsures_bind
                (fun _ : List (Result ResponseValue × Work) => True) _ _ _
                (fun _ => trivial) ?_
              intro items _
              exact runEnsures_pure _ _
                (full.catchNull ResponseValue.list (fun _ => by simp))
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Initial ordinary list accumulation preserves bubbling item failures after erasure.
  Witness: list induction, mixed value preservation, and result combination; each item
  runs at its actual threaded fresh-reference supply.
  -/
  theorem completeListValue_preserves_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (selected : List FieldDetails)
      (values : List (ResolverValue ObjectRef))
      (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
      (path : ResponsePath) (index : Nat) (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures
          (fun completed =>
            BubblesPreserved
              (GraphQL.Execution.completeValueList schema resolvers variables fuel
                itemType (selected.map eraseField) values) completed.result)
          (completeListValue schema resolvers variables fuel itemType selected values path
            index usages deferMap) := by
    cases values with
    | nil =>
        simp only [completeListValue, GraphQL.Execution.completeValueList]
        exact runEnsures_pure _ _ (BubblesPreserved.refl _)
    | cons value rest =>
        simp only [completeListValue, GraphQL.Execution.completeValueList]
        refine runEnsures_bind
          (fun completed => ValueFailuresPreserved
            (GraphQL.Execution.completeValue schema resolvers variables fuel itemType
              (selected.map eraseField) value) completed.result) _ _ _ ?_ ?_
        · exact completeValue_preserves_failures schema resolvers variables fuel itemType selected
            value valid (path ++ [.index index]) usages deferMap false
        · intro head preservedHead
          refine runEnsures_bind
            (fun completed => BubblesPreserved
              (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
                (selected.map eraseField) rest) completed.result) _ _ _ ?_ ?_
          · exact completeListValue_preserves_failures schema resolvers variables fuel itemType
              selected rest valid path (index + 1) usages deferMap
          · intro tail preservedTail
            exact runEnsures_pure _ _
              (BubblesPreserved.combineCompletions List.cons preservedHead.1 preservedTail)
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

-----------------------------------------------------------------------------------------
-- Root execution and retained stream failures
-----------------------------------------------------------------------------------------

/-- Full ordinary root execution cannot repair an initially bubbling incremental root.
Witness: root collection preserves argument validity and erases to the ordinary groups;
the mixed execution-plan theorem then applies at the actual fresh-reference supply.
-/
theorem executeRoot_preserves_failures (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection)
    (valid : SelectionSet.hasValidIncrementalArguments variables selections = true)
    : RunEnsures
        (fun completed =>
          BubblesPreserved
            (GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
              parentType source (SelectionSet.eraseIncrementalDirectives selections))
            completed.result)
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) := by
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind
    (fun collection =>
      eraseGroups collection.collectedFieldsMap
        = GraphQL.Execution.collectFields schema variables parentType source
            (SelectionSet.eraseIncrementalDirectives selections)
      ∧ GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables)
        collection.collectedFieldsMap) _ _ _ ?_ ?_
  · intro state
    exact ⟨collectFields_erase schema variables parentType source selections none state,
      ArgumentValidity.collectFields_valid schema variables parentType source selections
        valid none state⟩
  · intro collection collected
    simpa only [GraphQL.Execution.executeRootSelectionSet, collected.1]
      using executePlan_preserves_failures schema resolvers variables fuel parentType
        source collection collected.2 [] [] []

/-- A retained failed mixed stream item forces ordinary completion of its full list to
bubble. Witness: input-list induction follows the actual threaded state until its retained
error; mixed value preservation and ordinary result combination propagate that failure.
Deferred child failures may add errors later, so equality of error counts is not claimed.
-/
theorem completeStreamItems_failure_bubbles (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (selected : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (index state errors : Nat) (children : Work)
    (failed
      : (.error errors, children)
        ∈ ((completeStreamItems schema resolvers variables fuel itemType selected values
              path index).run
            state).1)
    : ∃ count,
        GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          (selected.map eraseField) values
        = .error count := by
  induction values generalizing index state with
  | nil => simp [completeStreamItems] at failed
  | cons value rest ih =>
      let action := completeValue schema resolvers variables fuel itemType selected value
        (path ++ [.index index]) [] [] false
      let head := (action.run state).1
      let next := (action.run state).2
      have preserved := (completeValue_preserves_failures schema resolvers variables fuel
        itemType selected value valid (path ++ [.index index]) [] [] false state).1
      cases outcome : head.result with
      | error count =>
          obtain ⟨ordinaryCount, ordinaryFailed⟩ := preserved _ outcome
          cases tail : GraphQL.Execution.completeValueList schema resolvers variables fuel
              itemType (selected.map eraseField) rest <;>
            simp [GraphQL.Execution.completeValueList, Result.combine, ordinaryFailed, tail]
      | ok pair =>
          have completed := outcome
          dsimp only [head, action] at completed
          have tailFailed : (.error errors, children)
              ∈ ((completeStreamItems schema resolvers variables fuel itemType selected rest
                    path (index + 1)).run next).1 := by
            simpa [completeStreamItems, completed, next, action] using failed
          obtain ⟨ordinaryCount, ordinaryFailed⟩ := ih (index + 1) next tailFailed
          cases item : GraphQL.Execution.completeValue schema resolvers variables fuel
              itemType (selected.map eraseField) value <;>
            simp [GraphQL.Execution.completeValueList, Result.combine, item, ordinaryFailed]

end GraphQL.IncrementalDelivery.Correctness.InitialFailures
