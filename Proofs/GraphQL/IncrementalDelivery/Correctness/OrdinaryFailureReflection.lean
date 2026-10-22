import Proofs.GraphQL.IncrementalDelivery.Correctness.OrdinaryFailureAlgebra
import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicListErrors
import Proofs.GraphQL.IncrementalDelivery.Correctness.ArgumentValidity

/-! Mixed ordinary failures are initial failures or actual retained descendant tasks. -/

namespace GraphQL.IncrementalDelivery.Correctness.OrdinaryFailures
open GraphQL.IncrementalDelivery.Execution
open Semantics
open WorkQueueSemantics (NodeRefs)

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  /-- Ordinary plan bubbling has an initial bubble or a real retained failed task.
  Witness: ordinary partition permutation and mixed immediate/deferred comparison;
  deferred failures are retained even when their partial initial outcomes do not bubble.
  -/
  theorem executePlan_explains_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (collection : FieldCollection)
      (valid
        : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables)
            collection.collectedFieldsMap)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures
          (fun completed =>
            BubblesExplained path
              (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                parentType source (eraseGroups collection.collectedFieldsMap)) completed)
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
        BubblesExplained path
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source (eraseGroups plan.collectedFieldsMap)) completed)
      _ _ _ ?_ ?_
    · exact executeCollectedFields_explains_failures schema resolvers variables fuel parentType
        source plan.collectedFieldsMap partitionValid.1 path usages _
    · intro initial explained
      have ordered := TypedResponse.basicFields_perm_withErrors schema resolvers variables fuel
        parentType source (buildExecutionPlan_erasure_perm collection.collectedFieldsMap usages).symm
      have erased : eraseGroups (executionPlanGroups plan)
          = eraseGroups plan.collectedFieldsMap
            ++ eraseGroups (plan.newCollectedFieldsMaps.flatMap Prod.snd) := by
        simp [executionPlanGroups, eraseGroups]
      rw [erased, TypedResponse.basicFields_append_result] at ordered
      cases initialResult : initial.result with
      | error count =>
          exact runEnsures_pure _ _ (fun _ _ => Or.inl ⟨count, initialResult⟩)
      | ok pair =>
          refine runEnsures_bind
            (fun tasks =>
              ∀ errors,
                GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                    parentType source
                    (eraseGroups (plan.newCollectedFieldsMaps.flatMap Prod.snd))
                  = .error errors
                → FailedBelow path tasks) _ _ _ ?_ ?_
          · exact collectExecutionGroups_explains_failures schema resolvers variables fuel
              parentType source plan.newCollectedFieldsMaps partitionValid.2 path _
          · intro tasks deferred
            apply runEnsures_pure
            apply BubblesExplained.of_fieldEquivalent ordered
            intro errors failed
            cases immediateResult
                  : GraphQL.Execution.executeCollectedFields schema resolvers variables
                      fuel parentType source (eraseGroups plan.collectedFieldsMap) with
            | error count =>
                simpa only [initialResult]
                  using explained.retain_right tasks count immediateResult
            | ok head =>
                cases deferredResult
                      : GraphQL.Execution.executeCollectedFields schema resolvers
                          variables fuel parentType source
                          (eraseGroups
                            (plan.newCollectedFieldsMaps.flatMap Prod.snd)) with
                | error count =>
                    exact Or.inr ((deferred count deferredResult).combine_right initial.work)
                | ok tail =>
                    simp [Result.combine, immediateResult, deferredResult] at failed
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary deferred-partition bubbling identifies actual retained failed work.
  Witness: partition-list descent through the actual fresh-reference sequence. A partial
  group's descendant failure stays beneath its retained execution-group task.
  -/
  theorem collectExecutionGroups_explains_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (NodeRefs × CollectedFieldsMap))
      (valid
        : ∀ partition ∈ partitions,
            GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables) partition.2)
      (path : ResponsePath) (deferMap : DeferMap)
      : RunEnsures
          (fun work =>
            ∀ errors,
              GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                  parentType source (eraseGroups (partitions.flatMap Prod.snd))
                = .error errors
              → FailedBelow path work)
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap) := by
    cases partitions with
    | nil =>
        simp [collectExecutionGroups, RunEnsures, eraseGroups,
          GraphQL.Execution.executeCollectedFields]
    | cons partition rest =>
        obtain ⟨usages, fields⟩ := partition
        simp only [collectExecutionGroups, executeExecutionGroup]
        refine runEnsures_bind
          (fun completed => BubblesExplained path
            (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source (eraseGroups fields)) completed) _ _ _ ?_ ?_
        · exact executeCollectedFields_explains_failures schema resolvers variables fuel
            parentType source fields (valid (usages, fields) (by simp)) path usages deferMap
        · intro initial explained
          refine runEnsures_bind
            (fun work => ∀ errors,
              GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                parentType source (eraseGroups (rest.flatMap Prod.snd)) = .error errors
                → FailedBelow path work) _ _ _ ?_ ?_
          · exact collectExecutionGroups_explains_failures schema resolvers variables fuel
              parentType source rest (fun partition member => valid partition (by simp [member]))
              path deferMap
          · intro tail deferred
            apply runEnsures_pure
            intro errors failed
            simp only [List.flatMap_cons, eraseGroups, List.map_append,
              TypedResponse.basicFields_append_result] at failed
            cases first
                  : GraphQL.Execution.executeCollectedFields schema resolvers variables
                      fuel parentType source (eraseGroups fields) with
            | error count =>
                rcases explained count first with already | retained
                · obtain ⟨count, bubbles⟩ := already
                  exact (by
                    simpa only [Completion.outcome, bubbles]
                      using (FailedBelow.executionGroup_error
                              (usages.filterMap (lookupDeferredFragment? deferMap)) path
                              count initial.work).combine_left
                        tail)
                · exact (retained.executionGroup_child _ path initial.outcome).combine_left tail
            | ok head =>
                cases last
                      : GraphQL.Execution.executeCollectedFields schema resolvers
                          variables fuel parentType source
                          (eraseGroups (rest.flatMap Prod.snd)) with
                | error count => exact (deferred count last).combine_right _
                | ok suffix =>
                    simp [eraseGroups] at first last
                    simp [Result.combine, first, last] at failed
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Ordinary field bubbling is initial bubbling or retained descendant failure.
  Witness: group-list descent and completion combination, including cancelled child work
  when the combined initial result already bubbles.
  -/
  theorem executeCollectedFields_explains_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (valid : GroupsSatisfy (ArgumentValidity.FieldArgumentsValid variables) groups)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures
          (fun completed =>
            BubblesExplained path
              (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                parentType source (eraseGroups groups)) completed)
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages deferMap) := by
    cases groups with
    | nil =>
        simp only [executeCollectedFields_nil]
        apply runEnsures_pure
        apply BubblesExplained.of_result_eq
        simp [Completion.pure, eraseGroups, GraphQL.Execution.executeCollectedFields]
    | cons head tail =>
        obtain ⟨name, selected⟩ := head
        simp only [executeCollectedFields_cons, eraseGroups, List.map_cons, eraseGroup,
          GraphQL.Execution.executeCollectedFields]
        refine runEnsures_bind
          (fun completed =>
            BubblesExplained path
              (GraphQL.Execution.executeField schema resolvers variables fuel parentType
                source name (selected.map eraseField)) completed) _ _ _ ?_ ?_
        · exact executeResponseField_explains_failures schema resolvers variables fuel parentType
            source name selected (valid (name, selected) (by simp)) path usages deferMap
        · intro head explainedHead
          refine runEnsures_bind
            (fun completed => BubblesExplained path
              (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType
                source (eraseGroups tail)) completed) _ _ _ ?_ ?_
          · exact executeCollectedFields_explains_failures schema resolvers variables fuel
              parentType source tail (fun group member => valid group (by simp [member]))
              path usages deferMap
          · intro tail explainedTail
            exact runEnsures_pure _ _
              (BubblesExplained.combine List.append explainedHead explainedTail)
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Ordinary field failures have an initial failure or retained nested failure.
  Witness: exact lookup/coercion/resolution branches; mixed value failure evidence is
  mapped into the response field and its attachment bound weakens to the parent.
  -/
  theorem executeResponseField_explains_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (selected : List FieldDetails)
      (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures
          (fun completed =>
            BubblesExplained path
              (GraphQL.Execution.executeField schema resolvers variables fuel parentType
                source name (selected.map eraseField)) completed)
          (executeResponseField schema resolvers variables fuel parentType source name
            selected path usages deferMap) := by
    cases fuel with
    | zero =>
        cases selected <;> simp [executeResponseField, GraphQL.Execution.executeField,
          RunEnsures, BubblesExplained, Completion.error, GraphQL.Execution.outOfFuel]
    | succ fuel =>
        cases selected with
        | nil =>
            simp [executeResponseField, GraphQL.Execution.executeField, RunEnsures,
              BubblesExplained, Completion.error]
        | cons field rest =>
            cases lookup : schema.lookupField parentType field.fieldName with
            | none =>
                simp [executeResponseField, GraphQL.Execution.executeField, eraseField,
                  lookup, RunEnsures, BubblesExplained, Completion.error]
            | some definition =>
                cases coercion
                      : coerceArgumentValues schema variables definition.arguments
                          field.arguments with
                | error =>
                    simp only [executeResponseField, GraphQL.Execution.executeField,
                      List.map_cons, eraseField, lookup, coercion]
                    apply runEnsures_pure
                    apply BubblesExplained.of_result_eq
                    rfl
                | success arguments =>
                    cases resolved
                          : resolveFieldValue resolvers parentType field.fieldName
                              arguments source with
                    | none =>
                        simp only [executeResponseField, GraphQL.Execution.executeField,
                          List.map_cons, eraseField, lookup, coercion, resolved]
                        apply runEnsures_pure
                        apply BubblesExplained.of_result_eq
                        rfl
                    | some value =>
                        simp only [executeResponseField, GraphQL.Execution.executeField,
                          List.map_cons, eraseField, lookup, coercion, resolved]
                        refine runEnsures_bind
                          (fun completed => ValueFailuresExplained (path ++ [.field name])
                            (GraphQL.Execution.completeValue schema resolvers variables fuel
                              definition.outputType ((field :: rest).map eraseField) value)
                            completed) _ _ _ ?_ ?_
                        · exact completeValue_explains_failures schema resolvers variables fuel
                            definition.outputType (field :: rest) value valid
                            (path ++ [.field name]) usages deferMap true
                        · intro completed explained
                          apply runEnsures_pure
                          have mapped := BubblesExplained.at_ancestor
                            (explained.1.map (fun value => [(name, value)]))
                            (ancestor := path) ⟨[.field name], rfl⟩
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

  /-- Ordinary mixed value bubbling/null has an initial counterpart or a failed task.
  Witness: mutual descent through actual object plans, list streams, and non-null catches.
  Argument validity excludes only the modeled stream-count rejection branch.
  -/
  theorem completeValue_explains_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (fieldType : TypeRef) (selected : List FieldDetails)
      (resolved : ResolverValue ObjectRef)
      (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures
          (fun completed =>
            ValueFailuresExplained path
              (GraphQL.Execution.completeValue schema resolvers variables fuel fieldType
                (selected.map eraseField) resolved) completed)
          (completeValue schema resolvers variables fuel fieldType selected resolved path
            usages deferMap allowStream) := by
    cases fuel with
    | zero =>
        simp [completeValue, GraphQL.Execution.completeValue, RunEnsures,
          ValueFailuresExplained, BubblesExplained, Completion.error, GraphQL.Execution.outOfFuel]
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simp only [completeValue, GraphQL.Execution.completeValue]
            refine runEnsures_bind
              (fun completed => ValueFailuresExplained path
                (GraphQL.Execution.completeValue schema resolvers variables (fuel + 1) inner
                  (selected.map eraseField) resolved) completed) _ _ _ ?_ ?_
            · exact completeValue_explains_failures schema resolvers variables (fuel + 1)
                inner selected resolved valid path usages deferMap allowStream
            · intro completed explained
              exact runEnsures_pure _ _ explained.nonNull
        | named parentType =>
            cases resolved with
            | null =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                apply runEnsures_pure
                apply ValueFailuresExplained.of_result_eq
                rfl
            | scalar scalar =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                split <;> apply runEnsures_pure <;>
                  apply ValueFailuresExplained.of_result_eq <;> rfl
            | list data =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                apply runEnsures_pure
                apply ValueFailuresExplained.of_result_eq
                rfl
            | object runtimeType ref =>
                cases applies : schema.typeIncludesObjectBool parentType runtimeType <;>
                  simp only [completeValue, GraphQL.Execution.completeValue, applies,
                    Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                · apply runEnsures_pure
                  apply ValueFailuresExplained.of_result_eq
                  rfl
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
                      (fun completed => BubblesExplained path
                        (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                          runtimeType (.object runtimeType ref)
                          (GraphQL.Execution.collectSubfields schema variables runtimeType
                            (.object runtimeType ref) (selected.map eraseField)))
                        completed) _ _ _ ?_ ?_
                    · simpa only [collected.1] using executePlan_explains_failures schema
                        resolvers variables fuel runtimeType (.object runtimeType ref) collection
                        collected.2 path usages deferMap
                    · intro completed explained
                      exact runEnsures_pure _ _
                        (explained.catchNull ResponseValue.object (fun _ => by simp))
        | list inner =>
            cases resolved with
            | null | scalar _ | object _ _ =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                apply runEnsures_pure
                apply ValueFailuresExplained.of_result_eq
                rfl
            | list data =>
                simpa only [completeValue, GraphQL.Execution.completeValue]
                  using completeListValueWithStream_explains_failures schema resolvers
                    variables fuel inner selected data valid path usages deferMap
                    allowStream
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary list bubbling is explained by its initial prefix or retained streamed tail.
  Witness: exact take/drop result combination, mixed prefix comparison, and retained
  item/child evidence. Exhausted boundaries require no hypothetical item failure.
  -/
  theorem completeListValueWithStream_explains_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (selected : List FieldDetails)
      (values : List (ResolverValue ObjectRef))
      (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures
          (fun completed =>
            ValueFailuresExplained path
              (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
                (GraphQL.Execution.completeValueList schema resolvers variables fuel
                  itemType (selected.map eraseField) values)) completed)
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
          (fun completed => BubblesExplained path
            (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
              (selected.map eraseField) values) completed) _ _ _ ?_ ?_
        · exact completeListValue_explains_failures schema resolvers variables fuel itemType
            selected values valid path 0 usages deferMap
        · intro completed explained
          exact runEnsures_pure _ _
            (explained.catchNull ResponseValue.list (fun _ => by simp))
    | some usage =>
        refine runEnsures_bind
          (fun completed => BubblesExplained path
            (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
              (selected.map eraseField) (values.take usage.initialCount)) completed)
          _ _ _ ?_ ?_
        · exact completeListValue_explains_failures schema resolvers variables fuel itemType
            selected (values.take usage.initialCount) valid path 0 usages deferMap
        · intro initial explained
          cases initialResult : initial.result with
          | error count =>
              apply runEnsures_pure
              apply BubblesExplained.catchNull ResponseValue.list (fun _ => by simp)
              exact (fun _ _ => Or.inl ⟨count, initialResult⟩ : BubblesExplained path
                (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
                  (selected.map eraseField) values) initial)
          | ok pair =>
              simp only
              split
              · rename_i exhausted
                have remaining : values.drop usage.initialCount = [] :=
                  List.drop_eq_nil_iff.mpr (by omega)
                have same := SourceReconstruction.basicList_split_result schema resolvers
                  variables fuel itemType (selected.map eraseField) values usage.initialCount
                rw [remaining] at same
                simp only [GraphQL.Execution.completeValueList] at same
                have full : GraphQL.Execution.completeValueList schema resolvers variables fuel
                    itemType (selected.map eraseField) values
                    = GraphQL.Execution.completeValueList schema resolvers variables fuel
                      itemType (selected.map eraseField) (values.take usage.initialCount) := by
                  rw [same]
                  cases GraphQL.Execution.completeValueList schema resolvers variables fuel
                    itemType (selected.map eraseField) (values.take usage.initialCount) <;>
                    simp [Result.combine]
                rw [full]
                exact runEnsures_pure _ _
                  (explained.catchNull ResponseValue.list (fun _ => by simp))
              · refine runEnsures_bind (fun _ : NodeRef => True) _ _ _ (fun _ => trivial)
                  ?_
                intro ref _
                let streamFields := selected.map (fun field => { field with deferUsage := none })
                have streamValid : ∀ field ∈ streamFields,
                    ArgumentValidity.FieldArgumentsValid variables field := by
                  intro field member
                  change field ∈ selected.map (fun original =>
                    { original with deferUsage := none }) at member
                  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
                  rw [← same]
                  exact valid original originalMember
                have erasure : streamFields.map eraseField = selected.map eraseField := by
                  simp [streamFields, List.map_map, eraseField]
                refine runEnsures_bind
                  (fun items =>
                    ∀ errors,
                      GraphQL.Execution.completeValueList schema resolvers variables fuel
                          itemType (selected.map eraseField)
                          (values.drop usage.initialCount)
                        = .error errors
                      → ItemsHaveFailure path items) _ _ _ ?_ ?_
                · simpa only [erasure] using completeStreamItems_explains_failures schema
                    resolvers variables fuel itemType streamFields
                    (values.drop usage.initialCount) streamValid path usage.initialCount
                · intro items deferred
                  apply runEnsures_pure
                  let node : DeliveryNode := { ref := ref, path := path, label := usage.label }
                  have full : BubblesExplained path
                      (GraphQL.Execution.completeValueList schema resolvers variables fuel
                        itemType (selected.map eraseField) values)
                      { initial with work := .combine initial.work (.stream node items) } := by
                    intro errors failed
                    rw [SourceReconstruction.basicList_split_result schema resolvers variables
                      fuel itemType (selected.map eraseField) values usage.initialCount] at failed
                    cases first
                          : GraphQL.Execution.completeValueList schema resolvers variables
                              fuel itemType (selected.map eraseField)
                              (values.take usage.initialCount) with
                    | error count =>
                        exact explained.retain_right (.stream node items) count first
                    | ok head =>
                        cases last
                              : GraphQL.Execution.completeValueList schema resolvers
                                  variables fuel itemType (selected.map eraseField)
                                  (values.drop usage.initialCount) with
                        | error count =>
                            exact Or.inr
                              (FailedBelow.combine_right
                                ((deferred count last).in_stream node
                                  ⟨[], by simp [node]⟩)
                                initial.work)
                        | ok tail => simp [Result.combine, first, last] at failed
                  simpa [Completion.catchNull, initialResult, node]
                    using full.catchNull ResponseValue.list (fun _ => by simp)
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary initial-list bubbling has an initial bubble or a retained child failure.
  Witness: actual item state sequence, mixed value comparison, and completion combination.
  -/
  theorem completeListValue_explains_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (selected : List FieldDetails)
      (values : List (ResolverValue ObjectRef))
      (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
      (path : ResponsePath) (index : Nat) (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures
          (fun completed =>
            BubblesExplained path
              (GraphQL.Execution.completeValueList schema resolvers variables fuel
                itemType (selected.map eraseField) values) completed)
          (completeListValue schema resolvers variables fuel itemType selected values path
            index usages deferMap) := by
    cases values with
    | nil =>
        simp only [completeListValue, GraphQL.Execution.completeValueList]
        apply runEnsures_pure
        apply BubblesExplained.of_result_eq
        rfl
    | cons value rest =>
        simp only [completeListValue, GraphQL.Execution.completeValueList]
        refine runEnsures_bind
          (fun completed => ValueFailuresExplained (path ++ [.index index])
            (GraphQL.Execution.completeValue schema resolvers variables fuel itemType
              (selected.map eraseField) value) completed) _ _ _ ?_ ?_
        · exact completeValue_explains_failures schema resolvers variables fuel itemType selected
            value valid (path ++ [.index index]) usages deferMap false
        · intro head explainedHead
          refine runEnsures_bind
            (fun completed => BubblesExplained path
              (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
                (selected.map eraseField) rest) completed) _ _ _ ?_ ?_
          · exact completeListValue_explains_failures schema resolvers variables fuel itemType
              selected rest valid path (index + 1) usages deferMap
          · intro tail explainedTail
            exact runEnsures_pure _ _ (BubblesExplained.combine List.cons
              (explainedHead.1.at_ancestor ⟨[.index index], rfl⟩) explainedTail)
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Ordinary streamed-tail bubbling identifies a failed retained item or its child work.
  Witness: short-circuit item-list descent and mixed value failure reflection; an earlier
  initial item bubble itself suffices even if ordinary bubbling occurs in a later item.
  -/
  theorem completeStreamItems_explains_failures (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (selected : List FieldDetails)
      (values : List (ResolverValue ObjectRef))
      (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
      (path : ResponsePath) (index : Nat)
      : RunEnsures
          (fun items =>
            ∀ errors,
              GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
                  (selected.map eraseField) values
                = .error errors
              → ItemsHaveFailure path items)
          (completeStreamItems schema resolvers variables fuel itemType selected values
            path index) := by
    cases values with
    | nil => simp [completeStreamItems, RunEnsures, GraphQL.Execution.completeValueList]
    | cons value rest =>
        simp only [completeStreamItems]
        refine runEnsures_bind
          (fun completed => ValueFailuresExplained (path ++ [.index index])
            (GraphQL.Execution.completeValue schema resolvers variables fuel itemType
              (selected.map eraseField) value) completed) _ _ _ ?_ ?_
        · exact completeValue_explains_failures schema resolvers variables fuel itemType
            selected value valid (path ++ [.index index]) [] [] false
        · intro initial explained
          cases initialResult : initial.result with
          | error count =>
              exact runEnsures_pure _ _
                (fun _ _ =>
                  ⟨initial.outcome, .empty, by simp, Or.inl ⟨count, initialResult⟩⟩)
          | ok pair =>
              refine runEnsures_bind
                (fun items =>
                  ∀ errors,
                    GraphQL.Execution.completeValueList schema resolvers variables fuel
                        itemType (selected.map eraseField) rest
                      = .error errors
                    → ItemsHaveFailure path items) _ _ _ ?_ ?_
              · exact completeStreamItems_explains_failures schema resolvers variables fuel
                  itemType selected rest valid path (index + 1)
              · intro tail deferred
                apply runEnsures_pure
                intro errors failed
                cases first
                      : GraphQL.Execution.completeValue schema resolvers variables fuel
                          itemType (selected.map eraseField) value with
                | error count =>
                    rcases explained.1 count first with already | retained
                    · obtain ⟨count, impossible⟩ := already
                      simp [initialResult] at impossible
                    · exact ⟨initial.outcome, initial.work, by simp,
                        Or.inr (retained.at_ancestor ⟨[.index index], rfl⟩)⟩
                | ok head =>
                    cases last
                          : GraphQL.Execution.completeValueList schema resolvers variables
                              fuel itemType (selected.map eraseField) rest with
                    | error count => exact (deferred count last).cons _
                    | ok suffix =>
                        simp [GraphQL.Execution.completeValueList, Result.combine, first, last]
                          at failed
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

-----------------------------------------------------------------------------------------
-- Root comparison and the ordinary-null coverage branch
-----------------------------------------------------------------------------------------

/-- Ordinary root bubbling is initial bubbling or retained mixed descendant failure.
Witness: collection erasure and argument preservation, followed by plan reflection at
the actual fresh-reference supply. The statement does not prescribe an observation.
-/
theorem executeRoot_explains_failures (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection)
    (valid : SelectionSet.hasValidIncrementalArguments variables selections = true)
    : RunEnsures
        (fun completed =>
          BubblesExplained []
            (GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
              parentType source (SelectionSet.eraseIncrementalDirectives selections))
            completed)
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
      using executePlan_explains_failures schema resolvers variables fuel parentType
        source collection collected.2 [] [] []

/-- Arbitrary mixed execution covers an ordinary null root caused by bubbling.
Witness: the initial response is already null, or root reflection supplies an actual
failed descendant task and the null-ancestor coverage branch. No initial-error or
schedule assumption is needed for this pure comparison certificate.
-/
theorem preparedResponseCovers_bubblingRoot (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (valid : SelectionSet.hasValidIncrementalArguments variables selections = true)
    (state errors : Nat)
    (bubbles
      : GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
          parentType source (SelectionSet.eraseIncrementalDirectives selections)
        = .error errors)
    (containers : Bool)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel
            parentType source selections).run
          state).1
      PreparedResponseCovers .null (selectionSetResultToResponse completed.result)
        completed.work containers := by
  rcases executeRoot_explains_failures schema resolvers variables fuel parentType source
      selections valid state errors bubbles with initialFailed | retained
  · obtain ⟨count, initialFailed⟩ := initialFailed
    dsimp only
    rw [initialFailed]
    intro path member
    simp only [ResponsePositions.value, List.mem_singleton] at member
    subst path
    exact Or.inl (List.mem_append_left _ (by simp [selectionSetResultToResponse,
      ResponsePositions.value]))
  · obtain ⟨occurrence, owners, producer, payload, known, fails, below⟩ := retained
    exact preparedResponseCovers_null_of_failedTask known fails _ containers

end GraphQL.IncrementalDelivery.Correctness.OrdinaryFailures
