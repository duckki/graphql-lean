import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.CacheInvariants

/-!
Execution invariants for the source-caching ungrouped executor.

Completion and selection visits preserve cache readiness and absorption.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem resultValueOrNull_cacheReady_of_ok {ObjectRef : Type}
    (result : Result (FieldCacheValue ObjectRef))
    : (∀ value errors, result = .ok (value, errors) -> FieldCacheMergeReady value)
      -> FieldCacheMergeReady (resultValueOrNull result) := by
  intro hok
  cases result with
  | error errors =>
      simp [resultValueOrNull]
      exact FieldCacheMergeReady.null
  | ok result =>
      rcases result with ⟨value, errors⟩
      simpa [resultValueOrNull] using hok value errors rfl

theorem resultValueOrNull_outOfFuel_cacheReady {ObjectRef : Type}
    : FieldCacheMergeReady
        (resultValueOrNull (outOfFuel : Result (FieldCacheValue ObjectRef))) := by
  simp [outOfFuel, resultValueOrNull]
  exact FieldCacheMergeReady.null

theorem resultValueOrNull_handleFieldError_cacheReady {ObjectRef : Type}
    (fieldType : TypeRef)
    : FieldCacheMergeReady
        (resultValueOrNull
          (handleFieldError fieldType : Result (FieldCacheValue ObjectRef))) := by
  cases fieldType <;>
    simp [handleFieldError, resultValueOrNull] <;>
    exact FieldCacheMergeReady.null

theorem resultValueOrNull_nonNullCompletion_cacheReady {ObjectRef : Type}
    (completed : Result (FieldCacheValue ObjectRef))
    : FieldCacheMergeReady (resultValueOrNull completed)
      -> FieldCacheMergeReady (resultValueOrNull (nonNullCompletion completed)) := by
  intro hready
  cases completed with
  | error errors =>
      simp [resultValueOrNull, nonNullCompletion]
      exact FieldCacheMergeReady.null
  | ok result =>
      rcases result with ⟨response, errors⟩
      cases response <;>
        simp [resultValueOrNull, nonNullCompletion] at hready ⊢
      · exact FieldCacheMergeReady.null
      · exact hready
      · exact hready
      · exact hready

theorem resultValueOrNull_catchVisitBubbleAsNull_cacheReady {ObjectRef : Type}
    (value : FieldCacheValue ObjectRef) (status : VisitStatus)
    : FieldCacheMergeReady value
      -> FieldCacheMergeReady
          (resultValueOrNull (catchVisitBubbleAsNull value status)) := by
  intro hvalue
  cases status with
  | error errors =>
      simp [catchVisitBubbleAsNull, resultValueOrNull]
      exact FieldCacheMergeReady.null
  | ok result =>
      rcases result with ⟨u, errors⟩
      simpa [catchVisitBubbleAsNull, resultValueOrNull] using hvalue

theorem resultValueOrNull_catchBubbleAsNull_cacheReady {ObjectRef α : Type}
    (wrap : α -> FieldCacheValue ObjectRef) (completed : Result α)
    : (∀ value errors,
        completed = .ok (value, errors) -> FieldCacheMergeReady (wrap value))
      -> FieldCacheMergeReady (resultValueOrNull (catchBubbleAsNull wrap completed)) := by
  intro hok
  cases completed with
  | error errors =>
      simp [catchBubbleAsNull, resultValueOrNull]
      exact FieldCacheMergeReady.null
  | ok result =>
      rcases result with ⟨value, errors⟩
      simpa [catchBubbleAsNull, resultValueOrNull] using hok value errors rfl

theorem mergeResponseFieldResult_cacheReady_and_shape {ObjectRef : Type}
    (source : ResolverValue ObjectRef)
    (responseName : Name) (fieldResult : Result (FieldCacheValue ObjectRef))
    (fields : List (Name × FieldCacheValue ObjectRef))
    : FieldCacheMergeReady (.object source fields)
      -> FieldCacheMergeReady (resultValueOrNull fieldResult)
      -> FieldCacheMergeReady
            (mergeResponseFieldResult responseName fieldResult
              (.object source fields)).value
          ∧ FieldCacheAbsorptionShape (.object source fields)
              (mergeResponseFieldResult responseName fieldResult
                (.object source fields)).value := by
  intro hfields hincoming
  have hshape :=
    FieldCacheFieldsAbsorptionShape.mergeField_of_ready source responseName
      (resultValueOrNull fieldResult) fields hfields hincoming
  have hready := hshape.output_ready
  simpa [mergeResponseFieldResult, mergeResponseFieldIntoObject] using
    And.intro hready (FieldCacheAbsorptionShape.object hshape)

theorem lookupField?_some_cacheReady {ObjectRef : Type}
    (source : ResolverValue ObjectRef)
    (responseName : Name) (fields : List (Name × FieldCacheValue ObjectRef))
    (response : FieldCacheValue ObjectRef)
    : FieldCacheMergeReady (.object source fields)
      -> lookupField? responseName fields = some response
      -> FieldCacheMergeReady response := by
  intro hready hlookup
  induction fields with
  | nil =>
      simp [lookupField?] at hlookup
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, fieldResponse⟩
      by_cases h : fieldResponseName == responseName
      · simp [lookupField?, h] at hlookup
        subst response
        exact
          FieldCacheMergeReady.object_field source
            ((fieldResponseName, fieldResponse) :: rest) fieldResponseName
            fieldResponse hready (by simp)
      · have hrestReady : FieldCacheMergeReady (.object source rest) := by
          apply FieldCacheMergeReady.object
          · exact (FieldCacheMergeReady.object_keysNodup source
                    ((fieldResponseName, fieldResponse) :: rest) hready).tail
          · intro restName restResponse hmem
            exact
              FieldCacheMergeReady.object_field source
                ((fieldResponseName, fieldResponse) :: rest) restName restResponse
                hready (by simp [hmem])
        simp [lookupField?, h] at hlookup
        exact ih hrestReady hlookup

theorem executeField_resultValueOrNull_cacheReady_of_completeValue
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source : ResolverValue ObjectRef)
    (previous? : Option (FieldCacheValue ObjectRef)) (field : ExecutableField)
    (hcomplete
      : ∀ fieldType selectionSet value previous?,
          (∀ previous, previous? = some previous -> FieldCacheMergeReady previous)
          -> FieldCacheMergeReady
              (resultValueOrNull
                (completeValue schema resolvers variableValues completionFuel
                  fieldType selectionSet value previous?)))
    : (∀ previous, previous? = some previous -> FieldCacheMergeReady previous)
      -> FieldCacheMergeReady
          (resultValueOrNull
            (executeField schema resolvers variableValues completionFuel source
              previous? field)) := by
  intro hprevious
  unfold executeField
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      simp [resultValueOrNull]
      exact FieldCacheMergeReady.null
  | some fieldDefinition =>
      cases previous? with
      | none =>
          cases hresolve
                : resolveFieldValue schema resolvers variableValues fieldDefinition
                    field.parentType field.fieldName field.arguments source with
          | none =>
              simpa [hlookup, hresolve] using
                (resultValueOrNull_handleFieldError_cacheReady
                  (ObjectRef := ObjectRef) fieldDefinition.outputType)
          | some resolved =>
              simpa [hlookup, hresolve] using
                hcomplete fieldDefinition.outputType field.selectionSet resolved none
                  (by intro previous h; cases h)
      | some previous =>
          have hpreviousReady : FieldCacheMergeReady previous :=
            hprevious previous rfl
          cases hreuse
                : reusablePreviousValue? schema fieldDefinition.outputType previous with
          | some reusable =>
              cases previous with
              | null =>
                  simp [reusablePreviousValue?] at hreuse
                  subst reusable
                  simpa [reusablePreviousValue?, resultValueOrNull] using
                    hpreviousReady
              | scalar value =>
                  by_cases hcomposite :
                      fieldDefinition.outputType.isCompositeBool schema = true
                  · simp [reusablePreviousValue?, hcomposite] at hreuse
                  · simp [reusablePreviousValue?, hcomposite] at hreuse
                    subst reusable
                    simpa [reusablePreviousValue?, hcomposite, resultValueOrNull] using
                      hpreviousReady
              | object previousSource fields =>
                  simp [reusablePreviousValue?] at hreuse
              | list sourceValues? values =>
                  cases sourceValues? with
                  | none =>
                      by_cases hcomposite :
                          fieldDefinition.outputType.isCompositeBool schema = true
                      · simp [reusablePreviousValue?, hcomposite] at hreuse
                      · simp [reusablePreviousValue?, hcomposite] at hreuse
                        subst reusable
                        simpa [reusablePreviousValue?, hcomposite,
                          resultValueOrNull] using hpreviousReady
                  | some sourceValues =>
                      simp [reusablePreviousValue?] at hreuse
          | none =>
              cases previous with
              | null =>
                  simp [reusablePreviousValue?] at hreuse
              | scalar value =>
                  simp [hreuse, resultValueOrNull]
                  exact FieldCacheMergeReady.null
              | object previousSource fields =>
                  exact
                    hcomplete fieldDefinition.outputType field.selectionSet
                      previousSource (some (.object previousSource fields))
                      (by intro cached h; cases h; exact hpreviousReady)
              | list sourceValues? values =>
                  cases sourceValues? with
                  | none =>
                      simp [hreuse, resultValueOrNull]
                      exact FieldCacheMergeReady.null
                  | some sourceValues =>
                      exact
                        hcomplete fieldDefinition.outputType field.selectionSet
                          (.list sourceValues)
                          (some (.list (some sourceValues) values))
                          (by intro cached h; cases h; exact hpreviousReady)

theorem resultCombine_cons_values_cacheReady {ObjectRef : Type}
    (head : Result (FieldCacheValue ObjectRef))
    (tail : Result (List (FieldCacheValue ObjectRef)))
    : FieldCacheMergeReady (resultValueOrNull head)
      -> (∀ tailValues tailErrors,
            tail = .ok (tailValues, tailErrors)
            -> ∀ response, response ∈ tailValues -> FieldCacheMergeReady response)
      -> ∀ completedValues errors,
          Result.combine List.cons head tail = .ok (completedValues, errors)
          -> ∀ response, response ∈ completedValues -> FieldCacheMergeReady response := by
  intro hheadReady htailReady completedValues errors hok response hmem
  cases head with
  | error headErrors =>
      cases tail with
      | error tailErrors =>
          simp [GraphQL.Execution.Result.combine] at hok
      | ok tailResult =>
          rcases tailResult with ⟨tailValues, tailErrors⟩
          simp [GraphQL.Execution.Result.combine] at hok
  | ok headResult =>
      rcases headResult with ⟨headValue, headErrors⟩
      cases tail with
      | error tailErrors =>
          simp [GraphQL.Execution.Result.combine] at hok
      | ok tailResult =>
          rcases tailResult with ⟨tailValues, tailErrors⟩
          simp [GraphQL.Execution.Result.combine] at hok
          rcases hok with ⟨hcompletedValues, _herrors⟩
          subst completedValues
          simp at hmem
          rcases hmem with hresponse | htailMem
          · subst response
            simpa [resultValueOrNull] using hheadReady
          · exact htailReady tailValues tailErrors rfl response htailMem

mutual
  theorem visitSelection_cacheReady {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ selection output,
          FieldCacheMergeReady output
          -> FieldCacheMergeReady
              (visitSelection schema resolvers variableValues fuel parentType source
                selection output).value := by
    intro selection output houtput
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases output with
          | null =>
              simpa [visitSelection, hallows, mergeResponseFieldResult,
                mergeResponseFieldIntoObject] using houtput
          | scalar value =>
              simpa [visitSelection, hallows, mergeResponseFieldResult,
                mergeResponseFieldIntoObject] using houtput
          | list sourceValues? values =>
              simpa [visitSelection, hallows, mergeResponseFieldResult,
                mergeResponseFieldIntoObject] using houtput
          | object objectSource fields =>
              have hprevious :
                  ∀ previous,
                    objectField? responseName (.object objectSource fields)
                        = some previous
                    -> FieldCacheMergeReady previous := by
                intro previous hlookup
                exact
                  lookupField?_some_cacheReady objectSource responseName fields
                    previous houtput (by simpa [objectField?] using hlookup)
              simp only [visitSelection, hallows, if_true]
              apply (mergeResponseFieldResult_cacheReady_and_shape objectSource
                      responseName _ fields houtput ?_).1
              cases fuel with
              | zero =>
                  cases hlookup
                        : objectField? responseName (.object objectSource fields) with
                  | none =>
                      simpa [hlookup] using
                        (resultValueOrNull_outOfFuel_cacheReady
                          (ObjectRef := ObjectRef))
                  | some previous =>
                      simpa [hlookup, resultValueOrNull] using
                        hprevious previous hlookup
              | succ completionFuel =>
                  exact
                    executeField_resultValueOrNull_cacheReady_of_completeValue
                      schema resolvers variableValues completionFuel source
                      (objectField? responseName (.object objectSource fields))
                      (executableField parentType responseName fieldName arguments
                        selectionSet)
                      (by
                        intro fieldType childSelectionSet value previous? hprevious'
                        exact
                          completeValue_cacheReady schema resolvers variableValues
                            completionFuel fieldType childSelectionSet value previous?
                            hprevious')
                      hprevious
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simpa [visitSelection, hfalse] using houtput
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases typeCondition with
          | none =>
              simpa [visitSelection, hallows] using
                visitSubfields_cacheReady schema resolvers variableValues fuel
                  parentType source selectionSet output houtput
          | some typeCondition =>
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source typeCondition = true
              · simpa [visitSelection, hallows, happly] using
                  visitSubfields_cacheReady schema resolvers variableValues fuel
                    parentType source selectionSet output houtput
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source typeCondition =
                      false := by
                  cases h :
                      doesFragmentTypeApplyBool schema parentType source typeCondition
                  · rfl
                  · contradiction
                simpa [visitSelection, hallows, hfalse] using houtput
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          cases typeCondition <;> simpa [visitSelection, hfalse] using houtput
  termination_by selection output _houtput => (fuel, 0, sizeOf selection, 0)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem visitSubfields_cacheReady {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ selectionSet output,
          FieldCacheMergeReady output
          -> FieldCacheMergeReady
              (visitSubfields schema resolvers variableValues fuel parentType source
                selectionSet output).value := by
    intro selectionSet output houtput
    cases selectionSet with
    | nil =>
        simpa [visitSubfields] using houtput
    | cons selection rest =>
        let head :=
          visitSelection schema resolvers variableValues fuel parentType source
            selection output
        have hheadReady : FieldCacheMergeReady head.value :=
          visitSelection_cacheReady schema resolvers variableValues fuel parentType
            source selection output houtput
        cases hstatus : head.status with
        | error errors =>
            simpa [visitSubfields, head, hstatus] using hheadReady
        | ok ok =>
            have htailReady :=
              visitSubfields_cacheReady schema resolvers variableValues fuel
                parentType source rest head.value hheadReady
            simpa [visitSubfields, head, hstatus] using htailReady
  termination_by selectionSet output _houtput =>
    (fuel, 0, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem completeValue_cacheReady {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : ∀ fuel fieldType selectionSet value previous?,
          (∀ previous, previous? = some previous -> FieldCacheMergeReady previous)
          -> FieldCacheMergeReady
              (resultValueOrNull
                (completeValue schema resolvers variableValues fuel fieldType
                  selectionSet value previous?)) := by
    intro fuel fieldType selectionSet value previous? hprevious
    cases fuel with
    | zero =>
        simpa [completeValue] using
          (resultValueOrNull_outOfFuel_cacheReady (ObjectRef := ObjectRef))
    | succ completionFuel =>
        cases previous? with
        | none =>
            cases fieldType with
            | nonNull inner =>
                simpa [completeValue] using
                  resultValueOrNull_nonNullCompletion_cacheReady
                    (completeValue schema resolvers variableValues
                      (completionFuel + 1) inner selectionSet value none)
                    (completeValue_cacheReady schema resolvers variableValues
                      (completionFuel + 1) inner selectionSet value none
                      (by intro previous h; cases h))
            | named typeName =>
                cases value with
                | null =>
                    simp [completeValue, resultValueOrNull]
                    exact FieldCacheMergeReady.null
                | scalar scalarValue =>
                    by_cases hcomposite :
                        (TypeRef.named typeName).isCompositeBool schema = true
                    · simp [completeValue, hcomposite, resultValueOrNull]
                      exact FieldCacheMergeReady.null
                    · have hfalse :
                          (TypeRef.named typeName).isCompositeBool schema = false := by
                        cases h :
                            (TypeRef.named typeName).isCompositeBool schema
                        · rfl
                        · contradiction
                      simp [completeValue, hfalse, resultValueOrNull]
                      exact FieldCacheMergeReady.scalar scalarValue
                | object runtimeType ref =>
                    by_cases hinclude :
                        schema.typeIncludesObjectBool typeName runtimeType = true
                    · have hbase :
                          FieldCacheMergeReady
                            (.object (ResolverValue.object runtimeType ref) []) :=
                        FieldCacheMergeReady.object
                          (.object runtimeType ref) []
                          (by simp [FieldCacheKeysNodup])
                          (by intro responseName response hmem; simp at hmem)
                      have hvisited :=
                        visitSubfields_cacheReady schema resolvers variableValues
                          completionFuel runtimeType (.object runtimeType ref)
                          selectionSet (.object (.object runtimeType ref) []) hbase
                      simpa [completeValue, hinclude, reuseOrCreateObject?] using
                        resultValueOrNull_catchVisitBubbleAsNull_cacheReady
                          (visitSubfields schema resolvers variableValues
                            completionFuel runtimeType (.object runtimeType ref)
                            selectionSet (.object (.object runtimeType ref) [])).value
                          (visitSubfields schema resolvers variableValues
                            completionFuel runtimeType (.object runtimeType ref)
                            selectionSet (.object (.object runtimeType ref) [])).status
                          hvisited
                    · have hfalse :
                          schema.typeIncludesObjectBool typeName runtimeType = false := by
                        cases h :
                            schema.typeIncludesObjectBool typeName runtimeType
                        · rfl
                        · contradiction
                      simp [completeValue, hfalse, resultValueOrNull]
                      exact FieldCacheMergeReady.null
                | list values =>
                    simp [completeValue, resultValueOrNull]
                    exact FieldCacheMergeReady.null
            | list inner =>
                cases value with
                | list values =>
                    let sourceValues? :=
                      if inner.isCompositeBool schema then some values else none
                    have hcompleted :
                        ∀ completedValues errors,
                          completeValueList schema resolvers variableValues
                              completionFuel inner selectionSet values []
                            = .ok (completedValues, errors)
                          -> FieldCacheMergeReady
                              (.list sourceValues? completedValues) := by
                      intro completedValues errors hok
                      exact
                        FieldCacheMergeReady.list sourceValues? completedValues
                          (completeValueList_values_cacheReady schema resolvers
                            variableValues completionFuel inner selectionSet values []
                            (by intro previous hmem; simp at hmem) completedValues
                            errors hok)
                    simpa [completeValue, reuseOrCreateList?, sourceValues?] using
                      resultValueOrNull_catchBubbleAsNull_cacheReady
                        (fun completedValues =>
                          FieldCacheValue.list sourceValues? completedValues)
                        (completeValueList schema resolvers variableValues
                          completionFuel inner selectionSet values []) hcompleted
                | null =>
                    simp [completeValue, resultValueOrNull]
                    exact FieldCacheMergeReady.null
                | scalar scalarValue =>
                    simp [completeValue, resultValueOrNull]
                    exact FieldCacheMergeReady.null
                | object runtimeType ref =>
                    simp [completeValue, resultValueOrNull]
                    exact FieldCacheMergeReady.null
        | some previous =>
            have hpreviousReady : FieldCacheMergeReady previous :=
              hprevious previous rfl
            cases previous with
            | null =>
                simp [completeValue, resultValueOrNull]
                exact FieldCacheMergeReady.null
            | scalar previousValue =>
                simp [completeValue, resultValueOrNull]
                exact FieldCacheMergeReady.null
            | object previousSource previousFields =>
                cases fieldType with
                | nonNull inner =>
                    simpa [completeValue] using
                      resultValueOrNull_nonNullCompletion_cacheReady
                        (completeValue schema resolvers variableValues
                          (completionFuel + 1) inner selectionSet value
                          (some (.object previousSource previousFields)))
                        (completeValue_cacheReady schema resolvers variableValues
                          (completionFuel + 1) inner selectionSet value
                          (some (.object previousSource previousFields))
                          (by intro cached h; cases h; exact hpreviousReady))
                | named typeName =>
                    cases value with
                    | object runtimeType ref =>
                        by_cases hinclude :
                            schema.typeIncludesObjectBool typeName runtimeType = true
                        · have hvisited :=
                            visitSubfields_cacheReady schema resolvers variableValues
                              completionFuel runtimeType (.object runtimeType ref)
                              selectionSet (.object previousSource previousFields)
                              hpreviousReady
                          simpa [completeValue, hinclude, reuseOrCreateObject?] using
                            resultValueOrNull_catchVisitBubbleAsNull_cacheReady
                              (visitSubfields schema resolvers variableValues
                                completionFuel runtimeType (.object runtimeType ref)
                                selectionSet
                                (.object previousSource previousFields)).value
                              (visitSubfields schema resolvers variableValues
                                completionFuel runtimeType (.object runtimeType ref)
                                selectionSet
                                (.object previousSource previousFields)).status
                              hvisited
                        · have hfalse :
                              schema.typeIncludesObjectBool typeName runtimeType =
                                false := by
                            cases h :
                                schema.typeIncludesObjectBool typeName runtimeType
                            · rfl
                            · contradiction
                          simp [completeValue, hfalse, resultValueOrNull]
                          exact FieldCacheMergeReady.null
                    | null =>
                        simp [completeValue, resultValueOrNull]
                        exact FieldCacheMergeReady.null
                    | scalar scalarValue =>
                        simp [completeValue, resultValueOrNull]
                        exact FieldCacheMergeReady.null
                    | list values =>
                        simp [completeValue, resultValueOrNull]
                        exact FieldCacheMergeReady.null
                | list inner =>
                    cases value <;>
                      simp [completeValue, reuseOrCreateList?, resultValueOrNull] <;>
                      exact FieldCacheMergeReady.null
            | list sourceValues? previousValues =>
                cases fieldType with
                | nonNull inner =>
                    simpa [completeValue] using
                      resultValueOrNull_nonNullCompletion_cacheReady
                        (completeValue schema resolvers variableValues
                          (completionFuel + 1) inner selectionSet value
                          (some (.list sourceValues? previousValues)))
                        (completeValue_cacheReady schema resolvers variableValues
                          (completionFuel + 1) inner selectionSet value
                          (some (.list sourceValues? previousValues))
                          (by intro cached h; cases h; exact hpreviousReady))
                | named typeName =>
                    cases value <;>
                      simp [completeValue, reuseOrCreateObject?, resultValueOrNull] <;>
                      exact FieldCacheMergeReady.null
                | list inner =>
                    cases value with
                    | list values =>
                        have hpreviousValues :
                            ∀ previous,
                              previous ∈ previousValues
                              -> FieldCacheMergeReady previous := by
                          intro previous hmem
                          exact
                            FieldCacheMergeReady.list_value sourceValues?
                              previousValues previous hpreviousReady hmem
                        have hcompleted :
                            ∀ completedValues errors,
                              completeValueList schema resolvers variableValues
                                  completionFuel inner selectionSet values
                                  previousValues
                                = .ok (completedValues, errors)
                              -> FieldCacheMergeReady
                                  (.list sourceValues? completedValues) := by
                          intro completedValues errors hok
                          exact
                            FieldCacheMergeReady.list sourceValues? completedValues
                              (completeValueList_values_cacheReady schema resolvers
                                variableValues completionFuel inner selectionSet values
                                previousValues hpreviousValues completedValues errors
                                hok)
                        simpa [completeValue, reuseOrCreateList?] using
                          resultValueOrNull_catchBubbleAsNull_cacheReady
                            (fun completedValues =>
                              FieldCacheValue.list sourceValues? completedValues)
                            (completeValueList schema resolvers variableValues
                              completionFuel inner selectionSet values previousValues)
                            hcompleted
                    | null =>
                        simp [completeValue, resultValueOrNull]
                        exact FieldCacheMergeReady.null
                    | scalar scalarValue =>
                        simp [completeValue, resultValueOrNull]
                        exact FieldCacheMergeReady.null
                    | object runtimeType ref =>
                        simp [completeValue, resultValueOrNull]
                        exact FieldCacheMergeReady.null
  termination_by fuel fieldType _selectionSet value _previous? =>
    (fuel, 0, sizeOf fieldType, sizeOf value)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem completeValueList_values_cacheReady {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (itemType : TypeRef) (selectionSet : List Selection)
      : ∀ values previousValues,
          (∀ previous, previous ∈ previousValues -> FieldCacheMergeReady previous)
          -> ∀ completedValues errors,
              completeValueList schema resolvers variableValues fuel itemType
                  selectionSet values previousValues
                = .ok (completedValues, errors)
              -> ∀ response,
                  response ∈ completedValues -> FieldCacheMergeReady response := by
    intro values previousValues hpreviousValues completedValues errors hok
    cases values with
    | nil =>
        cases previousValues with
        | nil =>
            simp [completeValueList] at hok
            rcases hok with ⟨hcompletedValues, _herrors⟩
            subst completedValues
            intro response hmem
            simp at hmem
        | cons previous rest =>
            simp [completeValueList] at hok
    | cons value restValues =>
        let previous? := previousValues.head?
        let remainingPrevious := previousValues.tail
        let head : Result (FieldCacheValue ObjectRef) :=
          match previous? with
          | some .null => .ok (.null, 0)
          | _ =>
              completeValue schema resolvers variableValues fuel itemType
                selectionSet value previous?
        let tail : Result (List (FieldCacheValue ObjectRef)) :=
          completeValueList schema resolvers variableValues fuel itemType
            selectionSet restValues remainingPrevious
        have hprevious? :
            ∀ previous,
              previous? = some previous -> FieldCacheMergeReady previous := by
          cases previousValues with
          | nil =>
              intro previous hsome
              simp [previous?] at hsome
          | cons previous rest =>
              intro previousValue hsome
              have heq : previous = previousValue := by
                simpa [previous?] using Option.some.inj hsome
              subst previousValue
              exact hpreviousValues previous (by simp)
        have hremainingPrevious :
            ∀ previous,
              previous ∈ remainingPrevious -> FieldCacheMergeReady previous := by
          cases previousValues with
          | nil =>
              intro previous hmem
              simp [remainingPrevious] at hmem
          | cons previous rest =>
              intro previousValue hmem
              exact hpreviousValues previousValue (by
                right
                exact hmem)
        have hheadReady : FieldCacheMergeReady (resultValueOrNull head) := by
          dsimp [head]
          cases hprev : previous? with
          | none =>
              exact
                completeValue_cacheReady schema resolvers variableValues fuel
                  itemType selectionSet value none
                  (by intro previous h; exact hprevious? previous (by rw [hprev]; exact h))
          | some previous =>
              cases previous with
              | null => exact FieldCacheMergeReady.null
              | scalar previousValue =>
                  exact
                    completeValue_cacheReady schema resolvers variableValues fuel
                      itemType selectionSet value (some (.scalar previousValue))
                      (by
                        intro cached h
                        exact hprevious? cached (by rw [hprev]; exact h))
              | object previousSource fields =>
                  exact
                    completeValue_cacheReady schema resolvers variableValues fuel
                      itemType selectionSet value
                      (some (.object previousSource fields))
                      (by
                        intro cached h
                        exact hprevious? cached (by rw [hprev]; exact h))
              | list sourceValues? values =>
                  exact
                    completeValue_cacheReady schema resolvers variableValues fuel
                      itemType selectionSet value
                      (some (.list sourceValues? values))
                      (by
                        intro cached h
                        exact hprevious? cached (by rw [hprev]; exact h))
        have htailReady :
            ∀ tailValues tailErrors,
              tail = .ok (tailValues, tailErrors)
              -> ∀ response,
                  response ∈ tailValues -> FieldCacheMergeReady response :=
          completeValueList_values_cacheReady schema resolvers variableValues fuel
            itemType selectionSet restValues remainingPrevious hremainingPrevious
        exact
          resultCombine_cons_values_cacheReady head tail hheadReady htailReady
            completedValues errors (by
              rw [completeValueList.eq_3] at hok
              change Result.combine List.cons head tail = .ok (completedValues, errors) at hok
              exact hok)
  termination_by values previousValues _hpreviousValues completedValues errors _hok =>
    (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega
end

theorem visitFieldResult_cacheReady {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (output : FieldCacheValue ObjectRef)
    : FieldCacheMergeReady output
      -> FieldCacheMergeReady
          (resultValueOrNull
            (match fuel with
              | 0 =>
                  match objectField? responseName output with
                  | some previous => .ok (previous, 0)
                  | none => outOfFuel
              | completionFuel + 1 =>
                  executeField schema resolvers variableValues completionFuel source
                    (objectField? responseName output)
                    (executableField parentType responseName fieldName arguments
                      selectionSet))) := by
  intro houtput
  have hprevious :
      ∀ previous,
        objectField? responseName output = some previous
        -> FieldCacheMergeReady previous := by
    intro previous hlookup
    cases output with
    | null => simp [objectField?] at hlookup
    | scalar value => simp [objectField?] at hlookup
    | list sourceValues? values => simp [objectField?] at hlookup
    | object objectSource fields =>
        exact
          lookupField?_some_cacheReady objectSource responseName fields previous
            houtput (by simpa [objectField?] using hlookup)
  cases fuel with
  | zero =>
      cases hlookup : objectField? responseName output with
      | none =>
          simpa [hlookup] using
            (resultValueOrNull_outOfFuel_cacheReady (ObjectRef := ObjectRef))
      | some previous =>
          simpa [hlookup, resultValueOrNull] using hprevious previous hlookup
  | succ completionFuel =>
      exact
        executeField_resultValueOrNull_cacheReady_of_completeValue schema resolvers
          variableValues completionFuel source (objectField? responseName output)
          (executableField parentType responseName fieldName arguments selectionSet)
          (by
            intro fieldType childSelectionSet value previous? hprevious'
            exact
              completeValue_cacheReady schema resolvers variableValues
                completionFuel fieldType childSelectionSet value previous? hprevious')
          hprevious

mutual
  theorem visitSelection_cacheAbsorptionShape {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ selection output,
          FieldCacheMergeReady output
          -> FieldCacheAbsorptionShape output
              (visitSelection schema resolvers variableValues fuel parentType source
                selection output).value := by
    intro selection output houtput
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases output with
          | null =>
              simpa [visitSelection, hallows, mergeResponseFieldResult,
                mergeResponseFieldIntoObject] using
                FieldCacheAbsorptionShape.refl_of_ready .null houtput
          | scalar value =>
              simpa [visitSelection, hallows, mergeResponseFieldResult,
                mergeResponseFieldIntoObject] using
                FieldCacheAbsorptionShape.refl_of_ready (.scalar value) houtput
          | list sourceValues? values =>
              simpa [visitSelection, hallows, mergeResponseFieldResult,
                mergeResponseFieldIntoObject] using
                FieldCacheAbsorptionShape.refl_of_ready
                  (.list sourceValues? values) houtput
          | object objectSource fields =>
              simp only [visitSelection, hallows, if_true]
              apply (mergeResponseFieldResult_cacheReady_and_shape objectSource
                      responseName _ fields houtput ?_).2
              exact
                visitFieldResult_cacheReady schema resolvers variableValues fuel
                  parentType source responseName fieldName arguments selectionSet
                  (.object objectSource fields) houtput
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simpa [visitSelection, hfalse] using
            FieldCacheAbsorptionShape.refl_of_ready output houtput
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases typeCondition with
          | none =>
              simpa [visitSelection, hallows] using
                visitSubfields_cacheAbsorptionShape schema resolvers
                  variableValues fuel parentType source selectionSet output houtput
          | some typeCondition =>
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source typeCondition =
                    true
              · simpa [visitSelection, hallows, happly] using
                  visitSubfields_cacheAbsorptionShape schema resolvers
                    variableValues fuel parentType source selectionSet output houtput
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source typeCondition =
                      false := by
                  cases h :
                      doesFragmentTypeApplyBool schema parentType source typeCondition
                  · rfl
                  · contradiction
                simpa [visitSelection, hallows, hfalse] using
                  FieldCacheAbsorptionShape.refl_of_ready output houtput
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          cases typeCondition <;> simpa [visitSelection, hfalse] using
            FieldCacheAbsorptionShape.refl_of_ready output houtput
  termination_by selection output _houtput => (sizeOf selection, 0)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem visitSubfields_cacheAbsorptionShape {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ selectionSet output,
          FieldCacheMergeReady output
          -> FieldCacheAbsorptionShape output
              (visitSubfields schema resolvers variableValues fuel parentType source
                selectionSet output).value := by
    intro selectionSet output houtput
    cases selectionSet with
    | nil =>
        simpa [visitSubfields] using
          FieldCacheAbsorptionShape.refl_of_ready output houtput
    | cons selection rest =>
        let head :=
          visitSelection schema resolvers variableValues fuel parentType source
            selection output
        have hheadShape : FieldCacheAbsorptionShape output head.value :=
          visitSelection_cacheAbsorptionShape schema resolvers variableValues fuel
            parentType source selection output houtput
        have hheadReady : FieldCacheMergeReady head.value := hheadShape.output_ready
        cases hstatus : head.status with
        | error errors =>
            simpa [visitSubfields, head, hstatus] using hheadShape
        | ok ok =>
            have htailShape :=
              visitSubfields_cacheAbsorptionShape schema resolvers variableValues
                fuel parentType source rest head.value hheadReady
            simpa [visitSubfields, head, hstatus] using
              FieldCacheAbsorptionShape.trans hheadShape htailShape
  termination_by selectionSet output _houtput => (sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega
end

end ExecutionUngrouped
end Algorithms

end GraphQL
