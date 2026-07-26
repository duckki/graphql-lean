import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldExecution

namespace GraphQL
namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

variable {ObjectRef : Type}

theorem combineVisitStatus_error_positive {left right : VisitStatus} {errors : Nat}
    : (combineVisitStatus left right) = .error errors
      -> (∀ leftErrors, left = .error leftErrors -> 0 < leftErrors)
      -> (∀ rightErrors, right = .error rightErrors -> 0 < rightErrors)
      -> 0 < errors := by
  intro h hleft hright
  cases left with
  | error leftErrors =>
      have hleftPos := hleft leftErrors rfl
      cases right with
      | error rightErrors =>
          simp [combineVisitStatus, GraphQL.Execution.Result.combine] at h
          omega
      | ok rightResult =>
          rcases rightResult with ⟨rightUnit, rightErrors⟩
          simp [combineVisitStatus, GraphQL.Execution.Result.combine] at h
          omega
  | ok leftResult =>
      rcases leftResult with ⟨leftUnit, leftErrors⟩
      cases right with
      | error rightErrors =>
          have hrightPos := hright rightErrors rfl
          simp [combineVisitStatus, GraphQL.Execution.Result.combine] at h
          omega
      | ok rightResult =>
          rcases rightResult with ⟨rightUnit, rightErrors⟩
          simp [combineVisitStatus, GraphQL.Execution.Result.combine] at h

mutual
  theorem visitSubfields_status_error_positive
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ (selectionSet : List Selection) (output : ResponseValue) errors,
          (visitSubfields schema resolvers variableValues fuel parentType source
              selectionSet output).snd
            = .error errors
          -> 0 < errors
    | [], output, errors, h => by
        simp [visitSubfields, visitOk] at h
    | selection :: rest, output, errors, h => by
        simp [visitSubfields] at h
        apply combineVisitStatus_error_positive h
        · intro leftErrors hleft
          exact
            visitSelection_status_error_positive schema resolvers variableValues
              fuel parentType source selection output leftErrors hleft
        · intro rightErrors hright
          exact
            visitSubfields_status_error_positive schema resolvers variableValues
              fuel parentType source rest
              (visitSelection schema resolvers variableValues fuel parentType
                source selection output).fst rightErrors hright

  theorem visitSelection_status_error_positive
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ (selection : Selection) (output : ResponseValue) errors,
          (visitSelection schema resolvers variableValues fuel parentType source
              selection output).snd
            = .error errors
          -> 0 < errors
    | .field responseName fieldName arguments directives selectionSet, output,
        errors, h => by
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases fuel with
          | zero =>
              cases hprevious :
                  responseObjectField? responseName output with
              | none =>
                  simp [visitSelection, hallows, hprevious,
                    mergeResponseFieldResult, GraphQL.Execution.outOfFuel,
                    resultStatus] at h
                  omega
              | some previous =>
                  simp [visitSelection, hallows, hprevious,
                    mergeResponseFieldResult, resultStatus, visitOk] at h
          | succ fuel' =>
              cases hfield :
                  executeField schema resolvers variableValues fuel' source
                    (responseObjectField? responseName output)
                    (executableField parentType responseName fieldName arguments
                      selectionSet) with
              | error fieldErrors =>
                  simp [visitSelection, hallows, mergeResponseFieldResult,
                    hfield, resultStatus] at h
                  subst errors
                  exact
                    executeField_error_positive schema resolvers variableValues
                      fuel' source (responseObjectField? responseName output)
                      (executableField parentType responseName fieldName
                        arguments selectionSet)
                      fieldErrors hfield
              | ok fieldResult =>
                  rcases fieldResult with ⟨fieldValue, fieldErrors⟩
                  simp [visitSelection, hallows, mergeResponseFieldResult,
                    hfield, resultStatus, visitOk] at h
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hallow :
                selectionDirectivesAllowBool variableValues directives <;>
              simp [hallow] at hallows ⊢
          simp [visitSelection, hblocked, visitOk] at h
    | .inlineFragment none directives selectionSet, output, errors, h => by
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [visitSelection, hallows] at h
          exact
            visitSubfields_status_error_positive schema resolvers variableValues
              fuel parentType source selectionSet output errors h
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hallow :
                selectionDirectivesAllowBool variableValues directives <;>
              simp [hallow] at hallows ⊢
          simp [visitSelection, hblocked, visitOk] at h
    | .inlineFragment (some typeCondition) directives selectionSet, output,
        errors, h => by
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · by_cases happly :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                true
          · simp [visitSelection, hallows, happly] at h
            exact
              visitSubfields_status_error_positive schema resolvers
                variableValues fuel parentType source selectionSet output errors
                h
          · have hnotApply :
                doesFragmentTypeApplyBool schema parentType source typeCondition =
                  false := by
              cases hmatch :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition <;>
                simp [hmatch] at happly ⊢
            simp [visitSelection, hallows, hnotApply, visitOk] at h
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hallow :
                selectionDirectivesAllowBool variableValues directives <;>
              simp [hallow] at hallows ⊢
          simp [visitSelection, hblocked, visitOk] at h

  theorem executeField_error_positive
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (completionFuel : Nat)
      (source : ResolverValue ObjectRef) (previous? : Option ResponseValue)
      (field : ExecutableField) errors
      : executeField schema resolvers variableValues completionFuel source previous? field
          = .error errors
        -> 0 < errors := by
    intro h
    cases hlookup : schema.lookupField field.parentType field.fieldName with
    | none =>
        simp [executeField, hlookup] at h
        omega
    | some fieldDefinition =>
        rcases fieldDefinition with ⟨fieldDefinitionName, outputType, fieldArguments⟩
        cases hprevious :
            reusablePreviousValue? schema outputType previous? with
        | some previous =>
            simp [executeField, hlookup, hprevious] at h
        | none =>
            cases hresolve :
                resolvers.resolve field.parentType field.fieldName
                  field.arguments source with
            | none =>
                cases outputType with
                | named typeName =>
                    simp [executeField, hlookup, hprevious, hresolve,
                      handleFieldError] at h
                | list inner =>
                    simp [executeField, hlookup, hprevious, hresolve,
                      handleFieldError] at h
                | nonNull inner =>
                    simp [executeField, hlookup, hprevious, hresolve,
                      handleFieldError] at h
                    omega
            | some resolved =>
                simp [executeField, hlookup, hprevious, hresolve] at h
                exact
                  completeValue_error_positive schema resolvers variableValues
                    completionFuel outputType field.selectionSet
                    resolved previous? errors h

  theorem completeValue_error_positive
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : ∀ fuel fieldType selectionSet (value : ResolverValue ObjectRef) previous? errors,
          completeValue schema resolvers variableValues fuel fieldType selectionSet
              value previous?
            = .error errors
          -> 0 < errors
    | 0, fieldType, selectionSet, value, previous?, errors, h => by
        rw [completeValue.eq_def] at h
        simp [outOfFuel] at h
        omega
    | fuel + 1, fieldType, selectionSet, value, previous?, errors, h => by
        rw [completeValue.eq_def] at h
        cases previous? with
        | none =>
            cases fieldType with
            | named typeName =>
                cases value with
                | null =>
                    simp at h
                | scalar value =>
                    by_cases hcomposite :
                        (TypeRef.named typeName).isCompositeBool schema = true
                    · simp [hcomposite] at h
                      omega
                    · simp [hcomposite] at h
                | object runtimeType ref =>
                    by_cases hincludes :
                        schema.typeIncludesObjectBool typeName runtimeType = true
                    · simp [hincludes, reuseOrCreateObject?,
                        catchVisitBubbleAsNull] at h
                      cases hvisit :
                          (visitSubfields schema resolvers variableValues fuel
                            runtimeType (ResolverValue.object runtimeType ref)
                            selectionSet (ResponseValue.object [])).snd <;>
                        rw [hvisit] at h <;>
                        cases h
                    · have hnotIncludes :
                          schema.typeIncludesObjectBool typeName runtimeType =
                            false := by
                        cases hmatch :
                            schema.typeIncludesObjectBool typeName runtimeType <;>
                          simp [hmatch] at hincludes ⊢
                      simp [hnotIncludes] at h
                      omega
                | list values =>
                    simp at h
                    omega
            | list inner =>
                cases value with
                | list values =>
                    simp [reuseOrCreateList?, catchBubbleAsNull]
                      at h
                    cases hcompleted :
                        completeValueList schema resolvers variableValues fuel
                          inner selectionSet values [] <;>
                      rw [hcompleted] at h <;>
                      cases h
                | null =>
                    simp at h
                | scalar value =>
                    simp at h
                    omega
                | object runtimeType ref =>
                    simp at h
                    omega
            | nonNull inner =>
                cases hinner :
                    completeValue schema resolvers variableValues (fuel + 1)
                      inner selectionSet value none with
                | error innerErrors =>
                    change
                      nonNullCompletion
                          (completeValue schema resolvers variableValues
                            (fuel + 1) inner selectionSet value none) =
                        .error errors at h
                    rw [hinner] at h
                    have herrors : innerErrors = errors := by
                      simpa [nonNullCompletion] using h
                    subst errors
                    exact
                      completeValue_error_positive schema resolvers variableValues
                        (fuel + 1) inner selectionSet value none innerErrors
                        hinner
                | ok innerResult =>
                    rcases innerResult with ⟨innerValue, innerErrors⟩
                    cases innerValue <;> cases innerErrors <;>
                      simp [hinner, nonNullCompletion] at h <;>
                      omega
        | some previous =>
            cases previous with
            | null =>
                simp at h
            | scalar previous =>
                simp at h
                omega
            | object fields =>
                cases fieldType with
                | named typeName =>
                    cases value with
                    | null =>
                        simp at h
                    | scalar value =>
                        simp at h
                        omega
                    | object runtimeType ref =>
                        by_cases hincludes :
                            schema.typeIncludesObjectBool typeName runtimeType =
                              true
                        · simp [hincludes, reuseOrCreateObject?,
                            catchVisitBubbleAsNull] at h
                          cases hvisit :
                              (visitSubfields schema resolvers variableValues
                                fuel runtimeType
                                (ResolverValue.object runtimeType ref)
                                selectionSet (ResponseValue.object fields)).snd <;>
                            rw [hvisit] at h <;>
                            cases h
                        · have hnotIncludes :
                              schema.typeIncludesObjectBool typeName runtimeType =
                                false := by
                            cases hmatch :
                                schema.typeIncludesObjectBool typeName
                                  runtimeType <;>
                              simp [hmatch] at hincludes ⊢
                          simp [hnotIncludes] at h
                          omega
                    | list values =>
                        simp at h
                        omega
                | list inner =>
                    cases value with
                    | list values =>
                        simp [reuseOrCreateList?] at h
                        omega
                    | null =>
                        simp at h
                    | scalar value =>
                        simp at h
                        omega
                    | object runtimeType ref =>
                        simp at h
                        omega
                | nonNull inner =>
                    cases hinner :
                        completeValue schema resolvers variableValues (fuel + 1)
                          inner selectionSet value (some (.object fields)) with
                    | error innerErrors =>
                        change
                          nonNullCompletion
                              (completeValue schema resolvers variableValues
                                (fuel + 1) inner selectionSet value
                                (some (.object fields))) =
                            .error errors at h
                        rw [hinner] at h
                        have herrors : innerErrors = errors := by
                          simpa [nonNullCompletion] using h
                        subst errors
                        exact
                          completeValue_error_positive schema resolvers
                            variableValues (fuel + 1) inner selectionSet value
                            (some (.object fields)) innerErrors hinner
                    | ok innerResult =>
                        rcases innerResult with ⟨innerValue, innerErrors⟩
                        cases innerValue <;> cases innerErrors <;>
                          simp [hinner, nonNullCompletion] at h <;>
                          omega
            | list previousValues =>
                cases fieldType with
                | named typeName =>
                    cases value with
                    | null =>
                        simp at h
                    | scalar value =>
                        simp at h
                        omega
                    | object runtimeType ref =>
                        by_cases hincludes :
                            schema.typeIncludesObjectBool typeName runtimeType =
                              true
                        · simp [hincludes, reuseOrCreateObject?]
                            at h
                          omega
                        · have hnotIncludes :
                              schema.typeIncludesObjectBool typeName runtimeType =
                                false := by
                            cases hmatch :
                                schema.typeIncludesObjectBool typeName
                                  runtimeType <;>
                              simp [hmatch] at hincludes ⊢
                          simp [hnotIncludes] at h
                          omega
                    | list values =>
                        simp at h
                        omega
                | list inner =>
                    cases value with
                    | list values =>
                        simp [reuseOrCreateList?,
                          catchBubbleAsNull] at h
                        cases hcompleted :
                            completeValueList schema resolvers variableValues
                              fuel inner selectionSet values previousValues <;>
                          rw [hcompleted] at h <;>
                          cases h
                    | null =>
                        simp at h
                    | scalar value =>
                        simp at h
                        omega
                    | object runtimeType ref =>
                        simp at h
                        omega
                | nonNull inner =>
                    cases hinner :
                        completeValue schema resolvers variableValues (fuel + 1)
                          inner selectionSet value (some (.list previousValues))
                        with
                    | error innerErrors =>
                        change
                          nonNullCompletion
                              (completeValue schema resolvers variableValues
                                (fuel + 1) inner selectionSet value
                                (some (.list previousValues))) =
                            .error errors at h
                        rw [hinner] at h
                        have herrors : innerErrors = errors := by
                          simpa [nonNullCompletion] using h
                        subst errors
                        exact
                          completeValue_error_positive schema resolvers
                            variableValues (fuel + 1) inner selectionSet value
                            (some (.list previousValues)) innerErrors hinner
                    | ok innerResult =>
                        rcases innerResult with ⟨innerValue, innerErrors⟩
                        cases innerValue <;> cases innerErrors <;>
                          simp [hinner, nonNullCompletion] at h <;>
                          omega

  theorem completeValueList_head_error_positive
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (selectionSet : List Selection) (value : ResolverValue ObjectRef)
      (previousValues : List ResponseValue) errors
      : (match previousValues.head? with
          | some .null => (.ok (.null, 0) : Result ResponseValue)
          | _ =>
              completeValue schema resolvers variableValues fuel itemType
                selectionSet value previousValues.head?)
          = .error errors
        -> 0 < errors := by
    intro h
    cases hprev : previousValues.head? with
    | none =>
        have hcomplete :
            completeValue schema resolvers variableValues fuel itemType
              selectionSet value none = .error errors := by
          simpa [hprev] using h
        exact
          completeValue_error_positive schema resolvers variableValues fuel
            itemType selectionSet value none errors hcomplete
    | some previous =>
        cases previous with
        | null =>
            simp [hprev] at h
        | scalar previousValue =>
            have hcomplete :
                completeValue schema resolvers variableValues fuel itemType
                  selectionSet value (some (.scalar previousValue)) =
                  .error errors := by
              simpa [hprev] using h
            exact
              completeValue_error_positive schema resolvers variableValues fuel
                itemType selectionSet value (some (.scalar previousValue))
                errors hcomplete
        | object fields =>
            have hcomplete :
                completeValue schema resolvers variableValues fuel itemType
                  selectionSet value (some (.object fields)) = .error errors := by
              simpa [hprev] using h
            exact
              completeValue_error_positive schema resolvers variableValues fuel
                itemType selectionSet value (some (.object fields)) errors
                hcomplete
        | list values =>
            have hcomplete :
                completeValue schema resolvers variableValues fuel itemType
                  selectionSet value (some (.list values)) = .error errors := by
              simpa [hprev] using h
            exact
              completeValue_error_positive schema resolvers variableValues fuel
                itemType selectionSet value (some (.list values)) errors
                hcomplete

  theorem completeValueList_error_positive
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (selectionSet : List Selection)
      : ∀ values previousValues errors,
          completeValueList schema resolvers variableValues fuel itemType
              selectionSet values previousValues
            = .error errors
          -> 0 < errors
    | [], previous :: previousValues, errors, h => by
        simp [completeValueList] at h
        omega
    | [], [], errors, h => by
        simp [completeValueList] at h
    | value :: values, previousValues, errors, h => by
        simp [completeValueList] at h
        let head : Result ResponseValue :=
            match previousValues.head? with
            | some .null => (.ok (.null, 0) : Result ResponseValue)
            | _ =>
                completeValue schema resolvers variableValues fuel itemType
                  selectionSet value previousValues.head?
        let tail : Result (List ResponseValue) :=
            completeValueList schema resolvers variableValues fuel itemType
              selectionSet values previousValues.tail
        change GraphQL.Execution.Result.combine List.cons head tail =
          .error errors at h
        cases hhead : head with
        | error headErrors =>
            cases htail : tail with
            | error tailErrors =>
                simp only [GraphQL.Execution.Result.combine, hhead, htail] at h
                have hheadPos : 0 < headErrors := by
                  have hheadOriginal :
                      (match previousValues.head? with
                        | some .null =>
                            (.ok (.null, 0) : Result ResponseValue)
                        | _ =>
                            completeValue schema resolvers variableValues fuel
                              itemType selectionSet value
                              previousValues.head?) = .error headErrors := by
                    simpa [head] using hhead
                  exact
                    completeValueList_head_error_positive schema resolvers
                      variableValues fuel itemType selectionSet value
                      previousValues headErrors hheadOriginal
                injection h with herrors
                subst errors
                omega
            | ok tailResult =>
                rcases tailResult with ⟨tailValues, tailErrors⟩
                simp only [GraphQL.Execution.Result.combine, hhead, htail] at h
                have hheadPos : 0 < headErrors := by
                  have hheadOriginal :
                      (match previousValues.head? with
                        | some .null =>
                            (.ok (.null, 0) : Result ResponseValue)
                        | _ =>
                            completeValue schema resolvers variableValues fuel
                              itemType selectionSet value
                              previousValues.head?) = .error headErrors := by
                    simpa [head] using hhead
                  exact
                    completeValueList_head_error_positive schema resolvers
                      variableValues fuel itemType selectionSet value
                      previousValues headErrors hheadOriginal
                injection h with herrors
                subst errors
                omega
        | ok headResult =>
            rcases headResult with ⟨headValue, headErrors⟩
            cases htail : tail with
            | error tailErrors =>
                simp only [GraphQL.Execution.Result.combine, hhead, htail] at h
                have htailOriginal :
                    completeValueList schema resolvers variableValues fuel
                      itemType selectionSet values previousValues.tail =
                      .error tailErrors := by
                  simpa [tail] using htail
                have htailPos :=
                  completeValueList_error_positive schema resolvers
                    variableValues fuel itemType selectionSet values
                    previousValues.tail tailErrors htailOriginal
                injection h with herrors
                subst errors
                omega
            | ok tailResult =>
                rcases tailResult with ⟨tailValues, tailErrors⟩
                simp only [GraphQL.Execution.Result.combine, hhead, htail] at h
                cases h
end

theorem completeResolvedValue_error_positive
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (fieldType : TypeRef) (selectionSet : List Selection)
    (resolved : ResolverValue ObjectIdentity)
    (previous? : Option ResponseValue)
    : ∀ errors,
        completeResolvedValue schema resolvers variableValues depth fieldType
            selectionSet resolved previous?
          = .error errors
        -> 0 < errors := by
  intro errors h
  unfold completeResolvedValue at h
  cases hreuse :
      reusablePreviousValue? schema fieldType previous? with
  | some previous =>
      simp [hreuse] at h
  | none =>
      simp [hreuse] at h
      cases fieldType with
      | named typeName =>
          exact
            completeValue_error_positive schema resolvers variableValues depth
              (.named typeName) selectionSet resolved previous? errors h
      | list inner =>
          exact
            completeValue_error_positive schema resolvers variableValues depth
              (.list inner) selectionSet resolved previous? errors h
      | nonNull inner =>
          cases hinner :
              completeResolvedValue schema resolvers variableValues depth inner
                selectionSet resolved previous? with
          | error innerErrors =>
              simp [hinner, nonNullCompletion] at h
              subst errors
              exact
                completeResolvedValue_error_positive schema resolvers
                  variableValues depth inner selectionSet resolved previous?
                  innerErrors hinner
          | ok innerResult =>
              rcases innerResult with ⟨innerValue, innerErrors⟩
              cases innerValue <;> cases innerErrors <;>
                simp [hinner, nonNullCompletion] at h ⊢ <;> omega

mutual
  theorem specCompleteValue_error_positive
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : ∀ fuel fieldType fields (value : ResolverValue ObjectRef) errors,
          GraphQL.Execution.completeValue schema resolvers variableValues fuel
              fieldType fields value
            = .error errors
          -> 0 < errors
    | 0, fieldType, fields, value, errors, h => by
        simp [GraphQL.Execution.completeValue, outOfFuel] at h
        omega
    | fuel + 1, fieldType, fields, value, errors, h => by
        cases fieldType with
        | nonNull inner =>
            cases hinner :
                GraphQL.Execution.completeValue schema resolvers variableValues
                  (fuel + 1) inner fields value with
            | error innerErrors =>
                have herrors : innerErrors = errors := by
                  simpa [GraphQL.Execution.completeValue, hinner,
                    nonNullCompletion] using h
                subst errors
                exact
                  specCompleteValue_error_positive schema resolvers
                    variableValues (fuel + 1) inner fields value innerErrors
                    hinner
            | ok innerResult =>
                rcases innerResult with ⟨innerValue, innerErrors⟩
                cases innerValue <;> cases innerErrors <;>
                  simp [GraphQL.Execution.completeValue, hinner,
                    nonNullCompletion] at h <;> omega
        | named typeName =>
            cases value with
            | null =>
                simp [GraphQL.Execution.completeValue] at h
            | scalar scalarValue =>
                by_cases hcomposite :
                    (TypeRef.named typeName).isCompositeBool schema = true
                · simp [GraphQL.Execution.completeValue, hcomposite] at h
                  omega
                · simp [GraphQL.Execution.completeValue, hcomposite] at h
            | object runtimeType ref =>
                by_cases hincludes :
                    schema.typeIncludesObjectBool typeName runtimeType = true
                · simp [GraphQL.Execution.completeValue, hincludes,
                    catchBubbleAsNull] at h
                  cases hcompleted :
                      GraphQL.Execution.executeCollectedFields schema resolvers
                        variableValues fuel (.object runtimeType ref)
                        (GraphQL.Execution.collectFields schema variableValues
                          runtimeType (.object runtimeType ref)
                          (GraphQL.Execution.mergedFieldSelectionSet
                            fields)) <;>
                    rw [hcompleted] at h <;>
                    cases h
                · have hnotIncludes :
                      schema.typeIncludesObjectBool typeName runtimeType =
                        false := by
                    cases hmatch :
                        schema.typeIncludesObjectBool typeName runtimeType <;>
                      simp [hmatch] at hincludes ⊢
                  simp [GraphQL.Execution.completeValue, hnotIncludes] at h
                  omega
            | list values =>
                simp [GraphQL.Execution.completeValue] at h
                omega
        | list inner =>
            cases value with
            | list values =>
                simp [GraphQL.Execution.completeValue, catchBubbleAsNull] at h
                cases hcompleted :
                    GraphQL.Execution.completeValueList schema resolvers
                      variableValues fuel inner fields values <;>
                  rw [hcompleted] at h <;>
                  cases h
            | null =>
                simp [GraphQL.Execution.completeValue] at h
            | scalar scalarValue =>
                simp [GraphQL.Execution.completeValue] at h
                omega
            | object runtimeType ref =>
                simp [GraphQL.Execution.completeValue] at h
                omega

  theorem specCompleteValueList_error_positive
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField)
      : ∀ values errors,
          GraphQL.Execution.completeValueList schema resolvers variableValues fuel
              itemType fields values
            = .error errors
          -> 0 < errors
    | [], errors, h => by
        simp [GraphQL.Execution.completeValueList] at h
    | value :: values, errors, h => by
        simp [GraphQL.Execution.completeValueList] at h
        cases hhead :
            GraphQL.Execution.completeValue schema resolvers variableValues fuel
              itemType fields value with
        | error headErrors =>
            cases htail :
                GraphQL.Execution.completeValueList schema resolvers
                  variableValues fuel itemType fields values with
            | error tailErrors =>
                simp [hhead, htail, GraphQL.Execution.Result.combine] at h
                have hheadPos :=
                  specCompleteValue_error_positive schema resolvers
                    variableValues fuel itemType fields value headErrors hhead
                omega
            | ok tailResult =>
                rcases tailResult with ⟨tailValues, tailErrors⟩
                simp [hhead, htail, GraphQL.Execution.Result.combine] at h
                have hheadPos :=
                  specCompleteValue_error_positive schema resolvers
                    variableValues fuel itemType fields value headErrors hhead
                omega
        | ok headResult =>
            rcases headResult with ⟨headValue, headErrors⟩
            cases htail :
                GraphQL.Execution.completeValueList schema resolvers
                  variableValues fuel itemType fields values with
            | error tailErrors =>
                simp [hhead, htail, GraphQL.Execution.Result.combine] at h
                have htailPos :=
                  specCompleteValueList_error_positive schema resolvers
                    variableValues fuel itemType fields values tailErrors htail
                omega
            | ok tailResult =>
                rcases tailResult with ⟨tailValues, tailErrors⟩
                simp [hhead, htail, GraphQL.Execution.Result.combine] at h
end

end ExecutionUngrouped
end Algorithms
end GraphQL
