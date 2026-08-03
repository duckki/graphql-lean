import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.ExecutionInvariants

/-!
Output erasure and source-alignment facts for cached ungrouped execution.

This layer projects cache-carrying values to ordinary response values and
tracks resolver-source alignment through completion.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem lookupField?_outputFields {ObjectRef : Type} (responseName : Name)
    : ∀ fields : List (Name × FieldCacheValue ObjectRef),
        (lookupField? responseName fields).map FieldCacheValue.output
        = ExecutionUngroupedUncached.lookupResponseField? responseName
            (outputFields fields)
  | [] => by
      simp [lookupField?, ExecutionUngroupedUncached.lookupResponseField?]
  | (fieldResponseName, response) :: rest => by
      by_cases h : fieldResponseName == responseName
      · simp [lookupField?, ExecutionUngroupedUncached.lookupResponseField?, h]
      · simp [lookupField?, ExecutionUngroupedUncached.lookupResponseField?, h,
          lookupField?_outputFields responseName rest]

theorem objectField?_output {ObjectRef : Type} (responseName : Name)
    (value : FieldCacheValue ObjectRef)
    : (objectField? responseName value).map FieldCacheValue.output
      = ExecutionUngroupedUncached.responseObjectField? responseName value.output := by
  cases value <;>
    simp [objectField?, ExecutionUngroupedUncached.responseObjectField?]
  rename_i source fields
  simpa using lookupField?_outputFields (ObjectRef := ObjectRef) responseName fields

theorem lookupField?_mergeResponseField_self {ObjectRef : Type}
    (responseName : Name) (incoming : FieldCacheValue ObjectRef)
    : ∀ fields : List (Name × FieldCacheValue ObjectRef),
        lookupField? responseName (mergeResponseField responseName incoming fields)
        = match lookupField? responseName fields with
          | none => some incoming
          | some existing => some (mergeResponse existing incoming)
  | [] => by
      simp [lookupField?, mergeResponseField]
  | (fieldResponseName, existing) :: rest => by
      by_cases hname : fieldResponseName == responseName
      · simp [lookupField?, mergeResponseField, hname]
      · simp [lookupField?, mergeResponseField, hname,
          lookupField?_mergeResponseField_self responseName incoming rest]

theorem lookupField?_mergeResponseField_other {ObjectRef : Type}
    (target responseName : Name) (incoming : FieldCacheValue ObjectRef)
    : target ≠ responseName
      -> ∀ fields : List (Name × FieldCacheValue ObjectRef),
          lookupField? target (mergeResponseField responseName incoming fields)
          = lookupField? target fields
  | hne, [] => by
      simp [lookupField?, mergeResponseField]
      exact hne.symm
  | hne, (fieldResponseName, existing) :: rest => by
      by_cases hfieldTarget : fieldResponseName == target
      · have hfieldTargetEq : fieldResponseName = target := beq_iff_eq.mp hfieldTarget
        have hfieldResponse : (fieldResponseName == responseName) = false := by
          cases h : fieldResponseName == responseName
          · rfl
          · have heq : fieldResponseName = responseName := beq_iff_eq.mp h
            exact False.elim (hne (hfieldTargetEq.symm.trans heq))
        simp [lookupField?, mergeResponseField, hfieldTarget, hfieldResponse]
      · by_cases hfieldResponse : fieldResponseName == responseName
        · simp [lookupField?, mergeResponseField, hfieldTarget, hfieldResponse]
        · simp [lookupField?, mergeResponseField, hfieldTarget, hfieldResponse,
            lookupField?_mergeResponseField_other target responseName incoming hne
              rest]

theorem reusablePreviousValue?_output {ObjectRef : Type} (schema : Schema)
    (fieldType : TypeRef) (previous reusable : FieldCacheValue ObjectRef)
    : reusablePreviousValue? schema fieldType previous = some reusable
      -> ExecutionUngroupedUncached.reusablePreviousValue? schema fieldType
            (some previous.output)
          = some reusable.output := by
  intro h
  cases previous with
  | null =>
      simp [reusablePreviousValue?] at h
      subst reusable
      simp [ExecutionUngroupedUncached.reusablePreviousValue?]
  | scalar value =>
      simp [reusablePreviousValue?,
        ExecutionUngroupedUncached.reusablePreviousValue?] at h ⊢
      rcases h with ⟨hcomposite, hreusable⟩
      subst reusable
      simp [hcomposite]
  | object source fields =>
      simp [reusablePreviousValue?] at h
  | list sourceValues? values =>
      cases sourceValues? with
      | none =>
          simp [reusablePreviousValue?,
            ExecutionUngroupedUncached.reusablePreviousValue?] at h ⊢
          rcases h with ⟨hcomposite, hreusable⟩
          subst reusable
          simp [hcomposite]
      | some sourceValues =>
          simp [reusablePreviousValue?] at h

theorem reuseOrCreateObject?_output {ObjectRef : Type}
    (source : ResolverValue ObjectRef)
    (previous? : Option (FieldCacheValue ObjectRef))
    : (reuseOrCreateObject? source previous?).map FieldCacheValue.output
      = ExecutionUngroupedUncached.reuseOrCreateObject?
          (previous?.map FieldCacheValue.output) := by
  cases previous? with
  | none =>
      simp [reuseOrCreateObject?,
        ExecutionUngroupedUncached.reuseOrCreateObject?]
  | some previous =>
      cases previous <;>
        simp [reuseOrCreateObject?,
          ExecutionUngroupedUncached.reuseOrCreateObject?]

theorem reuseOrCreateList?_output {ObjectRef : Type} (schema : Schema)
    (itemType : TypeRef) (sourceValues : List (ResolverValue ObjectRef))
    (previous? : Option (FieldCacheValue ObjectRef))
    : (reuseOrCreateList? schema itemType sourceValues previous?).map
        (fun pair => outputValues pair.2)
      = ExecutionUngroupedUncached.reuseOrCreateList?
          (previous?.map FieldCacheValue.output) := by
  cases previous? with
  | none =>
      simp [reuseOrCreateList?,
        ExecutionUngroupedUncached.reuseOrCreateList?]
  | some previous =>
      cases previous <;>
        simp [reuseOrCreateList?,
          ExecutionUngroupedUncached.reuseOrCreateList?]

theorem resultValueOrNull_output {ObjectRef : Type}
    (result : Result (FieldCacheValue ObjectRef))
    : (resultValueOrNull result).output
      = ExecutionUngroupedUncached.resultValueOrNull
          (outputResult FieldCacheValue.output result) := by
  cases result with
  | error errors =>
      simp [resultValueOrNull, ExecutionUngroupedUncached.resultValueOrNull,
        outputResult]
  | ok result =>
      rcases result with ⟨value, errors⟩
      simp [resultValueOrNull, ExecutionUngroupedUncached.resultValueOrNull,
        outputResult]

theorem resultStatus_output {ObjectRef : Type}
    (result : Result (FieldCacheValue ObjectRef))
    : resultStatus result
      = ExecutionUngroupedUncached.resultStatus
          (outputResult FieldCacheValue.output result) := by
  cases result with
  | error errors =>
      simp [resultStatus, ExecutionUngroupedUncached.resultStatus, outputResult]
  | ok result =>
      rcases result with ⟨value, errors⟩
      simp [resultStatus, ExecutionUngroupedUncached.resultStatus, outputResult,
        visitOk, ExecutionUngroupedUncached.visitOk]

theorem mergeResponseFieldIntoObject_output {ObjectRef : Type}
    (responseName : Name) (incoming output : FieldCacheValue ObjectRef)
    : (mergeResponseFieldIntoObject responseName incoming output).output
      = ExecutionUngroupedUncached.mergeResponseFieldIntoObject responseName
          incoming.output output.output := by
  cases output <;>
    simp [mergeResponseFieldIntoObject,
      ExecutionUngroupedUncached.mergeResponseFieldIntoObject,
      output_mergeResponseField]

def outputVisitResult {ObjectRef : Type} (visited : VisitResult ObjectRef)
    : ResponseValue × VisitStatus :=
  (visited.value.output, visited.status)

theorem mergeResponseFieldResult_output {ObjectRef : Type}
    (responseName : Name) (fieldResult : Result (FieldCacheValue ObjectRef))
    (output : FieldCacheValue ObjectRef)
    : outputVisitResult (mergeResponseFieldResult responseName fieldResult output)
      = ExecutionUngroupedUncached.mergeResponseFieldResult responseName
          (outputResult FieldCacheValue.output fieldResult) output.output := by
  cases fieldResult with
  | error errors =>
      simp [outputVisitResult, mergeResponseFieldResult,
        ExecutionUngroupedUncached.mergeResponseFieldResult,
        resultValueOrNull_output, resultStatus_output,
        mergeResponseFieldIntoObject_output, outputResult]
  | ok result =>
      rcases result with ⟨value, errors⟩
      simp [outputVisitResult, mergeResponseFieldResult,
        ExecutionUngroupedUncached.mergeResponseFieldResult,
        resultValueOrNull_output, resultStatus_output,
        mergeResponseFieldIntoObject_output, outputResult]

theorem handleFieldError_output {ObjectRef : Type} (fieldType : TypeRef)
    : outputResult FieldCacheValue.output
        (handleFieldError (ObjectRef := ObjectRef) fieldType)
      = GraphQL.Execution.handleFieldError fieldType := by
  cases fieldType <;>
    simp [handleFieldError, GraphQL.Execution.handleFieldError, outputResult]

theorem nonNullCompletion_output {ObjectRef : Type}
    (result : Result (FieldCacheValue ObjectRef))
    : outputResult FieldCacheValue.output (nonNullCompletion result)
      = GraphQL.Execution.nonNullCompletion
          (outputResult FieldCacheValue.output result) := by
  cases result with
  | error errors =>
      simp [nonNullCompletion, GraphQL.Execution.nonNullCompletion, outputResult]
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value <;> cases errors <;>
        simp [nonNullCompletion, GraphQL.Execution.nonNullCompletion,
          outputResult]

theorem catchBubbleAsNull_output {ObjectRef α : Type}
    (wrap : α -> FieldCacheValue ObjectRef) (result : Result α)
    : outputResult FieldCacheValue.output (catchBubbleAsNull wrap result)
      = GraphQL.Execution.catchBubbleAsNull (fun value => (wrap value).output)
          result := by
  cases result with
  | error errors =>
      simp [catchBubbleAsNull, GraphQL.Execution.catchBubbleAsNull,
        outputResult]
  | ok result =>
      rcases result with ⟨value, errors⟩
      simp [catchBubbleAsNull, GraphQL.Execution.catchBubbleAsNull,
        outputResult]

theorem catchBubbleAsNull_list_output {ObjectRef : Type}
    (sourceValues? : Option (List (ResolverValue ObjectRef)))
    (result : Result (List (FieldCacheValue ObjectRef)))
    : outputResult FieldCacheValue.output
        (catchBubbleAsNull (FieldCacheValue.list sourceValues?) result)
      = GraphQL.Execution.catchBubbleAsNull ResponseValue.list
          (outputResult outputValues result) := by
  cases result with
  | error errors =>
      simp [catchBubbleAsNull, GraphQL.Execution.catchBubbleAsNull, outputResult]
  | ok result =>
      rcases result with ⟨values, errors⟩
      simp [catchBubbleAsNull, GraphQL.Execution.catchBubbleAsNull, outputResult]

theorem catchVisitBubbleAsNull_output {ObjectRef : Type}
    (value : FieldCacheValue ObjectRef) (status : VisitStatus)
    : outputResult FieldCacheValue.output (catchVisitBubbleAsNull value status)
      = GraphQL.Execution.catchBubbleAsNull (fun value => value)
          (match status with
            | .error errors => .error errors
            | .ok (_unit, errors) => .ok (value.output, errors)) := by
  cases status with
  | error errors =>
      simp [catchVisitBubbleAsNull, GraphQL.Execution.catchBubbleAsNull,
        outputResult]
  | ok result =>
      rcases result with ⟨_unit, errors⟩
      simp [catchVisitBubbleAsNull, GraphQL.Execution.catchBubbleAsNull,
        outputResult]

theorem catchVisitBubbleAsNull_output_of_outputVisitResult {ObjectRef : Type}
    (visited : VisitResult ObjectRef) (uncached : ResponseValue × VisitStatus)
    : outputVisitResult visited = uncached
      -> outputResult FieldCacheValue.output
            (catchVisitBubbleAsNull visited.value visited.status)
          = ExecutionUngroupedUncached.catchVisitBubbleAsNull uncached.fst
              uncached.snd := by
  intro h
  subst uncached
  rcases visited with ⟨value, status⟩
  cases status with
  | error errors =>
      simp [outputVisitResult, catchVisitBubbleAsNull,
        ExecutionUngroupedUncached.catchVisitBubbleAsNull, outputResult]
  | ok result =>
      rcases result with ⟨_unit, errors⟩
      simp [outputVisitResult, catchVisitBubbleAsNull,
        ExecutionUngroupedUncached.catchVisitBubbleAsNull, outputResult]

theorem combine_cons_output {ObjectRef : Type}
    (head : Result (FieldCacheValue ObjectRef))
    (tail : Result (List (FieldCacheValue ObjectRef)))
    : outputResult outputValues (GraphQL.Execution.Result.combine List.cons head tail)
      = GraphQL.Execution.Result.combine List.cons
          (outputResult FieldCacheValue.output head)
          (outputResult outputValues tail) := by
  cases head <;> cases tail <;>
    simp [GraphQL.Execution.Result.combine, outputResult]

mutual
  theorem visitSubfields_value_object {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : ∀ fuel parentType source selectionSet objectSource fields,
          ∃ resultFields,
            (visitSubfields schema resolvers variableValues fuel parentType source
              selectionSet (.object objectSource fields)).value
            = .object objectSource resultFields
    | fuel, parentType, source, [], objectSource, fields => by
        exact ⟨fields, by simp [visitSubfields]⟩
    | fuel, parentType, source, selection :: rest, objectSource, fields => by
        unfold visitSubfields
        generalize hselection :
          visitSelection schema resolvers variableValues fuel parentType source
              selection (.object objectSource fields)
          =
          head
        have hhead :=
          visitSelection_value_object schema resolvers variableValues fuel
            parentType source selection objectSource fields
        rcases hhead with ⟨headFields, hhead⟩
        rw [hselection] at hhead
        cases hstatus : head.status with
        | error errors =>
            exact ⟨headFields, by simp [hhead, hstatus]⟩
        | ok ok =>
            have htail :=
              visitSubfields_value_object schema resolvers variableValues fuel
                parentType source rest objectSource headFields
            rcases htail with ⟨tailFields, htail⟩
            exact ⟨tailFields, by simp [hhead, hstatus, htail]⟩

  theorem visitSelection_value_object {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : ∀ fuel parentType source selection objectSource fields,
          ∃ resultFields,
            (visitSelection schema resolvers variableValues fuel parentType source
              selection (.object objectSource fields)).value
            = .object objectSource resultFields
    | fuel, parentType, source,
      .field responseName fieldName arguments directives selectionSet,
      objectSource, fields => by
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases fuel <;>
            simp [visitSelection, hallows, mergeResponseFieldResult,
              mergeResponseFieldIntoObject]
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          exact ⟨fields, by simp [visitSelection, hfalse]⟩
    | fuel, parentType, source,
      .inlineFragment none directives selectionSet, objectSource, fields => by
        by_cases hskip :
            (!selectionDirectivesAllowBool variableValues directives) = true
        · exact ⟨fields, by simp [visitSelection, hskip]⟩
        · have hallow :
              selectionDirectivesAllowBool variableValues directives = true := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · simp [h] at hskip
            · rfl
          simpa [visitSelection, hallow] using
            visitSubfields_value_object schema resolvers variableValues fuel
              parentType source selectionSet objectSource fields
    | fuel, parentType, source,
      .inlineFragment (some typeCondition) directives selectionSet, objectSource,
      fields => by
        by_cases hskip :
            (!selectionDirectivesAllowBool variableValues directives) = true
        · exact ⟨fields, by simp [visitSelection, hskip]⟩
        · have hallow :
              selectionDirectivesAllowBool variableValues directives = true := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · simp [h] at hskip
            · rfl
          by_cases hdoes :
              (!doesFragmentTypeApplyBool schema parentType source typeCondition) =
                true
          · have hnotApply :
                doesFragmentTypeApplyBool schema parentType source typeCondition =
                  false := by
              cases h :
                  doesFragmentTypeApplyBool schema parentType source typeCondition
              · rfl
              · simp [h] at hdoes
            exact ⟨fields, by simp [visitSelection, hallow, hnotApply]⟩
          · have happly :
                doesFragmentTypeApplyBool schema parentType source typeCondition =
                  true := by
              cases h :
                  doesFragmentTypeApplyBool schema parentType source typeCondition
              · simp [h] at hdoes
              · rfl
            simpa [visitSelection, hallow, happly] using
              visitSubfields_value_object schema resolvers variableValues fuel
                parentType source selectionSet objectSource fields
end

theorem resultValueOrNull_nonNullCompletion_sourceAligned {ObjectRef : Type}
    (source : ResolverValue ObjectRef)
    (completed : Result (FieldCacheValue ObjectRef))
    : FieldCacheSourceAligned source (resultValueOrNull completed)
      -> FieldCacheSourceAligned source
          (resultValueOrNull (nonNullCompletion completed)) := by
  intro haligned
  cases completed with
  | error errors =>
      simpa [resultValueOrNull, nonNullCompletion] using haligned
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value with
      | null =>
          simp [resultValueOrNull, nonNullCompletion]
          exact FieldCacheSourceAligned.null source
      | scalar value =>
          simpa [resultValueOrNull, nonNullCompletion] using haligned
      | object objectSource fields =>
          simpa [resultValueOrNull, nonNullCompletion] using haligned
      | list sourceValues? values =>
          simpa [resultValueOrNull, nonNullCompletion] using haligned

theorem resultCombine_cons_sourcesAligned {ObjectRef : Type}
    (source : ResolverValue ObjectRef)
    (sourceRest : List (ResolverValue ObjectRef))
    (head : Result (FieldCacheValue ObjectRef))
    (tail : Result (List (FieldCacheValue ObjectRef)))
    : FieldCacheSourceAligned source (resultValueOrNull head)
      -> (∀ tailValues tailErrors,
            tail = .ok (tailValues, tailErrors)
            -> FieldCacheSourcesAligned sourceRest tailValues)
      -> ∀ completedValues errors,
          Result.combine List.cons head tail = .ok (completedValues, errors)
          -> FieldCacheSourcesAligned (source :: sourceRest) completedValues := by
  intro hheadAligned htailAligned completedValues errors hok
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
          exact
            FieldCacheSourcesAligned.cons
              (by simpa [resultValueOrNull] using hheadAligned)
              (htailAligned tailValues tailErrors rfl)

mutual
  theorem completeValue_sourceAligned {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : ∀ fuel fieldType selectionSet value previous?,
          (∀ previous,
            previous? = some previous -> FieldCacheSourceAligned value previous)
          -> FieldCacheSourceAligned value
              (resultValueOrNull
                (completeValue schema resolvers variableValues fuel fieldType
                  selectionSet value previous?)) := by
    intro fuel fieldType selectionSet value previous? hprevious
    cases fuel with
    | zero =>
        simp [completeValue, resultValueOrNull]
        exact FieldCacheSourceAligned.null value
    | succ completionFuel =>
        cases previous? with
        | none =>
            cases fieldType with
            | nonNull inner =>
                simpa [completeValue] using
                  resultValueOrNull_nonNullCompletion_sourceAligned value
                    (completeValue schema resolvers variableValues
                      (completionFuel + 1) inner selectionSet value none)
                    (completeValue_sourceAligned schema resolvers variableValues
                      (completionFuel + 1) inner selectionSet value none
                      (by intro previous h; cases h))
            | named typeName =>
                cases value with
                | null =>
                    simp [completeValue, resultValueOrNull]
                    exact FieldCacheSourceAligned.null .null
                | scalar scalarValue =>
                    by_cases hcomposite :
                        (TypeRef.named typeName).isCompositeBool schema = true
                    · simp [completeValue, hcomposite, resultValueOrNull]
                      exact FieldCacheSourceAligned.null (.scalar scalarValue)
                    · have hfalse :
                          (TypeRef.named typeName).isCompositeBool schema = false := by
                        cases h :
                            (TypeRef.named typeName).isCompositeBool schema
                        · rfl
                        · contradiction
                      simp [completeValue, hfalse, resultValueOrNull]
                      exact FieldCacheSourceAligned.scalar scalarValue
                | object runtimeType ref =>
                    by_cases hinclude :
                        schema.typeIncludesObjectBool typeName runtimeType = true
                    · generalize hvisited :
                        visitSubfields schema resolvers variableValues
                            completionFuel runtimeType (.object runtimeType ref)
                            selectionSet (.object (.object runtimeType ref) [])
                          = visited
                      have hobject :=
                        visitSubfields_value_object schema resolvers variableValues
                          completionFuel runtimeType (.object runtimeType ref)
                          selectionSet (.object runtimeType ref) []
                      rw [hvisited] at hobject
                      cases hstatus : visited.status with
                      | error errors =>
                          simp [completeValue, hinclude, reuseOrCreateObject?,
                            hvisited, hstatus, catchVisitBubbleAsNull,
                            resultValueOrNull]
                          exact
                            FieldCacheSourceAligned.null (.object runtimeType ref)
                      | ok ok =>
                          rcases hobject with ⟨fields, hvalue⟩
                          rcases ok with ⟨_unit, errors⟩
                          simp [completeValue, hinclude, reuseOrCreateObject?,
                            hvisited, hstatus, catchVisitBubbleAsNull,
                            resultValueOrNull, hvalue]
                          exact
                            FieldCacheSourceAligned.object
                              (.object runtimeType ref) fields
                    · have hfalse :
                          schema.typeIncludesObjectBool typeName runtimeType =
                            false := by
                        cases h :
                            schema.typeIncludesObjectBool typeName runtimeType
                        · rfl
                        · contradiction
                      simp [completeValue, hfalse, resultValueOrNull]
                      exact FieldCacheSourceAligned.null (.object runtimeType ref)
                | list values =>
                    simp [completeValue, resultValueOrNull]
                    exact FieldCacheSourceAligned.null (.list values)
            | list inner =>
                cases value with
                | list values =>
                    generalize hcompleted :
                      completeValueList schema resolvers variableValues
                          completionFuel inner selectionSet values []
                        = completed
                    cases completed with
                    | error errors =>
                        simp [completeValue, reuseOrCreateList?, hcompleted,
                          catchBubbleAsNull, resultValueOrNull]
                        exact FieldCacheSourceAligned.null (.list values)
                    | ok result =>
                        rcases result with ⟨completedValues, errors⟩
                        have halignedValues :
                            FieldCacheSourcesAligned values completedValues :=
                          completeValueList_sourcesAligned schema resolvers
                            variableValues completionFuel inner selectionSet values
                            [] (FieldCacheSourcesPrefixAligned.nil values)
                            completedValues errors hcompleted
                        by_cases hcomposite : inner.isCompositeBool schema = true
                        · simp [completeValue, reuseOrCreateList?, hcompleted,
                            catchBubbleAsNull, resultValueOrNull, hcomposite]
                          exact
                            FieldCacheSourceAligned.cachedList values completedValues
                              halignedValues
                        · have hfalse : inner.isCompositeBool schema = false := by
                            cases h : inner.isCompositeBool schema
                            · rfl
                            · contradiction
                          simp [completeValue, reuseOrCreateList?, hcompleted,
                            catchBubbleAsNull, resultValueOrNull, hfalse]
                          exact
                            FieldCacheSourceAligned.finalList values completedValues
                              halignedValues
                | null =>
                    simp [completeValue, resultValueOrNull]
                    exact FieldCacheSourceAligned.null .null
                | scalar scalarValue =>
                    simp [completeValue, resultValueOrNull]
                    exact FieldCacheSourceAligned.null (.scalar scalarValue)
                | object runtimeType ref =>
                    simp [completeValue, resultValueOrNull]
                    exact FieldCacheSourceAligned.null (.object runtimeType ref)
        | some previous =>
            have hpreviousAligned : FieldCacheSourceAligned value previous :=
              hprevious previous rfl
            cases previous with
            | null =>
                simp [completeValue, resultValueOrNull]
                exact FieldCacheSourceAligned.null value
            | scalar previousValue =>
                simp [completeValue, resultValueOrNull]
                exact FieldCacheSourceAligned.null value
            | object previousSource previousFields =>
                cases hpreviousAligned with
                | object _source _fields =>
                    cases fieldType with
                    | nonNull inner =>
                        simpa [completeValue] using
                          resultValueOrNull_nonNullCompletion_sourceAligned value
                            (completeValue schema resolvers variableValues
                              (completionFuel + 1) inner selectionSet value
                              (some (.object value previousFields)))
                            (completeValue_sourceAligned schema resolvers
                              variableValues (completionFuel + 1) inner
                              selectionSet value
                              (some (.object value previousFields))
                              (by
                                intro cached h
                                cases h
                                exact
                                  FieldCacheSourceAligned.object value
                                    previousFields))
                    | named typeName =>
                        cases value with
                        | object runtimeType ref =>
                            by_cases hinclude :
                                schema.typeIncludesObjectBool typeName runtimeType =
                                  true
                            · generalize hvisited :
                                visitSubfields schema resolvers variableValues
                                    completionFuel runtimeType
                                    (.object runtimeType ref) selectionSet
                                    (.object (.object runtimeType ref)
                                      previousFields)
                                  = visited
                              have hobject :=
                                visitSubfields_value_object schema resolvers
                                  variableValues completionFuel runtimeType
                                  (.object runtimeType ref) selectionSet
                                  (.object runtimeType ref) previousFields
                              rw [hvisited] at hobject
                              cases hstatus : visited.status with
                              | error errors =>
                                  simp [completeValue, hinclude,
                                    reuseOrCreateObject?, hvisited, hstatus,
                                    catchVisitBubbleAsNull, resultValueOrNull]
                                  exact
                                    FieldCacheSourceAligned.null
                                      (.object runtimeType ref)
                              | ok ok =>
                                  rcases hobject with ⟨fields, hvalue⟩
                                  rcases ok with ⟨_unit, errors⟩
                                  simp [completeValue, hinclude,
                                    reuseOrCreateObject?, hvisited, hstatus,
                                    catchVisitBubbleAsNull, resultValueOrNull,
                                    hvalue]
                                  exact
                                    FieldCacheSourceAligned.object
                                      (.object runtimeType ref) fields
                            · have hfalse :
                                  schema.typeIncludesObjectBool typeName runtimeType =
                                    false := by
                                cases h :
                                    schema.typeIncludesObjectBool typeName runtimeType
                                · rfl
                                · contradiction
                              simp [completeValue, hfalse, resultValueOrNull]
                              exact
                                FieldCacheSourceAligned.null
                                  (.object runtimeType ref)
                        | null =>
                            simp [completeValue, resultValueOrNull]
                            exact FieldCacheSourceAligned.null .null
                        | scalar scalarValue =>
                            simp [completeValue, resultValueOrNull]
                            exact
                              FieldCacheSourceAligned.null (.scalar scalarValue)
                        | list values =>
                            simp [completeValue, resultValueOrNull]
                            exact FieldCacheSourceAligned.null (.list values)
                    | list inner =>
                        cases value <;>
                          simp [completeValue, reuseOrCreateList?,
                            resultValueOrNull] <;>
                          apply FieldCacheSourceAligned.null
            | list sourceValues? previousValues =>
                cases hpreviousAligned with
                | cachedList sourceValues _ halignedValues =>
                    cases fieldType with
                    | nonNull inner =>
                        simpa [completeValue] using
                          resultValueOrNull_nonNullCompletion_sourceAligned
                            (.list sourceValues)
                            (completeValue schema resolvers variableValues
                              (completionFuel + 1) inner selectionSet
                              (.list sourceValues)
                              (some (.list (some sourceValues) previousValues)))
                            (completeValue_sourceAligned schema resolvers
                              variableValues (completionFuel + 1) inner
                              selectionSet (.list sourceValues)
                              (some (.list (some sourceValues) previousValues))
                              (by
                                intro cached h
                                cases h
                                exact
                                  FieldCacheSourceAligned.cachedList sourceValues
                                    previousValues halignedValues))
                    | named typeName =>
                        simp [completeValue, resultValueOrNull]
                        exact FieldCacheSourceAligned.null (.list sourceValues)
                    | list inner =>
                        generalize hcompleted :
                          completeValueList schema resolvers variableValues
                              completionFuel inner selectionSet sourceValues
                              previousValues
                            = completed
                        cases completed with
                        | error errors =>
                            simp [completeValue, reuseOrCreateList?, hcompleted,
                              catchBubbleAsNull, resultValueOrNull]
                            exact
                              FieldCacheSourceAligned.null (.list sourceValues)
                        | ok result =>
                            rcases result with ⟨completedValues, errors⟩
                            have hcompletedAligned :
                                FieldCacheSourcesAligned sourceValues
                                  completedValues :=
                              completeValueList_sourcesAligned schema resolvers
                                variableValues completionFuel inner selectionSet
                                sourceValues previousValues
                                halignedValues.toPrefixAligned completedValues errors
                                hcompleted
                            simp [completeValue, reuseOrCreateList?, hcompleted,
                              catchBubbleAsNull, resultValueOrNull]
                            exact
                              FieldCacheSourceAligned.cachedList sourceValues
                                completedValues hcompletedAligned
                | finalList sourceValues _ halignedValues =>
                    cases fieldType with
                    | nonNull inner =>
                        simpa [completeValue] using
                          resultValueOrNull_nonNullCompletion_sourceAligned
                            (.list sourceValues)
                            (completeValue schema resolvers variableValues
                              (completionFuel + 1) inner selectionSet
                              (.list sourceValues)
                              (some (.list none previousValues)))
                            (completeValue_sourceAligned schema resolvers
                              variableValues (completionFuel + 1) inner
                              selectionSet (.list sourceValues)
                              (some (.list none previousValues))
                              (by
                                intro cached h
                                cases h
                                exact
                                  FieldCacheSourceAligned.finalList sourceValues
                                    previousValues halignedValues))
                    | named typeName =>
                        simp [completeValue, resultValueOrNull]
                        exact FieldCacheSourceAligned.null (.list sourceValues)
                    | list inner =>
                        generalize hcompleted :
                          completeValueList schema resolvers variableValues
                              completionFuel inner selectionSet sourceValues
                              previousValues
                            = completed
                        cases completed with
                        | error errors =>
                            simp [completeValue, reuseOrCreateList?, hcompleted,
                              catchBubbleAsNull, resultValueOrNull]
                            exact
                              FieldCacheSourceAligned.null (.list sourceValues)
                        | ok result =>
                            rcases result with ⟨completedValues, errors⟩
                            have hcompletedAligned :
                                FieldCacheSourcesAligned sourceValues
                                  completedValues :=
                              completeValueList_sourcesAligned schema resolvers
                                variableValues completionFuel inner selectionSet
                                sourceValues previousValues
                                halignedValues.toPrefixAligned completedValues errors
                                hcompleted
                            simp [completeValue, reuseOrCreateList?, hcompleted,
                              catchBubbleAsNull, resultValueOrNull]
                            exact
                              FieldCacheSourceAligned.finalList sourceValues
                                completedValues hcompletedAligned
  termination_by fuel fieldType _selectionSet value _previous? =>
    (fuel, sizeOf fieldType, sizeOf value)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem completeValueList_sourcesAligned {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (itemType : TypeRef) (selectionSet : List Selection)
      : ∀ values previousValues,
          FieldCacheSourcesPrefixAligned values previousValues
          -> ∀ completedValues errors,
              completeValueList schema resolvers variableValues fuel itemType
                  selectionSet values previousValues
                = .ok (completedValues, errors)
              -> FieldCacheSourcesAligned values completedValues := by
    intro values previousValues hprevious completedValues errors hok
    cases hprevious with
    | nil =>
        cases values with
        | nil =>
            simp [completeValueList] at hok
            rcases hok with ⟨hcompletedValues, _herrors⟩
            subst completedValues
            exact FieldCacheSourcesAligned.nil
        | cons source sourceRest =>
            let head : Result (FieldCacheValue ObjectRef) :=
              completeValue schema resolvers variableValues fuel itemType
                selectionSet source none
            let tail : Result (List (FieldCacheValue ObjectRef)) :=
              completeValueList schema resolvers variableValues fuel itemType
                selectionSet sourceRest []
            have hheadResultAligned :
                FieldCacheSourceAligned source (resultValueOrNull head) :=
              completeValue_sourceAligned schema resolvers variableValues fuel
                itemType selectionSet source none
                (by intro previous h; cases h)
            have htailAligned :
                ∀ tailValues tailErrors,
                  tail = .ok (tailValues, tailErrors)
                  -> FieldCacheSourcesAligned sourceRest tailValues :=
              completeValueList_sourcesAligned schema resolvers variableValues fuel
                itemType selectionSet sourceRest []
                (FieldCacheSourcesPrefixAligned.nil sourceRest)
            exact
              resultCombine_cons_sourcesAligned source sourceRest head tail
                hheadResultAligned htailAligned completedValues errors (by
                  simpa [completeValueList, head, tail] using hok)
    | @cons source previous sourceRest previousRest hheadAligned hrestAligned =>
        let tail : Result (List (FieldCacheValue ObjectRef)) :=
          completeValueList schema resolvers variableValues fuel itemType
            selectionSet sourceRest previousRest
        have htailAligned :
            ∀ tailValues tailErrors,
              tail = .ok (tailValues, tailErrors)
              -> FieldCacheSourcesAligned sourceRest tailValues :=
          completeValueList_sourcesAligned schema resolvers variableValues fuel
            itemType selectionSet sourceRest previousRest hrestAligned
        cases previous with
        | null =>
            let head : Result (FieldCacheValue ObjectRef) := .ok (.null, 0)
            exact
              resultCombine_cons_sourcesAligned source sourceRest head tail
                (FieldCacheSourceAligned.null source) htailAligned completedValues
                errors (by
                  simpa [completeValueList, head, tail] using hok)
        | scalar previousValue =>
            let head : Result (FieldCacheValue ObjectRef) :=
              completeValue schema resolvers variableValues fuel itemType
                selectionSet source (some (.scalar previousValue))
            have hheadResultAligned :
                FieldCacheSourceAligned source (resultValueOrNull head) :=
              completeValue_sourceAligned schema resolvers variableValues fuel
                itemType selectionSet source (some (.scalar previousValue))
                (by intro cached h; cases h; exact hheadAligned)
            exact
              resultCombine_cons_sourcesAligned source sourceRest head tail
                hheadResultAligned htailAligned completedValues errors (by
                  simpa [completeValueList, head, tail] using hok)
        | object previousSource fields =>
            let head : Result (FieldCacheValue ObjectRef) :=
              completeValue schema resolvers variableValues fuel itemType
                selectionSet source (some (.object previousSource fields))
            have hheadResultAligned :
                FieldCacheSourceAligned source (resultValueOrNull head) :=
              completeValue_sourceAligned schema resolvers variableValues fuel
                itemType selectionSet source (some (.object previousSource fields))
                (by intro cached h; cases h; exact hheadAligned)
            exact
              resultCombine_cons_sourcesAligned source sourceRest head tail
                hheadResultAligned htailAligned completedValues errors (by
                  simpa [completeValueList, head, tail] using hok)
        | list sourceValues? values =>
            let head : Result (FieldCacheValue ObjectRef) :=
              completeValue schema resolvers variableValues fuel itemType
                selectionSet source (some (.list sourceValues? values))
            have hheadResultAligned :
                FieldCacheSourceAligned source (resultValueOrNull head) :=
              completeValue_sourceAligned schema resolvers variableValues fuel
                itemType selectionSet source (some (.list sourceValues? values))
                (by intro cached h; cases h; exact hheadAligned)
            exact
              resultCombine_cons_sourcesAligned source sourceRest head tail
                hheadResultAligned htailAligned completedValues errors (by
                  simpa [completeValueList, head, tail] using hok)
  termination_by values previousValues _hprevious completedValues errors _hok =>
    (fuel, sizeOf itemType, sizeOf values)
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

theorem resultValueOrNull_nonNullCompletion_cacheAbsorptionShape
    {ObjectRef : Type} (previous : FieldCacheValue ObjectRef)
    (completed : Result (FieldCacheValue ObjectRef))
    : FieldCacheAbsorptionShape previous (resultValueOrNull completed)
      -> FieldCacheAbsorptionShape previous
          (resultValueOrNull (nonNullCompletion completed)) := by
  intro hshape
  cases completed with
  | error errors =>
      simpa [resultValueOrNull, nonNullCompletion] using hshape
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value <;>
        simpa [resultValueOrNull, nonNullCompletion] using hshape

mutual
  theorem completeValue_cacheAbsorptionShape {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : ∀ fuel fieldType selectionSet value previous,
          FieldCacheMergeReady previous
          -> FieldCacheSourceAligned value previous
          -> FieldCacheAbsorptionShape previous
              (resultValueOrNull
                (completeValue schema resolvers variableValues fuel fieldType
                  selectionSet value (some previous))) := by
    intro fuel fieldType selectionSet value previous hpreviousReady haligned
    cases fuel with
    | zero =>
        simp [completeValue, resultValueOrNull]
        exact FieldCacheAbsorptionShape.toNull previous
    | succ completionFuel =>
        cases previous with
        | null =>
            simp [completeValue, resultValueOrNull]
            exact FieldCacheAbsorptionShape.null
        | scalar previousValue =>
            simp [completeValue, resultValueOrNull]
            exact FieldCacheAbsorptionShape.toNull (.scalar previousValue)
        | object previousSource previousFields =>
            cases haligned with
            | object _source _fields =>
                cases fieldType with
                | nonNull inner =>
                    simpa [completeValue] using
                      resultValueOrNull_nonNullCompletion_cacheAbsorptionShape
                        (.object value previousFields)
                        (completeValue schema resolvers variableValues
                          (completionFuel + 1) inner selectionSet value
                          (some (.object value previousFields)))
                        (completeValue_cacheAbsorptionShape schema resolvers
                          variableValues (completionFuel + 1) inner selectionSet
                          value (.object value previousFields) hpreviousReady
                          (FieldCacheSourceAligned.object value previousFields))
                | named typeName =>
                    cases value with
                    | object runtimeType ref =>
                        by_cases hinclude :
                            schema.typeIncludesObjectBool typeName runtimeType = true
                        · let visited :=
                            visitSubfields schema resolvers variableValues
                              completionFuel runtimeType (.object runtimeType ref)
                              selectionSet
                              (.object (.object runtimeType ref) previousFields)
                          have hvisitShape :
                              FieldCacheAbsorptionShape
                                (.object (.object runtimeType ref) previousFields)
                                visited.value :=
                            visitSubfields_cacheAbsorptionShape schema resolvers
                              variableValues completionFuel runtimeType
                              (.object runtimeType ref) selectionSet
                              (.object (.object runtimeType ref) previousFields)
                              hpreviousReady
                          cases hstatus : visited.status with
                          | error errors =>
                              simp [completeValue, hinclude, reuseOrCreateObject?,
                                visited, hstatus, catchVisitBubbleAsNull,
                                resultValueOrNull]
                              exact
                                FieldCacheAbsorptionShape.toNull
                                  (.object (.object runtimeType ref) previousFields)
                          | ok ok =>
                              rcases ok with ⟨_unit, errors⟩
                              simpa [completeValue, hinclude,
                                reuseOrCreateObject?, visited, hstatus,
                                catchVisitBubbleAsNull, resultValueOrNull] using
                                hvisitShape
                        · have hfalse :
                              schema.typeIncludesObjectBool typeName runtimeType =
                                false := by
                            cases h :
                                schema.typeIncludesObjectBool typeName runtimeType
                            · rfl
                            · contradiction
                          simp [completeValue, hfalse, resultValueOrNull]
                          exact
                            FieldCacheAbsorptionShape.toNull
                              (.object (.object runtimeType ref) previousFields)
                    | null =>
                        simp [completeValue, resultValueOrNull]
                        exact
                          FieldCacheAbsorptionShape.toNull
                            (.object .null previousFields)
                    | scalar scalarValue =>
                        simp [completeValue, resultValueOrNull]
                        exact
                          FieldCacheAbsorptionShape.toNull
                            (.object (.scalar scalarValue) previousFields)
                    | list values =>
                        simp [completeValue, resultValueOrNull]
                        exact
                          FieldCacheAbsorptionShape.toNull
                            (.object (.list values) previousFields)
                | list inner =>
                    cases value <;>
                      simp [completeValue, reuseOrCreateList?,
                        resultValueOrNull] <;>
                      apply FieldCacheAbsorptionShape.toNull
        | list sourceValues? previousValues =>
            cases haligned with
            | cachedList sourceValues _ halignedValues =>
                cases fieldType with
                | nonNull inner =>
                    simpa [completeValue] using
                      resultValueOrNull_nonNullCompletion_cacheAbsorptionShape
                        (.list (some sourceValues) previousValues)
                        (completeValue schema resolvers variableValues
                          (completionFuel + 1) inner selectionSet
                          (.list sourceValues)
                          (some (.list (some sourceValues) previousValues)))
                        (completeValue_cacheAbsorptionShape schema resolvers
                          variableValues (completionFuel + 1) inner selectionSet
                          (.list sourceValues)
                          (.list (some sourceValues) previousValues) hpreviousReady
                          (FieldCacheSourceAligned.cachedList sourceValues
                            previousValues halignedValues))
                | named typeName =>
                    simp [completeValue, resultValueOrNull]
                    exact
                      FieldCacheAbsorptionShape.toNull
                        (.list (some sourceValues) previousValues)
                | list inner =>
                    generalize hcompleted :
                      completeValueList schema resolvers variableValues
                          completionFuel inner selectionSet sourceValues
                          previousValues
                        = completed
                    cases completed with
                    | error errors =>
                        simp [completeValue, reuseOrCreateList?, hcompleted,
                          catchBubbleAsNull, resultValueOrNull]
                        exact
                          FieldCacheAbsorptionShape.toNull
                            (.list (some sourceValues) previousValues)
                    | ok result =>
                        rcases result with ⟨completedValues, errors⟩
                        have hvaluesShape :=
                          completeValueList_cacheAbsorptionShape schema resolvers
                            variableValues completionFuel inner selectionSet
                            sourceValues previousValues (some sourceValues)
                            halignedValues hpreviousReady completedValues errors
                            hcompleted
                        simp [completeValue, reuseOrCreateList?, hcompleted,
                          catchBubbleAsNull, resultValueOrNull]
                        exact FieldCacheAbsorptionShape.list hvaluesShape
            | finalList sourceValues _ halignedValues =>
                cases fieldType with
                | nonNull inner =>
                    simpa [completeValue] using
                      resultValueOrNull_nonNullCompletion_cacheAbsorptionShape
                        (.list none previousValues)
                        (completeValue schema resolvers variableValues
                          (completionFuel + 1) inner selectionSet
                          (.list sourceValues)
                          (some (.list none previousValues)))
                        (completeValue_cacheAbsorptionShape schema resolvers
                          variableValues (completionFuel + 1) inner selectionSet
                          (.list sourceValues) (.list none previousValues)
                          hpreviousReady
                          (FieldCacheSourceAligned.finalList sourceValues
                            previousValues halignedValues))
                | named typeName =>
                    simp [completeValue, resultValueOrNull]
                    exact
                      FieldCacheAbsorptionShape.toNull
                        (.list none previousValues)
                | list inner =>
                    generalize hcompleted :
                      completeValueList schema resolvers variableValues
                          completionFuel inner selectionSet sourceValues
                          previousValues
                        = completed
                    cases completed with
                    | error errors =>
                        simp [completeValue, reuseOrCreateList?, hcompleted,
                          catchBubbleAsNull, resultValueOrNull]
                        exact
                          FieldCacheAbsorptionShape.toNull
                            (.list none previousValues)
                    | ok result =>
                        rcases result with ⟨completedValues, errors⟩
                        have hvaluesShape :=
                          completeValueList_cacheAbsorptionShape schema resolvers
                            variableValues completionFuel inner selectionSet
                            sourceValues previousValues none halignedValues
                            hpreviousReady completedValues errors hcompleted
                        simp [completeValue, reuseOrCreateList?, hcompleted,
                          catchBubbleAsNull, resultValueOrNull]
                        exact FieldCacheAbsorptionShape.list hvaluesShape
  termination_by fuel fieldType _selectionSet value previous =>
    (fuel, 0, sizeOf fieldType, sizeOf value + sizeOf previous)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem completeValueList_cacheAbsorptionShape {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (itemType : TypeRef) (selectionSet : List Selection)
      : ∀ values previousValues sourceValues?,
          FieldCacheSourcesAligned values previousValues
          -> FieldCacheMergeReady (.list sourceValues? previousValues)
          -> ∀ completedValues errors,
              completeValueList schema resolvers variableValues fuel itemType
                  selectionSet values previousValues
                = .ok (completedValues, errors)
              -> FieldCacheListAbsorptionShape sourceValues? previousValues
                  completedValues := by
    intro values previousValues sourceValues? haligned hpreviousReady
      completedValues errors hok
    cases haligned with
    | nil =>
        simp [completeValueList] at hok
        rcases hok with ⟨hcompletedValues, _herrors⟩
        subst completedValues
        exact FieldCacheListAbsorptionShape.nil
    | @cons source previous sourceRest previousRest hheadAligned hrestAligned =>
        let head : Result (FieldCacheValue ObjectRef) :=
          match (previous :: previousRest).head? with
          | some .null => .ok (.null, 0)
          | _ =>
              completeValue schema resolvers variableValues fuel itemType
                selectionSet source (some previous)
        let tail : Result (List (FieldCacheValue ObjectRef)) :=
          completeValueList schema resolvers variableValues fuel itemType
            selectionSet sourceRest (previous :: previousRest).tail
        have hcombine :
            Result.combine List.cons head tail = .ok (completedValues, errors) := by
          rw [completeValueList.eq_3] at hok
          change Result.combine List.cons head tail = .ok (completedValues, errors)
            at hok
          exact hok
        have hpreviousHeadReady : FieldCacheMergeReady previous :=
          FieldCacheMergeReady.list_value sourceValues?
            (previous :: previousRest) previous hpreviousReady (by simp)
        have hpreviousRestReady :
            FieldCacheMergeReady (.list sourceValues? previousRest) :=
          FieldCacheMergeReady.list sourceValues? previousRest (by
            intro response hmem
            exact
              FieldCacheMergeReady.list_value sourceValues?
                (previous :: previousRest) response hpreviousReady
                (by simp [hmem]))
        have hheadShape :
            FieldCacheAbsorptionShape previous (resultValueOrNull head) := by
          cases previous with
          | null => exact FieldCacheAbsorptionShape.null
          | scalar previousValue =>
              exact
                completeValue_cacheAbsorptionShape schema resolvers variableValues
                  fuel itemType selectionSet source (.scalar previousValue)
                  hpreviousHeadReady hheadAligned
          | object previousSource fields =>
              exact
                completeValue_cacheAbsorptionShape schema resolvers variableValues
                  fuel itemType selectionSet source
                  (.object previousSource fields) hpreviousHeadReady hheadAligned
          | list previousSourceValues? previousListValues =>
              exact
                completeValue_cacheAbsorptionShape schema resolvers variableValues
                  fuel itemType selectionSet source
                  (.list previousSourceValues? previousListValues)
                  hpreviousHeadReady hheadAligned
        cases hheadResult : head with
        | error headErrors =>
            cases htailResult : tail <;>
              simp [hheadResult, htailResult,
                GraphQL.Execution.Result.combine] at hcombine
        | ok headResult =>
            rcases headResult with ⟨headValue, headErrors⟩
            cases htailResult : tail with
            | error tailErrors =>
                simp [hheadResult, htailResult,
                  GraphQL.Execution.Result.combine] at hcombine
            | ok tailResult =>
                rcases tailResult with ⟨tailValues, tailErrors⟩
                simp [hheadResult, htailResult,
                  GraphQL.Execution.Result.combine] at hcombine
                rcases hcombine with ⟨hcompletedValues, herrors⟩
                subst completedValues
                subst errors
                have htailShape :=
                  completeValueList_cacheAbsorptionShape schema resolvers
                    variableValues fuel itemType selectionSet sourceRest
                    previousRest sourceValues? hrestAligned hpreviousRestReady
                    tailValues tailErrors (by simpa [tail] using htailResult)
                have hcompletedReady :
                    FieldCacheMergeReady
                      (.list sourceValues? (headValue :: tailValues)) :=
                  FieldCacheMergeReady.list sourceValues? (headValue :: tailValues)
                    (completeValueList_values_cacheReady schema resolvers
                      variableValues fuel itemType selectionSet
                      (source :: sourceRest) (previous :: previousRest)
                      (by
                        intro cached hmem
                        exact
                          FieldCacheMergeReady.list_value sourceValues?
                            (previous :: previousRest) cached hpreviousReady hmem)
                      (headValue :: tailValues) (headErrors + tailErrors) (by
                        exact hok))
                exact
                  FieldCacheListAbsorptionShape.cons hcompletedReady
                    (by simpa [hheadResult, resultValueOrNull] using hheadShape)
                    htailShape
  termination_by values previousValues _sourceValues? _haligned _hpreviousReady
      completedValues errors _hok =>
    (fuel, 2, sizeOf itemType, sizeOf values + sizeOf previousValues)
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
