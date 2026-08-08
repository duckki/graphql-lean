import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldGroup.SingleField

/-!
Prefix append-one helpers for field-group equivalence.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

attribute [local simp] TypeRef.namedType

local instance fieldGroupPrefixAppendResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem ExecutableFieldsMergedRaw_append_one_of_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw
      : ExecutableFieldsMergedRaw schema resolvers variableValues depth
          parentType source responseName field fields resolved)
    (hprefixResponses
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups
      : ∀ candidate,
          candidate ∈ fields ++ [later]
          -> ∃ fieldDefinition,
              schema.lookupField parentType candidate.fieldName = some fieldDefinition)
    (hresolveFirst
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hresolveLater
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: fields)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: fields) ++ [later])
                  }
                initial := .object []
              })
    : ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field (fields ++ [later]) resolved := by
  unfold ExecutableFieldsMergedRaw at hprefixRaw ⊢
  cases depth with
  | zero =>
      have hextendedResponses :
          ∀ candidate, candidate ∈ field :: (fields ++ [later]) ->
            candidate.responseName = responseName := by
        intro candidate hmem
        simp at hmem
        rcases hmem with hhead | htail
        · subst candidate
          exact hfieldResponse
        · rcases htail with hprefix | hlater
          · exact hprefixResponses candidate (by simp [hprefix])
          · subst candidate
            exact hlaterResponse
      have hextendedVisit :
          visitSubfields schema resolvers variableValues 1 parentType source
            (executableFieldSelections (field :: (fields ++ [later])))
            (.object []) =
          let fieldResult :=
            executeField schema resolvers variableValues 0 source none
              (executableField parentType responseName field.fieldName
                field.arguments field.selectionSet)
          (.object [(responseName, .null)], resultStatus fieldResult) :=
        visitSubfields_executableFieldSelections_completion_zero_same_response_fresh
          schema resolvers variableValues parentType source responseName field
          (fields ++ [later]) [] hextendedResponses htailLookups (by simp)
      rw [hextendedVisit]
      cases field with
      | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
          dsimp at hfieldResponse hfieldParent hresolveFirst ⊢
          subst fieldResponseName
          subst fieldParent
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [GraphQL.Execution.executeField, executeField, groupedFieldVisitResult, executableField, hlookup, resultStatus]
          | some fieldDefinition =>
              cases resolved with
              | none =>
                  cases fieldDefinition with
                  | mk definitionName outputType definitionArguments =>
                      cases outputType <;>
                        simp [GraphQL.Execution.executeField, executeField, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, executableField, hlookup, hresolveFirst, reusablePreviousValue?, handleFieldError, resultStatus, visitOk]
              | some resolvedValue =>
                  simp [GraphQL.Execution.executeField, executeField, GraphQL.Execution.completeValue, completeValue, outOfFuel, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, executableField, hlookup, hresolveFirst, reusablePreviousValue?, resultStatus]
  | succ childDepth =>
      cases field with
      | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
          cases later with
          | mk laterParent laterResponseName laterFieldName laterArguments
              laterSelectionSet =>
              dsimp at hfieldResponse hlaterResponse hfieldParent
              dsimp at hlaterParent hfieldName hresolveFirst hresolveLater
              dsimp at hprefixResponses hprefixChildren hobjects herrors
              dsimp at hchildren hprefixRaw ⊢
              subst fieldResponseName
              subst laterResponseName
              subst fieldParent
              subst laterParent
              subst laterFieldName
              have hselectionAppend :
                  executableFieldSelections
                      ({ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := arguments
                         selectionSet := selectionSet } ::
                        (fields ++
                          [{ parentType := parentType
                             responseName := responseName
                             fieldName := fieldName
                             arguments := laterArguments
                             selectionSet := laterSelectionSet }])) =
                  executableFieldSelections
                      ({ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := arguments
                         selectionSet := selectionSet } ::
                        fields) ++
                  executableFieldSelections
                    [{ parentType := parentType
                       responseName := responseName
                       fieldName := fieldName
                       arguments := laterArguments
                       selectionSet := laterSelectionSet }] := by
                simp [executableFieldSelections]
              rw [hselectionAppend]
              rw [visitSubfields_append_equivalence schema resolvers
                variableValues (childDepth + 2) parentType source
                (executableFieldSelections
                  ({ parentType := parentType
                     responseName := responseName
                     fieldName := fieldName
                     arguments := arguments
                     selectionSet := selectionSet } ::
                    fields))
                (executableFieldSelections
                  [{ parentType := parentType
                     responseName := responseName
                     fieldName := fieldName
                     arguments := laterArguments
                     selectionSet := laterSelectionSet }])
                (.object [])]
              rw [hprefixRaw]
              have hlaterResponseAll :
                  ∀ (candidate : ExecutableField),
                    candidate ∈
                        ([{ parentType := parentType
                            responseName := responseName
                            fieldName := fieldName
                            arguments := laterArguments
                            selectionSet := laterSelectionSet }] :
                          List ExecutableField) ->
                      candidate.responseName = responseName := by
                intro candidate hmem
                simp at hmem
                subst candidate
                rfl
              have htailNull :
                  visitSubfields schema resolvers variableValues
                    (childDepth + 2) parentType source
                    (executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := laterArguments
                         selectionSet := laterSelectionSet }])
                    (.object [(responseName, .null)]) =
                  (.object [(responseName, .null)], visitOk) :=
                visitSubfields_executableFieldSelections_existing_null
                  schema resolvers variableValues (childDepth + 1)
                  parentType source responseName
                  [{ parentType := parentType
                     responseName := responseName
                     fieldName := fieldName
                     arguments := laterArguments
                     selectionSet := laterSelectionSet }]
                  [(responseName, .null)] hlaterResponseAll
                  (by
                    intro candidate hmem
                    simp at hmem
                    subst candidate
                    exact htailLookups
                      { parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := laterArguments
                        selectionSet := laterSelectionSet }
                      (by simp))
                  (by simp [responseObjectField?, lookupResponseField?])
              cases hlookup : schema.lookupField parentType fieldName with
              | none =>
                  simp [GraphQL.Execution.executeField, hlookup, groupedFieldVisitResult, htailNull, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk]
              | some fieldDefinition =>
                  cases resolved with
                  | none =>
                      cases fieldDefinition with
                      | mk definitionName outputType definitionArguments =>
                          cases outputType <;>
                            simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, handleFieldError, htailNull, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk]
                  | some resolvedValue =>
                      cases fieldDefinition with
                      | mk definitionName outputType definitionArguments =>
                          cases outputType with
                          | named typeName =>
                              cases resolvedValue with
                              | null =>
                                  simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk, GraphQL.Execution.completeValue, htailNull]
                              | scalar value =>
                                  by_cases hcomposite :
                                      (TypeRef.named typeName).isCompositeBool
                                          schema =
                                        true
                                  · simp [GraphQL.Execution.executeField, visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, executableField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, combineVisitStatus, GraphQL.Execution.Result.combine, resultStatus, visitOk, GraphQL.Execution.completeValue, reusablePreviousValue?, hcomposite]
                                  · simp [GraphQL.Execution.executeField, visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, executableField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, combineVisitStatus, GraphQL.Execution.Result.combine, resultStatus, visitOk, GraphQL.Execution.completeValue, reusablePreviousValue?, hcomposite]
                              | object runtimeType identity =>
                                  have hspecAppend :
                                      GraphQL.Execution.Result.combine
                                        mergeResponse
                                        (GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.named typeName)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          (.object runtimeType identity))
                                        (completeResolvedValue schema resolvers
                                          variableValues (childDepth + 1)
                                          (.named typeName)
                                          laterSelectionSet
                                          (.object runtimeType identity)
                                          (some (resultValueOrNull
                                            (GraphQL.Execution.completeValue
                                              schema resolvers variableValues
                                              (childDepth + 1)
                                              (.named typeName)
                                              ({ parentType := parentType
                                                 responseName := responseName
                                                 fieldName := fieldName
                                                 arguments := arguments
                                                 selectionSet := selectionSet } ::
                                                fields)
                                              (.object runtimeType identity))))) =
                                      GraphQL.Execution.completeValue
                                        schema resolvers variableValues
                                        (childDepth + 1) (.named typeName)
                                        ({ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := arguments
                                           selectionSet := selectionSet } ::
                                          (fields ++
                                            [{ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := laterArguments
                                               selectionSet :=
                                                 laterSelectionSet }]))
                                        (.object runtimeType identity) :=
                                    completeValue_named_group_append_one_result_eq_spec_of_contained
                                      schema resolvers variableValues
                                      (childDepth + 1) typeName
                                      (.object runtimeType identity)
                                      ({ parentType := parentType
                                         responseName := responseName
                                         fieldName := fieldName
                                         arguments := arguments
                                         selectionSet := selectionSet } ::
                                        fields)
                                      { parentType := parentType
                                        responseName := responseName
                                        fieldName := fieldName
                                        arguments := laterArguments
                                        selectionSet := laterSelectionSet }
                                      (by
                                        intro childDepth' runtimeType' identity'
                                          hlt hcontains hincludes
                                        exact hprefixChildren childDepth'
                                          runtimeType' identity' hlt
                                          (by simpa [resolvedValueOrNull] using
                                            hcontains)
                                          (by
                                            simpa [Schema.fieldReturnType?,
                                              hlookup] using hincludes))
                                      (by
                                        intro childDepth' runtimeType' identity'
                                          hlt hcontains
                                        exact hobjects childDepth'
                                          runtimeType' identity' hlt
                                          (by simpa [resolvedValueOrNull] using
                                            hcontains))
                                      (by
                                        intro childDepth' runtimeType' identity'
                                          hlt hcontains
                                        exact herrors childDepth'
                                          runtimeType' identity' hlt
                                          (by simpa [resolvedValueOrNull] using
                                            hcontains))
                                      (by
                                        intro childDepth' runtimeType' identity'
                                          hlt hcontains hincludes
                                        exact hchildren childDepth'
                                          runtimeType' identity' hlt
                                          (by simpa [resolvedValueOrNull] using
                                            hcontains)
                                          (by
                                            simpa [Schema.fieldReturnType?,
                                              hlookup] using hincludes))
                                  have hprefixLocal :
                                      completeValue schema resolvers
                                        variableValues (childDepth + 1)
                                        (.named typeName)
                                        (GraphQL.Execution.mergedFieldSelectionSet
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                        fields))
                                        (.object runtimeType identity)
                                        none =
                                      GraphQL.Execution.completeValue
                                        schema resolvers variableValues
                                        (childDepth + 1) (.named typeName)
                                        ({ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := arguments
                                           selectionSet := selectionSet } ::
                                          fields)
                                        (.object runtimeType identity) :=
                                    completeValue_group_eq_spec_of_contained_child_states
                                      schema resolvers variableValues
                                      ({ parentType := parentType
                                         responseName := responseName
                                         fieldName := fieldName
                                         arguments := arguments
                                         selectionSet := selectionSet } ::
                                        fields)
                                      (childDepth + 1) typeName
                                      (.object runtimeType identity)
                                      (by
                                        intro childDepth' runtimeType' identity'
                                          hlt hcontains hincludes
                                        exact hprefixChildren childDepth'
                                          runtimeType' identity' hlt
                                          (by simpa [resolvedValueOrNull] using
                                            hcontains)
                                          (by
                                            simpa [Schema.fieldReturnType?,
                                              hlookup] using hincludes))
                                  have hrightNeutral :
                                      resultStatus
                                        (completeResolvedValue schema resolvers
                                          variableValues (childDepth + 1)
                                          (.named typeName)
                                          laterSelectionSet
                                          (.object runtimeType identity)
                                          (some (resultValueOrNull
                                            (GraphQL.Execution.completeValue
                                              schema resolvers variableValues
                                              (childDepth + 1)
                                              (.named typeName)
                                              ({ parentType := parentType
                                                 responseName := responseName
                                                 fieldName := fieldName
                                                 arguments := arguments
                                                 selectionSet := selectionSet } ::
                                                fields)
                                              (.object runtimeType identity))))) =
                                        visitOk := by
                                    by_cases hincludes :
                                        schema.typeIncludesObjectBool typeName
                                          runtimeType = true
                                    · have hrightLocal :=
                                        resultStatus_completeValue_object_append_second_of_errorNeutral
                                          schema resolvers variableValues
                                          childDepth typeName runtimeType
                                          identity
                                          (GraphQL.Execution.mergedFieldSelectionSet
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                              fields))
                                          laterSelectionSet hincludes
                                          (herrors childDepth runtimeType
                                            identity
                                            (Nat.lt_succ_self childDepth)
                                            (by
                                              simp [resolvedValueOrNull,
                                                ValueContainsObject.here]))
                                      dsimp at hrightLocal
                                      rw [hprefixLocal] at hrightLocal
                                      exact hrightLocal
                                    · have hnotIncludes :
                                          schema.typeIncludesObjectBool
                                            typeName runtimeType = false := by
                                        cases h :
                                            schema.typeIncludesObjectBool
                                              typeName runtimeType <;>
                                          simp [h] at hincludes ⊢
                                      simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hnotIncludes, resultValueOrNull, resultStatus, visitOk]
                                  have htailVisit :
                                      visitSubfields schema resolvers
                                        variableValues (childDepth + 2)
                                        parentType source
                                        (executableFieldSelections
                                          [{ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := laterArguments
                                             selectionSet :=
                                               laterSelectionSet }])
                                        (groupedFieldVisitResult responseName
                                          (GraphQL.Execution.singleFieldResult
                                            responseName
                                            (GraphQL.Execution.completeValue
                                              schema resolvers variableValues
                                              (childDepth + 1)
                                              (.named typeName)
                                              ({ parentType := parentType
                                                 responseName := responseName
                                                 fieldName := fieldName
                                                 arguments := arguments
                                                 selectionSet := selectionSet } ::
                                                fields)
                                              (.object runtimeType identity)))).fst =
                                      mergeResponseFieldResult responseName
                                        (completeResolvedValue schema resolvers
                                          variableValues (childDepth + 1)
                                          (.named typeName)
                                          laterSelectionSet
                                          (.object runtimeType identity)
                                          (some (resultValueOrNull
                                            (GraphQL.Execution.completeValue
                                              schema resolvers variableValues
                                              (childDepth + 1)
                                              (.named typeName)
                                              ({ parentType := parentType
                                                 responseName := responseName
                                                 fieldName := fieldName
                                                 arguments := arguments
                                                 selectionSet := selectionSet } ::
                                                fields)
                                              (.object runtimeType identity)))))
                                        (groupedFieldVisitResult responseName
                                          (GraphQL.Execution.singleFieldResult
                                            responseName
                                            (GraphQL.Execution.completeValue
                                              schema resolvers variableValues
                                              (childDepth + 1)
                                              (.named typeName)
                                              ({ parentType := parentType
                                                 responseName := responseName
                                                 fieldName := fieldName
                                                 arguments := arguments
                                                 selectionSet := selectionSet } ::
                                                fields)
                                              (.object runtimeType identity)))).fst := by
                                    cases hprefixCompleted
                                          : GraphQL.Execution.completeValue
                                              schema resolvers variableValues
                                              (childDepth + 1) (.named typeName)
                                              ({
                                                  parentType := parentType
                                                  responseName := responseName
                                                  fieldName := fieldName
                                                  arguments := arguments
                                                  selectionSet := selectionSet
                                                }
                                                :: fields)
                                              (.object runtimeType identity) with
                                    | error prefixErrors =>
                                        simp [groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, htailNull, completeResolvedValue_previous_null, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, resultStatus, visitOk]
                                    | ok prefixResult =>
                                        rcases prefixResult with
                                          ⟨prefixValue, prefixErrors⟩
                                        have hlaterVisit :=
                                          visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
                                            schema resolvers variableValues
                                            childDepth parentType
                                            source responseName fieldName
                                            laterArguments laterSelectionSet
                                            { name := definitionName
                                              outputType := .named typeName
                                              arguments :=
                                                definitionArguments }
                                            (.object runtimeType identity)
                                            prefixValue hlookup
                                            hresolveLater
                                        simpa [hprefixCompleted,
                                          groupedFieldVisitResult,
                                          GraphQL.Execution.singleFieldResult,
                                          resultValueOrNull, Nat.add_assoc]
                                          using hlaterVisit
                                  have hcombined :=
                                    groupedFieldVisitResult_singleFieldResult_combine_neutral
                                      responseName
                                      (GraphQL.Execution.completeValue
                                        schema resolvers variableValues
                                        (childDepth + 1) (.named typeName)
                                        ({ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := arguments
                                           selectionSet := selectionSet } ::
                                          fields)
                                        (.object runtimeType identity))
                                      (completeResolvedValue schema resolvers
                                        variableValues (childDepth + 1)
                                        (.named typeName)
                                        laterSelectionSet
                                        (.object runtimeType identity)
                                        (some (resultValueOrNull
                                          (GraphQL.Execution.completeValue
                                            schema resolvers variableValues
                                            (childDepth + 1)
                                            (.named typeName)
                                            ({ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := arguments
                                               selectionSet := selectionSet } ::
                                              fields)
                                            (.object runtimeType identity)))))
                                      (GraphQL.Execution.completeValue
                                        schema resolvers variableValues
                                        (childDepth + 1) (.named typeName)
                                        ({ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := arguments
                                           selectionSet := selectionSet } ::
                                          (fields ++
                                            [{ parentType := parentType
                                               responseName := responseName
                                               fieldName := fieldName
                                               arguments := laterArguments
                                               selectionSet :=
                                                 laterSelectionSet }]))
                                        (.object runtimeType identity))
                                      hrightNeutral hspecAppend
                                  simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult] at htailVisit hcombined ⊢
                                  rw [htailVisit]
                                  exact hcombined
                              | list values =>
                                  simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk, GraphQL.Execution.completeValue, htailNull]
                          | list inner =>
                              have happend :=
                                completeValue_group_append_one_result_eq_spec_and_status
                                  schema resolvers variableValues (.list inner)
                                  (childDepth + 1) resolvedValue
                                  ({ parentType := parentType
                                     responseName := responseName
                                     fieldName := fieldName
                                     arguments := arguments
                                     selectionSet := selectionSet } ::
                                    fields)
                                  { parentType := parentType
                                    responseName := responseName
                                    fieldName := fieldName
                                    arguments := laterArguments
                                    selectionSet := laterSelectionSet }
                                  (by
                                    intro childDepth' runtimeType' identity'
                                      hlt hcontains hincludes
                                    exact hprefixChildren childDepth'
                                      runtimeType' identity' hlt
                                      (by simpa [resolvedValueOrNull] using
                                        hcontains)
                                      (by
                                        simpa [Schema.fieldReturnType?,
                                          hlookup] using hincludes))
                                  (by
                                    intro childDepth' runtimeType' identity'
                                      hlt hcontains
                                    exact hobjects childDepth' runtimeType'
                                      identity' hlt
                                      (by simpa [resolvedValueOrNull] using
                                        hcontains))
                                  (by
                                    intro childDepth' runtimeType' identity'
                                      hlt hcontains
                                    exact herrors childDepth' runtimeType'
                                      identity' hlt
                                      (by simpa [resolvedValueOrNull] using
                                        hcontains))
                                  (by
                                    intro childDepth' runtimeType' identity'
                                      hlt hcontains hincludes
                                    exact hchildren childDepth' runtimeType'
                                      identity' hlt
                                      (by simpa [resolvedValueOrNull] using
                                        hcontains)
                                      (by
                                        simpa [Schema.fieldReturnType?,
                                          hlookup] using hincludes))
                              have hspecAppend := happend.left
                              have hrightNeutral := happend.right.left
                              have htailVisit :
                                  visitSubfields schema resolvers
                                    variableValues (childDepth + 2)
                                    parentType source
                                    (executableFieldSelections
                                      [{ parentType := parentType
                                         responseName := responseName
                                         fieldName := fieldName
                                         arguments := laterArguments
                                         selectionSet := laterSelectionSet }])
                                    (groupedFieldVisitResult responseName
                                      (GraphQL.Execution.singleFieldResult
                                        responseName
                                        (GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.list inner)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          resolvedValue))).fst =
                                  mergeResponseFieldResult responseName
                                    (completeResolvedValue schema resolvers
                                      variableValues (childDepth + 1)
                                      (.list inner) laterSelectionSet
                                      resolvedValue
                                      (some (resultValueOrNull
                                        (GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.list inner)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          resolvedValue))))
                                    (groupedFieldVisitResult responseName
                                      (GraphQL.Execution.singleFieldResult
                                        responseName
                                        (GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.list inner)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          resolvedValue))).fst := by
                                cases hprefixCompleted
                                      : GraphQL.Execution.completeValue schema
                                          resolvers variableValues
                                          (childDepth + 1) (.list inner)
                                          ({
                                              parentType := parentType
                                              responseName := responseName
                                              fieldName := fieldName
                                              arguments := arguments
                                              selectionSet := selectionSet
                                            }
                                            :: fields)
                                          resolvedValue with
                                | error prefixErrors =>
                                    simp [groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, htailNull, completeResolvedValue_previous_null, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, resultStatus, visitOk]
                                | ok prefixResult =>
                                    rcases prefixResult with
                                      ⟨prefixValue, prefixErrors⟩
                                    have hlaterVisit :=
                                      visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
                                        schema resolvers variableValues
                                        childDepth parentType source
                                        responseName fieldName laterArguments
                                        laterSelectionSet
                                        { name := definitionName
                                          outputType := .list inner
                                          arguments := definitionArguments }
                                        resolvedValue prefixValue hlookup
                                        hresolveLater
                                    simpa [hprefixCompleted,
                                      groupedFieldVisitResult,
                                      GraphQL.Execution.singleFieldResult,
                                      resultValueOrNull, Nat.add_assoc]
                                      using hlaterVisit
                              have hcombined :=
                                groupedFieldVisitResult_singleFieldResult_combine_neutral
                                  responseName
                                  (GraphQL.Execution.completeValue schema
                                    resolvers variableValues (childDepth + 1)
                                    (.list inner)
                                    ({ parentType := parentType
                                       responseName := responseName
                                       fieldName := fieldName
                                       arguments := arguments
                                       selectionSet := selectionSet } ::
                                      fields)
                                    resolvedValue)
                                  (completeResolvedValue schema resolvers
                                    variableValues (childDepth + 1)
                                    (.list inner) laterSelectionSet
                                    resolvedValue
                                    (some (resultValueOrNull
                                      (GraphQL.Execution.completeValue schema
                                        resolvers variableValues
                                        (childDepth + 1) (.list inner)
                                        ({ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := arguments
                                           selectionSet := selectionSet } ::
                                          fields)
                                        resolvedValue))))
                                  (GraphQL.Execution.completeValue schema
                                    resolvers variableValues (childDepth + 1)
                                    (.list inner)
                                    (({ parentType := parentType
                                        responseName := responseName
                                        fieldName := fieldName
                                        arguments := arguments
                                        selectionSet := selectionSet } ::
                                       fields) ++
                                      [{ parentType := parentType
                                         responseName := responseName
                                         fieldName := fieldName
                                         arguments := laterArguments
                                         selectionSet :=
                                           laterSelectionSet }])
                                    resolvedValue)
                                  hrightNeutral hspecAppend
                              simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult]
                                at htailVisit hcombined ⊢
                              rw [htailVisit]
                              exact hcombined
                          | nonNull inner =>
                              have happend :=
                                completeValue_group_append_one_result_eq_spec_and_status
                                  schema resolvers variableValues
                                  (.nonNull inner) (childDepth + 1)
                                  resolvedValue
                                  ({ parentType := parentType
                                     responseName := responseName
                                     fieldName := fieldName
                                     arguments := arguments
                                     selectionSet := selectionSet } ::
                                    fields)
                                  { parentType := parentType
                                    responseName := responseName
                                    fieldName := fieldName
                                    arguments := laterArguments
                                    selectionSet := laterSelectionSet }
                                  (by
                                    intro childDepth' runtimeType' identity'
                                      hlt hcontains hincludes
                                    exact hprefixChildren childDepth'
                                      runtimeType' identity' hlt
                                      (by simpa [resolvedValueOrNull] using
                                        hcontains)
                                      (by
                                        simpa [Schema.fieldReturnType?,
                                          hlookup] using hincludes))
                                  (by
                                    intro childDepth' runtimeType' identity'
                                      hlt hcontains
                                    exact hobjects childDepth' runtimeType'
                                      identity' hlt
                                      (by simpa [resolvedValueOrNull] using
                                        hcontains))
                                  (by
                                    intro childDepth' runtimeType' identity'
                                      hlt hcontains
                                    exact herrors childDepth' runtimeType'
                                      identity' hlt
                                      (by simpa [resolvedValueOrNull] using
                                        hcontains))
                                  (by
                                    intro childDepth' runtimeType' identity'
                                      hlt hcontains hincludes
                                    exact hchildren childDepth' runtimeType'
                                      identity' hlt
                                      (by simpa [resolvedValueOrNull] using
                                        hcontains)
                                      (by
                                        simpa [Schema.fieldReturnType?,
                                          hlookup] using hincludes))
                              have hspecAppend := happend.left
                              have hrightNeutral := happend.right.left
                              have htailVisit :
                                  visitSubfields schema resolvers
                                    variableValues (childDepth + 2)
                                    parentType source
                                    (executableFieldSelections
                                      [{ parentType := parentType
                                         responseName := responseName
                                         fieldName := fieldName
                                         arguments := laterArguments
                                         selectionSet := laterSelectionSet }])
                                    (groupedFieldVisitResult responseName
                                      (GraphQL.Execution.singleFieldResult
                                        responseName
                                        (GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.nonNull inner)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          resolvedValue))).fst =
                                  mergeResponseFieldResult responseName
                                    (completeResolvedValue schema resolvers
                                      variableValues (childDepth + 1)
                                      (.nonNull inner) laterSelectionSet
                                      resolvedValue
                                      (some (resultValueOrNull
                                        (GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.nonNull inner)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          resolvedValue))))
                                    (groupedFieldVisitResult responseName
                                      (GraphQL.Execution.singleFieldResult
                                        responseName
                                        (GraphQL.Execution.completeValue
                                          schema resolvers variableValues
                                          (childDepth + 1) (.nonNull inner)
                                          ({ parentType := parentType
                                             responseName := responseName
                                             fieldName := fieldName
                                             arguments := arguments
                                             selectionSet := selectionSet } ::
                                            fields)
                                          resolvedValue))).fst := by
                                cases hprefixCompleted
                                      : GraphQL.Execution.completeValue schema
                                          resolvers variableValues
                                          (childDepth + 1) (.nonNull inner)
                                          ({
                                              parentType := parentType
                                              responseName := responseName
                                              fieldName := fieldName
                                              arguments := arguments
                                              selectionSet := selectionSet
                                            }
                                            :: fields)
                                          resolvedValue with
                                | error prefixErrors =>
                                    simp [groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, htailNull, completeResolvedValue_previous_null, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, resultStatus, visitOk]
                                | ok prefixResult =>
                                    rcases prefixResult with
                                      ⟨prefixValue, prefixErrors⟩
                                    have hlaterVisit :=
                                      visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
                                        schema resolvers variableValues
                                        childDepth parentType source
                                        responseName fieldName laterArguments
                                        laterSelectionSet
                                        { name := definitionName
                                          outputType := .nonNull inner
                                          arguments := definitionArguments }
                                        resolvedValue prefixValue hlookup
                                        hresolveLater
                                    simpa [hprefixCompleted,
                                      groupedFieldVisitResult,
                                      GraphQL.Execution.singleFieldResult,
                                      resultValueOrNull, Nat.add_assoc]
                                      using hlaterVisit
                              have hcombined :=
                                groupedFieldVisitResult_singleFieldResult_combine_neutral
                                  responseName
                                  (GraphQL.Execution.completeValue schema
                                    resolvers variableValues (childDepth + 1)
                                    (.nonNull inner)
                                    ({ parentType := parentType
                                       responseName := responseName
                                       fieldName := fieldName
                                       arguments := arguments
                                       selectionSet := selectionSet } ::
                                      fields)
                                    resolvedValue)
                                  (completeResolvedValue schema resolvers
                                    variableValues (childDepth + 1)
                                    (.nonNull inner) laterSelectionSet
                                    resolvedValue
                                    (some (resultValueOrNull
                                      (GraphQL.Execution.completeValue schema
                                        resolvers variableValues
                                        (childDepth + 1) (.nonNull inner)
                                        ({ parentType := parentType
                                           responseName := responseName
                                           fieldName := fieldName
                                           arguments := arguments
                                           selectionSet := selectionSet } ::
                                          fields)
                                        resolvedValue))))
                                  (GraphQL.Execution.completeValue schema
                                    resolvers variableValues (childDepth + 1)
                                    (.nonNull inner)
                                    (({ parentType := parentType
                                        responseName := responseName
                                        fieldName := fieldName
                                        arguments := arguments
                                        selectionSet := selectionSet } ::
                                       fields) ++
                                      [{ parentType := parentType
                                         responseName := responseName
                                         fieldName := fieldName
                                         arguments := laterArguments
                                         selectionSet :=
                                           laterSelectionSet }])
                                    resolvedValue)
                                  hrightNeutral hspecAppend
                              simp [GraphQL.Execution.executeField, hlookup, hresolveFirst, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult]
                                at htailVisit hcombined ⊢
                              rw [htailVisit]
                              exact hcombined

theorem ExecutableFieldsMergedRoot_append_one_aligned_of_prefix_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw
      : ExecutableFieldsMergedRaw schema resolvers variableValues depth
          parentType source responseName field fields resolved)
    (hprefixResponses
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups
      : ∀ candidate,
          candidate ∈ fields ++ [later]
          -> ∃ fieldDefinition,
              schema.lookupField parentType candidate.fieldName = some fieldDefinition)
    (hresolveFirst
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hresolveLater
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: fields)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object [])).fst
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                  (.object [])).fst).fst)
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: fields) ++ [later])
                  }
                initial := .object []
              })
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source
          (executableFieldSelections (field :: (fields ++ [later]))))
        (GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName (field :: (fields ++ [later]))) := by
  cases depth with
  | zero =>
      have hraw :
          ExecutableFieldsMergedRaw schema resolvers variableValues 0
            parentType source responseName field (fields ++ [later]) resolved := by
        apply ExecutableFieldsMergedRaw_append_one_of_prefix schema resolvers
          variableValues 0 parentType source responseName field fields later
          resolved hprefixRaw hprefixResponses hfieldResponse hlaterResponse
          hfieldParent hlaterParent hfieldName htailLookups hresolveFirst
          hresolveLater
        · intro childDepth runtimeType identity hlt hcontains hincludes
          exact False.elim (Nat.not_lt_zero childDepth hlt)
        · intro childDepth runtimeType identity hlt hcontains
          exact False.elim (Nat.not_lt_zero childDepth hlt)
        · intro childDepth runtimeType identity hlt hcontains
          exact False.elim (Nat.not_lt_zero childDepth hlt)
        · intro childDepth runtimeType identity hlt hcontains hincludes
          exact False.elim (Nat.not_lt_zero childDepth hlt)
      exact
        RootSelectionResultAlignedEquivalent.of_eq
          (ExecutableFieldsMergedResponse_of_raw schema resolvers variableValues
            0 parentType source responseName field (fields ++ [later])
            resolved hraw)
  | succ completionDepth =>
      cases field with
      | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
          cases later with
          | mk laterParent laterResponseName laterFieldName laterArguments
              laterSelectionSet =>
              dsimp at hfieldResponse hlaterResponse hfieldParent
              dsimp at hlaterParent hfieldName hresolveFirst hresolveLater
              dsimp at hprefixResponses hprefixChildren hobjects
              dsimp at hchildren hprefixRaw ⊢
              subst fieldResponseName
              subst laterResponseName
              subst fieldParent
              subst laterParent
              subst laterFieldName
              have hlaterResponseAll :
                  ∀ (candidate : ExecutableField),
                    candidate ∈
                        ([{ parentType := parentType
                            responseName := responseName
                            fieldName := fieldName
                            arguments := laterArguments
                            selectionSet := laterSelectionSet }] :
                          List ExecutableField) ->
                      candidate.responseName = responseName := by
                intro candidate hmem
                simp at hmem
                subst candidate
                rfl
              have htailNull :
                  visitSubfields schema resolvers variableValues
                    (completionDepth + 2) parentType source
                    (executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := laterArguments
                         selectionSet := laterSelectionSet }])
                    (.object [(responseName, .null)]) =
                  (.object [(responseName, .null)], visitOk) :=
                visitSubfields_executableFieldSelections_existing_null
                  schema resolvers variableValues (completionDepth + 1)
                  parentType source responseName
                  [{ parentType := parentType
                     responseName := responseName
                     fieldName := fieldName
                     arguments := laterArguments
                     selectionSet := laterSelectionSet }]
                  [(responseName, .null)] hlaterResponseAll
                  (by
                    intro candidate hmem
                    simp at hmem
                    subst candidate
                    exact htailLookups
                      { parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := laterArguments
                        selectionSet := laterSelectionSet }
                      (by simp))
                  (by simp [responseObjectField?, lookupResponseField?])
              cases hlookup : schema.lookupField parentType fieldName with
              | none =>
                  unfold ExecutableFieldsMergedRaw at hprefixRaw
                  unfold executeRootSelectionSet
                  rw [show executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          (fields ++
                            [{ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := laterArguments
                               selectionSet := laterSelectionSet }])) =
                      executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields) ++
                      executableFieldSelections
                        [{ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := laterArguments
                           selectionSet := laterSelectionSet }] by
                    simp [executableFieldSelections, List.map_append]]
                  rw [visitSubfields_append_equivalence schema resolvers
                    variableValues (completionDepth + 2) parentType source
                    (executableFieldSelections
                      ({ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := arguments
                         selectionSet := selectionSet } ::
                        fields))
                    (executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := laterArguments
                         selectionSet := laterSelectionSet }])
                    (.object [])]
                  rw [hprefixRaw]
                  simp [GraphQL.Execution.executeField, hlookup, htailNull,
                    groupedFieldVisitResult, combineVisitStatus,
                    GraphQL.Execution.Result.combine, visitOk,
                    RootSelectionResultAlignedEquivalent,
                    ErrorPresenceEquivalent]
              | some fieldDefinition =>
                  cases resolved with
                  | none =>
                      unfold ExecutableFieldsMergedRaw at hprefixRaw
                      unfold executeRootSelectionSet
                      rw [show executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              (fields ++
                                [{ parentType := parentType
                                   responseName := responseName
                                   fieldName := fieldName
                                   arguments := laterArguments
                                   selectionSet := laterSelectionSet }])) =
                          executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              fields) ++
                          executableFieldSelections
                            [{ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := laterArguments
                               selectionSet := laterSelectionSet }] by
                        simp [executableFieldSelections, List.map_append]]
                      rw [visitSubfields_append_equivalence schema resolvers
                        variableValues (completionDepth + 2) parentType source
                        (executableFieldSelections
                          ({ parentType := parentType
                             responseName := responseName
                             fieldName := fieldName
                             arguments := arguments
                             selectionSet := selectionSet } ::
                            fields))
                        (executableFieldSelections
                          [{ parentType := parentType
                             responseName := responseName
                             fieldName := fieldName
                             arguments := laterArguments
                             selectionSet := laterSelectionSet }])
                        (.object [])]
                      rw [hprefixRaw]
                      cases fieldDefinition with
                      | mk definitionName outputType definitionArguments =>
                          cases outputType <;>
                            simp [GraphQL.Execution.executeField, hlookup,
                              hresolveFirst, handleFieldError,
                              groupedFieldVisitResult,
                              GraphQL.Execution.singleFieldResult, htailNull,
                              visitOk, combineVisitStatus,
                              GraphQL.Execution.Result.combine,
                              RootSelectionResultAlignedEquivalent,
                              ErrorPresenceEquivalent]
                  | some resolvedValue =>
                      simpa [GraphQL.Execution.executeField, hlookup,
                        hresolveFirst] using
                        executeRootSelectionSet_executableFieldSelections_append_one_aligned_resolved
                          schema resolvers variableValues completionDepth
                          parentType source responseName fieldName arguments
                          laterArguments selectionSet laterSelectionSet fields
                          fieldDefinition resolvedValue
                          (by
                            simpa using hprefixRaw)
                          hlookup
                          (by simpa using hresolveFirst)
                          (by simpa using hresolveLater)
                          (by
                            intro childDepth runtimeType identity hlt
                              hcontains hincludes
                            exact hprefixChildren childDepth runtimeType
                              identity hlt (by simpa using hcontains)
                              (by
                                simpa [Schema.fieldReturnType?, hlookup]
                                  using hincludes))
                          (by
                            intro childDepth runtimeType identity hlt
                              hcontains
                            exact hobjects childDepth runtimeType identity hlt
                              (by simpa using hcontains))
                          (by
                          intro childDepth runtimeType identity hlt
                            hcontains hincludes
                          exact hchildren childDepth runtimeType identity hlt
                            (by simpa using hcontains)
                            (by
                              simpa [Schema.fieldReturnType?, hlookup]
                                using hincludes))

theorem ExecutableFieldsMergedRoot_append_one_visit_aligned_of_prefix_contained_positive
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixAligned
      : GroupedFieldVisitAlignedEquivalent responseName
          (visitSubfields schema resolvers variableValues (completionDepth + 2)
            parentType source (executableFieldSelections (field :: fields))
            (.object []))
          (GraphQL.Execution.executeField schema resolvers variableValues
            (completionDepth + 2) source responseName (field :: fields)))
    (hprefixResponses
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups
      : ∀ candidate,
          candidate ∈ fields ++ [later]
          -> ∃ fieldDefinition,
              schema.lookupField parentType candidate.fieldName = some fieldDefinition)
    (hresolveFirst
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hresolveLater
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: fields)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object [])).fst
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                  (.object [])).fst).fst)
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: fields) ++ [later])
                  }
                initial := .object []
              })
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 2) parentType source
          (executableFieldSelections (field :: (fields ++ [later]))))
        (GraphQL.Execution.executeField schema resolvers variableValues
          (completionDepth + 2) source responseName
          (field :: (fields ++ [later]))) := by
  cases field with
  | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
      cases later with
      | mk laterParent laterResponseName laterFieldName laterArguments
          laterSelectionSet =>
          dsimp at hfieldResponse hlaterResponse hfieldParent
          dsimp at hlaterParent hfieldName hresolveFirst hresolveLater
          dsimp at hprefixResponses hprefixChildren hobjects hchildren
          subst fieldResponseName
          subst laterResponseName
          subst fieldParent
          subst laterParent
          subst laterFieldName
          have hlaterResponseAll :
              ∀ (candidate : ExecutableField),
                candidate ∈
                    ([{ parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := laterArguments
                        selectionSet := laterSelectionSet }] :
                      List ExecutableField) ->
                  candidate.responseName = responseName := by
            intro candidate hmem
            simp at hmem
            subst candidate
            rfl
          have htailNull :
              visitSubfields schema resolvers variableValues
                (completionDepth + 2) parentType source
                (executableFieldSelections
                  [{ parentType := parentType
                     responseName := responseName
                     fieldName := fieldName
                     arguments := laterArguments
                     selectionSet := laterSelectionSet }])
                (.object [(responseName, .null)]) =
              (.object [(responseName, .null)], visitOk) :=
            visitSubfields_executableFieldSelections_existing_null
              schema resolvers variableValues (completionDepth + 1)
              parentType source responseName
              [{ parentType := parentType
                 responseName := responseName
                 fieldName := fieldName
                 arguments := laterArguments
                 selectionSet := laterSelectionSet }]
              [(responseName, .null)] hlaterResponseAll
              (by
                intro candidate hmem
                simp at hmem
                subst candidate
                exact htailLookups
                  { parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet }
                  (by simp))
              (by simp [responseObjectField?, lookupResponseField?])
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              have hprefix :
                  GroupedFieldVisitAlignedEquivalent responseName
                    (visitSubfields schema resolvers variableValues
                      (completionDepth + 2) parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (.object []))
                    (GraphQL.Execution.singleFieldResult responseName
                      (.error 1)) := by
                simpa [GraphQL.Execution.executeField, hlookup,
                  GraphQL.Execution.singleFieldResult] using
                  hprefixAligned
              have htail :
                  visitSubfields schema resolvers variableValues
                    (completionDepth + 2) parentType source
                    (executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := laterArguments
                         selectionSet := laterSelectionSet }])
                    (visitSubfields schema resolvers variableValues
                      (completionDepth + 2) parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (.object [])).fst =
                  mergeResponseFieldResult responseName (.ok (.null, 0))
                    (visitSubfields schema resolvers variableValues
                      (completionDepth + 2) parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (.object [])).fst := by
                rw [hprefix.1]
                simpa [groupedFieldVisitResult,
                  GraphQL.Execution.singleFieldResult,
                  mergeResponseFieldResult, mergeResponseFieldIntoObject,
                  mergeResponseField, mergeResponse, resultValueOrNull,
                  resultStatus, visitOk] using htailNull
              have haligned :
                  ResponseValueResultAlignedEquivalent
                    (GraphQL.Execution.Result.combine mergeResponse
                      (.error 1 : Result ResponseValue) (.ok (.null, 0)))
                    (.error 1 : Result ResponseValue) := by
                simp [ResponseValueResultAlignedEquivalent,
                  GraphQL.Execution.Result.combine, ErrorPresenceEquivalent]
              simpa [GraphQL.Execution.executeField, hlookup,
                executableFieldSelections, List.map_append,
                GraphQL.Execution.singleFieldResult] using
                executeRootSelectionSet_append_one_visit_aligned_of_complete
                  schema resolvers variableValues (completionDepth + 2)
                  parentType source
                  (executableFieldSelections
                    ({ parentType := parentType
                       responseName := responseName
                       fieldName := fieldName
                       arguments := arguments
                       selectionSet := selectionSet } ::
                      fields))
                  (executableFieldSelections
                    [{ parentType := parentType
                       responseName := responseName
                       fieldName := fieldName
                       arguments := laterArguments
                       selectionSet := laterSelectionSet }])
                  responseName (.error 1 : Result ResponseValue)
                  (.ok (.null, 0)) (.error 1 : Result ResponseValue)
                  hprefix htail haligned
          | some fieldDefinition =>
              cases resolved with
              | none =>
                  have hprefix :
                      GroupedFieldVisitAlignedEquivalent responseName
                        (visitSubfields schema resolvers variableValues
                          (completionDepth + 2) parentType source
                          (executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              fields))
                          (.object []))
                        (GraphQL.Execution.singleFieldResult responseName
                          (handleFieldError fieldDefinition.outputType)) := by
                    simpa [GraphQL.Execution.executeField, hlookup,
                      hresolveFirst] using hprefixAligned
                  have htail :
                      visitSubfields schema resolvers variableValues
                        (completionDepth + 2) parentType source
                        (executableFieldSelections
                          [{ parentType := parentType
                             responseName := responseName
                             fieldName := fieldName
                             arguments := laterArguments
                             selectionSet := laterSelectionSet }])
                        (visitSubfields schema resolvers variableValues
                          (completionDepth + 2) parentType source
                          (executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              fields))
                          (.object [])).fst =
                      mergeResponseFieldResult responseName (.ok (.null, 0))
                        (visitSubfields schema resolvers variableValues
                          (completionDepth + 2) parentType source
                          (executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              fields))
                          (.object [])).fst := by
                    rw [hprefix.1]
                    cases fieldDefinition with
                    | mk definitionName outputType definitionArguments =>
                        cases outputType <;>
                          simp [handleFieldError, groupedFieldVisitResult,
                            GraphQL.Execution.singleFieldResult,
                            mergeResponseFieldResult,
                            mergeResponseFieldIntoObject,
                            mergeResponseField, mergeResponse,
                            resultValueOrNull, resultStatus, visitOk,
                            htailNull]
                  have haligned :
                      ResponseValueResultAlignedEquivalent
                        (GraphQL.Execution.Result.combine mergeResponse
                          (handleFieldError fieldDefinition.outputType)
                          (.ok (.null, 0)))
                        (handleFieldError fieldDefinition.outputType) := by
                    cases fieldDefinition with
                    | mk definitionName outputType definitionArguments =>
                        cases outputType <;>
                          simp [handleFieldError,
                            ResponseValueResultAlignedEquivalent,
                            GraphQL.Execution.Result.combine,
                            ErrorPresenceEquivalent, mergeResponse]
                  simpa [GraphQL.Execution.executeField, hlookup,
                    hresolveFirst, executableFieldSelections,
                    List.map_append] using
                    executeRootSelectionSet_append_one_visit_aligned_of_complete
                      schema resolvers variableValues (completionDepth + 2)
                      parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (executableFieldSelections
                        [{ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := laterArguments
                           selectionSet := laterSelectionSet }])
                      responseName (handleFieldError fieldDefinition.outputType)
                      (.ok (.null, 0))
                      (handleFieldError fieldDefinition.outputType)
                      hprefix htail haligned
              | some resolvedValue =>
                  simpa [GraphQL.Execution.executeField, hlookup,
                    hresolveFirst] using
                    executeRootSelectionSet_executableFieldSelections_append_one_visit_aligned_resolved
                      schema resolvers variableValues completionDepth
                      parentType source responseName fieldName arguments
                      laterArguments selectionSet laterSelectionSet fields
                      fieldDefinition resolvedValue
                      (by
                        simpa [GraphQL.Execution.executeField, hlookup,
                          hresolveFirst] using hprefixAligned)
                      hlookup
                      (by simpa using hresolveLater)
                      (by
                        intro childDepth runtimeType identity hlt
                          hcontains hincludes
                        exact hprefixChildren childDepth runtimeType identity
                          hlt (by simpa using hcontains)
                          (by
                            simpa [Schema.fieldReturnType?, hlookup]
                              using hincludes))
                      (by
                        intro childDepth runtimeType identity hlt hcontains
                        exact hobjects childDepth runtimeType identity hlt
                          (by simpa using hcontains))
                      (by
                        intro childDepth runtimeType identity hlt
                          hcontains hincludes
                        exact hchildren childDepth runtimeType identity hlt
                          (by simpa using hcontains)
                          (by
                            simpa [Schema.fieldReturnType?, hlookup]
                              using hincludes))

theorem
    ExecutableFieldsMergedRoot_append_one_visit_aligned_of_prefix_contained_positive_of_aligned_children
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixAligned
      : GroupedFieldVisitAlignedEquivalent responseName
          (visitSubfields schema resolvers variableValues (completionDepth + 2)
            parentType source (executableFieldSelections (field :: fields))
            (.object []))
          (GraphQL.Execution.executeField schema resolvers variableValues
            (completionDepth + 2) source responseName (field :: fields)))
    (hprefixResponses
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups
      : ∀ candidate,
          candidate ∈ fields ++ [later]
          -> ∃ fieldDefinition,
              schema.lookupField parentType candidate.fieldName = some fieldDefinition)
    (hresolveFirst
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hresolveLater
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields)))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))))
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object [])).fst
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                  (.object [])).fst).fst)
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ((field :: fields) ++ [later])))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType
                (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ((field :: fields) ++ [later]))))
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 2) parentType source
          (executableFieldSelections (field :: (fields ++ [later]))))
        (GraphQL.Execution.executeField schema resolvers variableValues
          (completionDepth + 2) source responseName
          (field :: (fields ++ [later]))) := by
  cases field with
  | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
      cases later with
      | mk laterParent laterResponseName laterFieldName laterArguments
          laterSelectionSet =>
          dsimp at hfieldResponse hlaterResponse hfieldParent
          dsimp at hlaterParent hfieldName hresolveFirst hresolveLater
          dsimp at hprefixResponses hprefixChildren hobjects hchildren
          subst fieldResponseName
          subst laterResponseName
          subst fieldParent
          subst laterParent
          subst laterFieldName
          have hlaterResponseAll :
              ∀ (candidate : ExecutableField),
                candidate ∈
                    ([{ parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := laterArguments
                        selectionSet := laterSelectionSet }] :
                      List ExecutableField) ->
                  candidate.responseName = responseName := by
            intro candidate hmem
            simp at hmem
            subst candidate
            rfl
          have htailNull :
              visitSubfields schema resolvers variableValues
                (completionDepth + 2) parentType source
                (executableFieldSelections
                  [{ parentType := parentType
                     responseName := responseName
                     fieldName := fieldName
                     arguments := laterArguments
                     selectionSet := laterSelectionSet }])
                (.object [(responseName, .null)]) =
              (.object [(responseName, .null)], visitOk) :=
            visitSubfields_executableFieldSelections_existing_null
              schema resolvers variableValues (completionDepth + 1)
              parentType source responseName
              [{ parentType := parentType
                 responseName := responseName
                 fieldName := fieldName
                 arguments := laterArguments
                 selectionSet := laterSelectionSet }]
              [(responseName, .null)] hlaterResponseAll
              (by
                intro candidate hmem
                simp at hmem
                subst candidate
                exact htailLookups
                  { parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet }
                  (by simp))
              (by simp [responseObjectField?, lookupResponseField?])
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              have hprefix :
                  GroupedFieldVisitAlignedEquivalent responseName
                    (visitSubfields schema resolvers variableValues
                      (completionDepth + 2) parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (.object []))
                    (GraphQL.Execution.singleFieldResult responseName
                      (.error 1)) := by
                simpa [GraphQL.Execution.executeField, hlookup,
                  GraphQL.Execution.singleFieldResult] using
                  hprefixAligned
              have htail :
                  visitSubfields schema resolvers variableValues
                    (completionDepth + 2) parentType source
                    (executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := laterArguments
                         selectionSet := laterSelectionSet }])
                    (visitSubfields schema resolvers variableValues
                      (completionDepth + 2) parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (.object [])).fst =
                  mergeResponseFieldResult responseName (.ok (.null, 0))
                    (visitSubfields schema resolvers variableValues
                      (completionDepth + 2) parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (.object [])).fst := by
                rw [hprefix.1]
                simpa [groupedFieldVisitResult,
                  GraphQL.Execution.singleFieldResult,
                  mergeResponseFieldResult, mergeResponseFieldIntoObject,
                  mergeResponseField, mergeResponse, resultValueOrNull,
                  resultStatus, visitOk] using htailNull
              have haligned :
                  ResponseValueResultAlignedEquivalent
                    (GraphQL.Execution.Result.combine mergeResponse
                      (.error 1 : Result ResponseValue) (.ok (.null, 0)))
                    (.error 1 : Result ResponseValue) := by
                simp [ResponseValueResultAlignedEquivalent,
                  GraphQL.Execution.Result.combine, ErrorPresenceEquivalent]
              simpa [GraphQL.Execution.executeField, hlookup,
                executableFieldSelections, List.map_append,
                GraphQL.Execution.singleFieldResult] using
                executeRootSelectionSet_append_one_visit_aligned_of_complete
                  schema resolvers variableValues (completionDepth + 2)
                  parentType source
                  (executableFieldSelections
                    ({ parentType := parentType
                       responseName := responseName
                       fieldName := fieldName
                       arguments := arguments
                       selectionSet := selectionSet } ::
                      fields))
                  (executableFieldSelections
                    [{ parentType := parentType
                       responseName := responseName
                       fieldName := fieldName
                       arguments := laterArguments
                       selectionSet := laterSelectionSet }])
                  responseName (.error 1 : Result ResponseValue)
                  (.ok (.null, 0)) (.error 1 : Result ResponseValue)
                  hprefix htail haligned
          | some fieldDefinition =>
              cases resolved with
              | none =>
                  have hprefix :
                      GroupedFieldVisitAlignedEquivalent responseName
                        (visitSubfields schema resolvers variableValues
                          (completionDepth + 2) parentType source
                          (executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              fields))
                          (.object []))
                        (GraphQL.Execution.singleFieldResult responseName
                          (handleFieldError fieldDefinition.outputType)) := by
                    simpa [GraphQL.Execution.executeField, hlookup,
                      hresolveFirst] using hprefixAligned
                  have htail :
                      visitSubfields schema resolvers variableValues
                        (completionDepth + 2) parentType source
                        (executableFieldSelections
                          [{ parentType := parentType
                             responseName := responseName
                             fieldName := fieldName
                             arguments := laterArguments
                             selectionSet := laterSelectionSet }])
                        (visitSubfields schema resolvers variableValues
                          (completionDepth + 2) parentType source
                          (executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              fields))
                          (.object [])).fst =
                      mergeResponseFieldResult responseName (.ok (.null, 0))
                        (visitSubfields schema resolvers variableValues
                          (completionDepth + 2) parentType source
                          (executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              fields))
                          (.object [])).fst := by
                    rw [hprefix.1]
                    cases fieldDefinition with
                    | mk definitionName outputType definitionArguments =>
                        cases outputType <;>
                          simp [handleFieldError, groupedFieldVisitResult,
                            GraphQL.Execution.singleFieldResult,
                            mergeResponseFieldResult,
                            mergeResponseFieldIntoObject,
                            mergeResponseField, mergeResponse,
                            resultValueOrNull, resultStatus, visitOk,
                            htailNull]
                  have haligned :
                      ResponseValueResultAlignedEquivalent
                        (GraphQL.Execution.Result.combine mergeResponse
                          (handleFieldError fieldDefinition.outputType)
                          (.ok (.null, 0)))
                        (handleFieldError fieldDefinition.outputType) := by
                    cases fieldDefinition with
                    | mk definitionName outputType definitionArguments =>
                        cases outputType <;>
                          simp [handleFieldError,
                            ResponseValueResultAlignedEquivalent,
                            GraphQL.Execution.Result.combine,
                            ErrorPresenceEquivalent, mergeResponse]
                  simpa [GraphQL.Execution.executeField, hlookup,
                    hresolveFirst, executableFieldSelections,
                    List.map_append] using
                    executeRootSelectionSet_append_one_visit_aligned_of_complete
                      schema resolvers variableValues (completionDepth + 2)
                      parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (executableFieldSelections
                        [{ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := laterArguments
                           selectionSet := laterSelectionSet }])
                      responseName (handleFieldError fieldDefinition.outputType)
                      (.ok (.null, 0))
                      (handleFieldError fieldDefinition.outputType)
                      hprefix htail haligned
              | some resolvedValue =>
                  simpa [GraphQL.Execution.executeField, hlookup,
                    hresolveFirst] using
                    executeRootSelectionSet_executableFieldSelections_append_one_visit_aligned_resolved_of_aligned_children
                      schema resolvers variableValues completionDepth
                      parentType source responseName fieldName arguments
                      laterArguments selectionSet laterSelectionSet fields
                      fieldDefinition resolvedValue
                      (by
                        simpa [GraphQL.Execution.executeField, hlookup,
                          hresolveFirst] using hprefixAligned)
                      hlookup
                      (by simpa using hresolveLater)
                      (by
                        intro childDepth runtimeType identity hlt
                          hcontains hincludes
                        exact hprefixChildren childDepth runtimeType identity
                          hlt (by simpa using hcontains)
                          (by
                            simpa [Schema.fieldReturnType?, hlookup]
                              using hincludes))
                      (by
                        intro childDepth runtimeType identity hlt hcontains
                        exact hobjects childDepth runtimeType identity hlt
                          (by simpa using hcontains))
                      (by
                        intro childDepth runtimeType identity hlt
                          hcontains hincludes
                        exact hchildren childDepth runtimeType identity hlt
                          (by simpa using hcontains)
                          (by
                            simpa [Schema.fieldReturnType?, hlookup]
                              using hincludes))

theorem
    ExecutableFieldsMergedVisit_append_one_visit_aligned_of_prefix_contained_positive_of_aligned_children
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixAligned
      : GroupedFieldVisitAlignedEquivalent responseName
          (visitSubfields schema resolvers variableValues (completionDepth + 2)
            parentType source (executableFieldSelections (field :: fields))
            (.object []))
          (GraphQL.Execution.executeField schema resolvers variableValues
            (completionDepth + 2) source responseName (field :: fields)))
    (hprefixResponses
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups
      : ∀ candidate,
          candidate ∈ fields ++ [later]
          -> ∃ fieldDefinition,
              schema.lookupField parentType candidate.fieldName = some fieldDefinition)
    (hresolveFirst
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hresolveLater
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields)))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))))
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object [])).fst
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                  (.object [])).fst).fst)
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ((field :: fields) ++ [later])))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType
                (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ((field :: fields) ++ [later]))))
    : GroupedFieldVisitAlignedEquivalent responseName
        (visitSubfields schema resolvers variableValues
          (completionDepth + 2) parentType source
          (executableFieldSelections (field :: (fields ++ [later])))
          (.object []))
        (GraphQL.Execution.executeField schema resolvers variableValues
          (completionDepth + 2) source responseName
          (field :: (fields ++ [later]))) := by
  cases field with
  | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
      cases later with
      | mk laterParent laterResponseName laterFieldName laterArguments
          laterSelectionSet =>
          dsimp at hfieldResponse hlaterResponse hfieldParent
          dsimp at hlaterParent hfieldName hresolveFirst hresolveLater
          dsimp at hprefixResponses hprefixChildren hobjects hchildren
          subst fieldResponseName
          subst laterResponseName
          subst fieldParent
          subst laterParent
          subst laterFieldName
          have hlaterResponseAll :
              ∀ (candidate : ExecutableField),
                candidate ∈
                    ([{ parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := laterArguments
                        selectionSet := laterSelectionSet }] :
                      List ExecutableField) ->
                  candidate.responseName = responseName := by
            intro candidate hmem
            simp at hmem
            subst candidate
            rfl
          have htailNull :
              visitSubfields schema resolvers variableValues
                (completionDepth + 2) parentType source
                (executableFieldSelections
                  [{ parentType := parentType
                     responseName := responseName
                     fieldName := fieldName
                     arguments := laterArguments
                     selectionSet := laterSelectionSet }])
                (.object [(responseName, .null)]) =
              (.object [(responseName, .null)], visitOk) :=
            visitSubfields_executableFieldSelections_existing_null
              schema resolvers variableValues (completionDepth + 1)
              parentType source responseName
              [{ parentType := parentType
                 responseName := responseName
                 fieldName := fieldName
                 arguments := laterArguments
                 selectionSet := laterSelectionSet }]
              [(responseName, .null)] hlaterResponseAll
              (by
                intro candidate hmem
                simp at hmem
                subst candidate
                exact htailLookups
                  { parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet }
                  (by simp))
              (by simp [responseObjectField?, lookupResponseField?])
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              have hprefix :
                  GroupedFieldVisitAlignedEquivalent responseName
                    (visitSubfields schema resolvers variableValues
                      (completionDepth + 2) parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (.object []))
                    (GraphQL.Execution.singleFieldResult responseName
                      (.error 1)) := by
                simpa [GraphQL.Execution.executeField, hlookup,
                  GraphQL.Execution.singleFieldResult] using
                  hprefixAligned
              have htail :
                  visitSubfields schema resolvers variableValues
                    (completionDepth + 2) parentType source
                    (executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := laterArguments
                         selectionSet := laterSelectionSet }])
                    (visitSubfields schema resolvers variableValues
                      (completionDepth + 2) parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (.object [])).fst =
                  mergeResponseFieldResult responseName (.ok (.null, 0))
                    (visitSubfields schema resolvers variableValues
                      (completionDepth + 2) parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (.object [])).fst := by
                rw [hprefix.1]
                simpa [groupedFieldVisitResult,
                  GraphQL.Execution.singleFieldResult,
                  mergeResponseFieldResult, mergeResponseFieldIntoObject,
                  mergeResponseField, mergeResponse, resultValueOrNull,
                  resultStatus, visitOk] using htailNull
              have haligned :
                  ResponseValueResultAlignedEquivalent
                    (GraphQL.Execution.Result.combine mergeResponse
                      (.error 1 : Result ResponseValue) (.ok (.null, 0)))
                    (.error 1 : Result ResponseValue) := by
                simp [ResponseValueResultAlignedEquivalent,
                  GraphQL.Execution.Result.combine, ErrorPresenceEquivalent]
              simpa [GraphQL.Execution.executeField, hlookup,
                executableFieldSelections, List.map_append,
                GraphQL.Execution.singleFieldResult] using
                visitSubfields_append_one_visit_aligned_of_complete
                  schema resolvers variableValues (completionDepth + 2)
                  parentType source
                  (executableFieldSelections
                    ({ parentType := parentType
                       responseName := responseName
                       fieldName := fieldName
                       arguments := arguments
                       selectionSet := selectionSet } ::
                      fields))
                  (executableFieldSelections
                    [{ parentType := parentType
                       responseName := responseName
                       fieldName := fieldName
                       arguments := laterArguments
                       selectionSet := laterSelectionSet }])
                  responseName (.error 1 : Result ResponseValue)
                  (.ok (.null, 0)) (.error 1 : Result ResponseValue)
                  hprefix htail haligned
          | some fieldDefinition =>
              cases resolved with
              | none =>
                  have hprefix :
                      GroupedFieldVisitAlignedEquivalent responseName
                        (visitSubfields schema resolvers variableValues
                          (completionDepth + 2) parentType source
                          (executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              fields))
                          (.object []))
                        (GraphQL.Execution.singleFieldResult responseName
                          (handleFieldError fieldDefinition.outputType)) := by
                    simpa [GraphQL.Execution.executeField, hlookup,
                      hresolveFirst] using hprefixAligned
                  have htail :
                      visitSubfields schema resolvers variableValues
                        (completionDepth + 2) parentType source
                        (executableFieldSelections
                          [{ parentType := parentType
                             responseName := responseName
                             fieldName := fieldName
                             arguments := laterArguments
                             selectionSet := laterSelectionSet }])
                        (visitSubfields schema resolvers variableValues
                          (completionDepth + 2) parentType source
                          (executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              fields))
                          (.object [])).fst =
                      mergeResponseFieldResult responseName (.ok (.null, 0))
                        (visitSubfields schema resolvers variableValues
                          (completionDepth + 2) parentType source
                          (executableFieldSelections
                            ({ parentType := parentType
                               responseName := responseName
                               fieldName := fieldName
                               arguments := arguments
                               selectionSet := selectionSet } ::
                              fields))
                          (.object [])).fst := by
                    rw [hprefix.1]
                    cases fieldDefinition with
                    | mk definitionName outputType definitionArguments =>
                        cases outputType <;>
                          simp [handleFieldError, groupedFieldVisitResult,
                            GraphQL.Execution.singleFieldResult,
                            mergeResponseFieldResult,
                            mergeResponseFieldIntoObject,
                            mergeResponseField, mergeResponse,
                            resultValueOrNull, resultStatus, visitOk,
                            htailNull]
                  have haligned :
                      ResponseValueResultAlignedEquivalent
                        (GraphQL.Execution.Result.combine mergeResponse
                          (handleFieldError fieldDefinition.outputType)
                          (.ok (.null, 0)))
                        (handleFieldError fieldDefinition.outputType) := by
                    cases fieldDefinition with
                    | mk definitionName outputType definitionArguments =>
                        cases outputType <;>
                          simp [handleFieldError,
                            ResponseValueResultAlignedEquivalent,
                            GraphQL.Execution.Result.combine,
                            ErrorPresenceEquivalent, mergeResponse]
                  simpa [GraphQL.Execution.executeField, hlookup,
                    hresolveFirst, executableFieldSelections,
                    List.map_append] using
                    visitSubfields_append_one_visit_aligned_of_complete
                      schema resolvers variableValues (completionDepth + 2)
                      parentType source
                      (executableFieldSelections
                        ({ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := arguments
                           selectionSet := selectionSet } ::
                          fields))
                      (executableFieldSelections
                        [{ parentType := parentType
                           responseName := responseName
                           fieldName := fieldName
                           arguments := laterArguments
                           selectionSet := laterSelectionSet }])
                      responseName (handleFieldError fieldDefinition.outputType)
                      (.ok (.null, 0))
                      (handleFieldError fieldDefinition.outputType)
                      hprefix htail haligned
              | some resolvedValue =>
                  simpa [GraphQL.Execution.executeField, hlookup,
                    hresolveFirst] using
                    visitSubfields_executableFieldSelections_append_one_visit_aligned_resolved_of_aligned_children
                      schema resolvers variableValues completionDepth
                      parentType source responseName fieldName arguments
                      laterArguments selectionSet laterSelectionSet fields
                      fieldDefinition resolvedValue
                      (by
                        simpa [GraphQL.Execution.executeField, hlookup,
                          hresolveFirst] using hprefixAligned)
                      hlookup
                      (by simpa using hresolveLater)
                      (by
                        intro childDepth runtimeType identity hlt
                          hcontains hincludes
                        exact hprefixChildren childDepth runtimeType identity
                          hlt (by simpa using hcontains)
                          (by
                            simpa [Schema.fieldReturnType?, hlookup]
                              using hincludes))
                      (by
                        intro childDepth runtimeType identity hlt hcontains
                        exact hobjects childDepth runtimeType identity hlt
                          (by simpa using hcontains))
                      (by
                        intro childDepth runtimeType identity hlt
                          hcontains hincludes
                        exact hchildren childDepth runtimeType identity hlt
                          (by simpa using hcontains)
                            (by
                              simpa [Schema.fieldReturnType?, hlookup]
                                using hincludes))

theorem ExecutableFieldsMergedResponse_append_one_of_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw
      : ExecutableFieldsMergedRaw schema resolvers variableValues depth
          parentType source responseName field fields resolved)
    (hprefixResponses
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups
      : ∀ candidate,
          candidate ∈ fields ++ [later]
          -> ∃ fieldDefinition,
              schema.lookupField parentType candidate.fieldName = some fieldDefinition)
    (hresolveFirst
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hresolveLater
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: fields)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: fields) ++ [later])
                  }
                initial := .object []
              })
    : ExecutableFieldsMergedResponse schema resolvers variableValues depth
        parentType source responseName field (fields ++ [later]) resolved := by
  apply ExecutableFieldsMergedResponse_of_raw schema resolvers variableValues
    depth parentType source responseName field (fields ++ [later]) resolved
  exact
    ExecutableFieldsMergedRaw_append_one_of_prefix schema resolvers
      variableValues depth parentType source responseName field fields later
      resolved hprefixRaw hprefixResponses hfieldResponse hlaterResponse
      hfieldParent hlaterParent hfieldName htailLookups hresolveFirst hresolveLater
      (by
        intro childDepth runtimeType identity hlt _hcontains hincludes
        exact hprefixChildren childDepth runtimeType identity hlt hincludes)
      (by
        intro childDepth runtimeType identity hlt _hcontains
        exact hobjects childDepth runtimeType identity hlt)
      (by
        intro childDepth runtimeType identity hlt _hcontains
        exact herrors childDepth runtimeType identity hlt)
      (by
        intro childDepth runtimeType identity hlt _hcontains hincludes
        exact hchildren childDepth runtimeType identity hlt hincludes)

theorem ExecutableFieldsMergedComplete_append_one_of_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw
      : ExecutableFieldsMergedRaw schema resolvers variableValues depth
          parentType source responseName field fields resolved)
    (hprefixResponses
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups
      : ∀ candidate,
          candidate ∈ fields ++ [later]
          -> ∃ fieldDefinition,
              schema.lookupField parentType candidate.fieldName = some fieldDefinition)
    (hresolveFirst
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hresolveLater
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: fields)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: fields) ++ [later])
                  }
                initial := .object []
              })
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field (fields ++ [later]) resolved := by
  apply ExecutableFieldsMergedComplete_of_MergedResponse
  apply ExecutableFieldsMergedResponse_append_one_of_prefix schema resolvers
    variableValues depth parentType source responseName field fields later
    resolved
  · exact hprefixRaw
  · exact hprefixResponses
  · exact hfieldResponse
  · exact hlaterResponse
  · exact hfieldParent
  · exact hlaterParent
  · exact hfieldName
  · exact htailLookups
  · exact hresolveFirst
  · exact hresolveLater
  · exact hprefixChildren
  · exact hobjects
  · exact herrors
  · exact hchildren

theorem ExecutableFieldsMergedResponse_append_one_of_prefix_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw
      : ExecutableFieldsMergedRaw schema resolvers variableValues depth
          parentType source responseName field fields resolved)
    (hprefixResponses
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups
      : ∀ candidate,
          candidate ∈ fields ++ [later]
          -> ∃ fieldDefinition,
              schema.lookupField parentType candidate.fieldName = some fieldDefinition)
    (hresolveFirst
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hresolveLater
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: fields)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: fields) ++ [later])
                  }
                initial := .object []
              })
    : ExecutableFieldsMergedResponse schema resolvers variableValues depth
        parentType source responseName field (fields ++ [later]) resolved := by
  apply ExecutableFieldsMergedResponse_of_raw schema resolvers variableValues
    depth parentType source responseName field (fields ++ [later]) resolved
  exact
    ExecutableFieldsMergedRaw_append_one_of_prefix schema resolvers
      variableValues depth parentType source responseName field fields later
      resolved hprefixRaw hprefixResponses hfieldResponse hlaterResponse
      hfieldParent hlaterParent hfieldName htailLookups hresolveFirst
      hresolveLater
      hprefixChildren hobjects herrors hchildren

theorem ExecutableFieldsMergedComplete_append_one_of_prefix_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hprefixRaw
      : ExecutableFieldsMergedRaw schema resolvers variableValues depth
          parentType source responseName field fields resolved)
    (hprefixResponses
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hfieldResponse : field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfieldName : later.fieldName = field.fieldName)
    (htailLookups
      : ∀ candidate,
          candidate ∈ fields ++ [later]
          -> ∃ fieldDefinition,
              schema.lookupField parentType candidate.fieldName = some fieldDefinition)
    (hresolveFirst
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hresolveLater
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: fields)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: fields))
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: fields) ++ [later])
                  }
                initial := .object []
              })
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field (fields ++ [later]) resolved := by
  apply ExecutableFieldsMergedComplete_of_MergedResponse
  apply ExecutableFieldsMergedResponse_append_one_of_prefix_contained
    schema resolvers variableValues depth parentType source responseName field
    fields later resolved
  · exact hprefixRaw
  · exact hprefixResponses
  · exact hfieldResponse
  · exact hlaterResponse
  · exact hfieldParent
  · exact hlaterParent
  · exact hfieldName
  · exact htailLookups
  · exact hresolveFirst
  · exact hresolveLater
  · exact hprefixChildren
  · exact hobjects
  · exact herrors
  · exact hchildren

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
