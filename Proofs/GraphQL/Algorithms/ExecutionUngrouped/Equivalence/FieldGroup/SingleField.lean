import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldGroup.CompleteAppend

/-!
Single executable-field execution helpers for field-group equivalence.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped
namespace Eager

open GraphQL.Execution

local instance fieldGroupSingleFieldResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem resultValueOrNull_executeField_depth_zero_none
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    : resultValueOrNull (executeField schema resolvers variableValues 0 source none field)
      = .null := by
  cases hlookup : schema.lookupField field.parentType field.fieldName with
      | none =>
          simp [executeField, hlookup, resultValueOrNull]
      | some fieldDefinition =>
          cases hresolve :
              resolvers.resolve field.parentType field.fieldName field.arguments
                source with
          | none =>
              rcases fieldDefinition with ⟨fdName, fdOutput, fdArgs⟩
              cases fdOutput <;>
                simp [executeField, hlookup, hresolve, reusablePreviousValue?, handleFieldError, resultValueOrNull]
          | some resolved =>
              simp [executeField, hlookup, hresolve, reusablePreviousValue?, completeValue, outOfFuel, resultValueOrNull]

theorem
    visitSubfields_executableFieldSelections_single_eq_groupedFieldVisitResult_of_guarded_child_states
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hfieldResponse : field.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
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
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : visitSubfields schema resolvers variableValues (depth + 1) parentType
        source (executableFieldSelections [field]) (.object [])
      = groupedFieldVisitResult responseName
          (GraphQL.Execution.executeField schema resolvers variableValues
            (depth + 1) source responseName [field]) := by
  cases field with
  | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
      dsimp at hfieldResponse hfieldParent hresolve hchildren ⊢
      subst fieldResponseName
      subst fieldParent
      cases hlookup : schema.lookupField parentType fieldName with
      | none =>
          simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult]
      | some fieldDefinition =>
          cases resolved with
          | none =>
              simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, hresolve, reusablePreviousValue?, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult]
          | some resolvedValue =>
              have hcomplete :
                  completeValue schema resolvers variableValues depth
                    fieldDefinition.outputType selectionSet resolvedValue
                    none =
                  GraphQL.Execution.completeValue schema resolvers
                    variableValues depth fieldDefinition.outputType
                    [executableField parentType responseName fieldName arguments
                      selectionSet]
                    resolvedValue :=
                completeValue_single_field_eq_spec_of_guarded_child_states
                  schema resolvers variableValues
                  (executableField parentType responseName fieldName arguments
                    selectionSet)
                  fieldDefinition.outputType depth resolvedValue
                  (by
                    intro childDepth runtimeType identity hlt hincludes
                    exact hchildren childDepth runtimeType identity hlt
                      (by
                        simpa [Schema.fieldReturnType?, hlookup] using
                          hincludes))
              rw [show
                  executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := arguments
                         selectionSet := selectionSet }] =
                    [executableFieldSelection
                      { parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet }] by
                rfl]
              simp [visitSubfields, visitSelection, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, hresolve, reusablePreviousValue?, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult, hcomplete]

theorem
    visitSubfields_executableFieldSelections_single_eq_groupedFieldVisitResult_of_contained_child_states
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hfieldResponse : field.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
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
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : visitSubfields schema resolvers variableValues (depth + 1) parentType
        source (executableFieldSelections [field]) (.object [])
      = groupedFieldVisitResult responseName
          (GraphQL.Execution.executeField schema resolvers variableValues
            (depth + 1) source responseName [field]) := by
  cases field with
  | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
      dsimp at hfieldResponse hfieldParent hresolve hchildren ⊢
      subst fieldResponseName
      subst fieldParent
      cases hlookup : schema.lookupField parentType fieldName with
      | none =>
          simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult]
      | some fieldDefinition =>
          cases resolved with
          | none =>
              simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, hresolve, reusablePreviousValue?, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult]
          | some resolvedValue =>
              have hcomplete :
                    completeValue schema resolvers variableValues depth
                      fieldDefinition.outputType selectionSet resolvedValue
                      none =
                  GraphQL.Execution.completeValue schema resolvers
                    variableValues depth fieldDefinition.outputType
                    [executableField parentType responseName fieldName arguments
                      selectionSet]
                    resolvedValue :=
                completeValue_single_field_eq_spec_of_contained_child_states
                  schema resolvers variableValues
                  (executableField parentType responseName fieldName arguments
                    selectionSet)
                  fieldDefinition.outputType depth resolvedValue
                  (by
                    intro childDepth runtimeType identity hlt hcontains
                      hincludes
                    exact hchildren childDepth runtimeType identity hlt
                      hcontains
                      (by
                        simpa [Schema.fieldReturnType?, hlookup] using
                          hincludes))
              rw [show
                  executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := arguments
                         selectionSet := selectionSet }] =
                    [executableFieldSelection
                      { parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet }] by
                rfl]
              simp [visitSubfields, visitSelection, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, executeField, GraphQL.Execution.executeField, hlookup, hresolve, reusablePreviousValue?, mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult, hcomplete]

theorem visitSubfields_executableFieldSelections_single_aligned_of_contained_child_states
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hfieldResponse : field.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) field.selectionSet)
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                field.selectionSet))
    : GroupedFieldVisitAlignedEquivalent responseName
        (visitSubfields schema resolvers variableValues (depth + 1) parentType
          source (executableFieldSelections [field]) (.object []))
        (GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName [field]) := by
  cases field with
  | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
      dsimp at hfieldResponse hfieldParent hresolve hchildren ⊢
      subst fieldResponseName
      subst fieldParent
      cases hlookup : schema.lookupField parentType fieldName with
      | none =>
          simp [visitSubfields, visitSelection, executableFieldSelections,
            executableFieldSelection, executableField,
            selectionDirectivesAllowBool_empty, responseObjectField?,
            lookupResponseField?, executeField, GraphQL.Execution.executeField,
            hlookup, groupedFieldVisitResult, GraphQL.Execution.singleFieldResult,
            mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult,
            GroupedFieldVisitAlignedEquivalent,
            VisitStatusAlignedEquivalent, ErrorPresenceEquivalent]
      | some fieldDefinition =>
          cases resolved with
          | none =>
              cases fieldDefinition with
              | mk definitionName outputType definitionArguments =>
                  cases outputType <;>
                    simp [visitSubfields, visitSelection,
                      executableFieldSelections, executableFieldSelection,
                      executableField, selectionDirectivesAllowBool_empty,
                      responseObjectField?, lookupResponseField?, executeField,
                      GraphQL.Execution.executeField, hlookup, hresolve,
                      reusablePreviousValue?, handleFieldError,
                      groupedFieldVisitResult,
                      GraphQL.Execution.singleFieldResult,
                      mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult,
                      GroupedFieldVisitAlignedEquivalent,
                      VisitStatusAlignedEquivalent, visitOk,
                      combineVisitStatus, GraphQL.Execution.Result.combine,
                      ErrorPresenceEquivalent]
          | some resolvedValue =>
              let executable :=
                executableField parentType responseName fieldName arguments
                  selectionSet
              have hcomplete :
                  ResponseValueResultAlignedEquivalent
                    (completeValue schema resolvers variableValues depth
                      fieldDefinition.outputType selectionSet resolvedValue none)
                    (GraphQL.Execution.completeValue schema resolvers
                      variableValues depth fieldDefinition.outputType
                      [executable] resolvedValue) := by
                have hgroup :=
                  completeValue_group_aligned_of_contained_child_states
                    schema resolvers variableValues [executable]
                    fieldDefinition.outputType depth resolvedValue
                    (by
                      intro childDepth runtimeType identity hlt hcontains
                        hincludes
                      simpa [executable, executableField,
                        GraphQL.Execution.mergedFieldSelectionSet] using
                        hchildren childDepth runtimeType identity hlt hcontains
                          (by
                            simpa [Schema.fieldReturnType?, hlookup] using
                              hincludes))
                simpa [executable, executableField,
                  GraphQL.Execution.mergedFieldSelectionSet] using hgroup
              rw [show
                  executableFieldSelections
                      [{ parentType := parentType
                         responseName := responseName
                         fieldName := fieldName
                         arguments := arguments
                         selectionSet := selectionSet }] =
                    [executableFieldSelection
                      { parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet }] by
                rfl]
              simpa [visitSubfields, visitSelection, executableFieldSelection,
                executableField, selectionDirectivesAllowBool_empty,
                responseObjectField?, lookupResponseField?, executeField,
                GraphQL.Execution.executeField, hlookup, hresolve,
                reusablePreviousValue?, executable] using
                mergeResponseFieldResult_empty_aligned_singleFieldResult
                  responseName hcomplete

theorem ExecutableFieldsMergedRaw_single_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
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
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedRaw
  simpa using
    visitSubfields_executableFieldSelections_single_eq_groupedFieldVisitResult_of_guarded_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsMergedRaw_single_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
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
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedRaw
  simpa using
    visitSubfields_executableFieldSelections_single_eq_groupedFieldVisitResult_of_contained_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem visitSubfields_executableFieldSelections_existing_null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name)
    : ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
        (∀ field, field ∈ fields -> field.responseName = responseName)
        -> (∀ field,
              field ∈ fields
              -> ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName = some fieldDefinition)
        -> responseObjectField? responseName (.object outputFields) = some .null
        -> visitSubfields schema resolvers variableValues (depth + 1)
              parentType source
              (executableFieldSelections fields) (.object outputFields)
            = (.object outputFields, visitOk)
  | [], outputFields, _hresponse, _hlookups, _hlookup => by
      simp [visitSubfields, executableFieldSelections, visitOk]
  | field :: rest, outputFields, hresponse, hlookups, hlookup => by
      have hfieldResponse : field.responseName = responseName :=
        hresponse field (by simp)
      rcases hlookups field (by simp) with ⟨fieldDefinition, hfieldLookup⟩
      have hrestResponse :
          ∀ restField, restField ∈ rest ->
            restField.responseName = responseName := by
        intro restField hmem
        exact hresponse restField (by simp [hmem])
      have hrestLookups :
          ∀ restField, restField ∈ rest ->
            ∃ fieldDefinition, schema.lookupField parentType
              restField.fieldName = some fieldDefinition := by
        intro restField hmem
        exact hlookups restField (by simp [hmem])
      have hmerge :
          mergeResponseField responseName .null outputFields = outputFields :=
        mergeResponseField_null_of_lookup_null responseName outputFields
          (by simpa [responseObjectField?] using hlookup)
      have hhead :
          visitSelection schema resolvers variableValues (depth + 1)
            parentType source
            (executableFieldSelection field) (.object outputFields) =
          (.object outputFields, visitOk) := by
        cases field with
        | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
            dsimp [executableFieldSelection] at hfieldResponse hfieldLookup ⊢
            subst fieldResponseName
            simp [visitSelection, selectionDirectivesAllowBool_empty, hlookup, executeField, executableField, hfieldLookup, reusablePreviousValue?_null, mergeResponseFieldResult, mergeResponseFieldIntoObject, hmerge, resultValueOrNull, resultStatus, visitOk]
      have hrest :=
        visitSubfields_executableFieldSelections_existing_null schema
          resolvers variableValues depth parentType source responseName rest
          outputFields hrestResponse hrestLookups hlookup
      rw [show executableFieldSelections (field :: rest) =
          executableFieldSelection field :: executableFieldSelections rest by
        rfl]
      simp [visitSubfields, hhead, hrest]

theorem visitSubfields_executableFieldSelections_completion_zero_same_response_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (rest : List ExecutableField)
    (outputFields : List (Name × ResponseValue))
    (hresponse
      : ∀ candidate, candidate ∈ field :: rest -> candidate.responseName = responseName)
    (hrestLookups
      : ∀ candidate,
          candidate ∈ rest
          -> ∃ fieldDefinition,
              schema.lookupField parentType candidate.fieldName = some fieldDefinition)
    (hfresh : responseName ∉ outputFields.map Prod.fst)
    : visitSubfields schema resolvers variableValues 1 parentType source
        (executableFieldSelections (field :: rest)) (.object outputFields)
      = let fieldResult :=
          executeField schema resolvers variableValues 0 source none
            (executableField parentType responseName field.fieldName field.arguments
              field.selectionSet)
        (
          .object (outputFields ++ [(responseName, .null)]),
          resultStatus fieldResult
        ) := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hrestResponse :
      ∀ restField, restField ∈ rest ->
        restField.responseName = responseName := by
    intro restField hmem
    exact hresponse restField (by simp [hmem])
  let fieldResult :=
    executeField schema resolvers variableValues 0 source none
      (executableField parentType responseName field.fieldName field.arguments
        field.selectionSet)
  have hlookupFresh :
      responseObjectField? responseName (.object outputFields) = none :=
    responseObjectField?_none_of_not_mem responseName outputFields hfresh
  have hvalueNull : resultValueOrNull fieldResult = .null := by
    dsimp [fieldResult]
    exact
      resultValueOrNull_executeField_depth_zero_none schema resolvers variableValues
        source
        (executableField parentType responseName field.fieldName field.arguments
          field.selectionSet)
  have hmerge :
      mergeResponseField responseName (resultValueOrNull fieldResult)
          outputFields =
        outputFields ++ [(responseName, .null)] := by
    rw [hvalueNull]
    exact mergeResponseField_of_not_mem responseName .null outputFields hfresh
  have hhead :
      visitSelection schema resolvers variableValues 1 parentType source
        (executableFieldSelection field) (.object outputFields) =
      (.object (outputFields ++ [(responseName, .null)]),
        resultStatus fieldResult) := by
    cases field with
    | mk fieldParent fieldResponseName fieldName arguments selectionSet =>
        dsimp [executableFieldSelection] at hfieldResponse ⊢
        subst fieldResponseName
        have hmerge' :
            mergeResponseField responseName
                (resultValueOrNull
                    (executeField schema resolvers variableValues 0 source
                      none
                    { parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet }))
                outputFields =
              outputFields ++ [(responseName, .null)] := by
          simpa [fieldResult, executableField] using hmerge
        dsimp [fieldResult]
        simp [visitSelection, selectionDirectivesAllowBool_empty, hlookupFresh, mergeResponseFieldResult, mergeResponseFieldIntoObject, hmerge', executableField]
  have hlookupNull :
      responseObjectField? responseName
          (.object (outputFields ++ [(responseName, .null)])) =
        some .null :=
    responseObjectField?_append_singleton_null_of_not_mem responseName
      outputFields hfresh
  have hrest :=
    visitSubfields_executableFieldSelections_existing_null schema resolvers
      variableValues 0 parentType source responseName rest
      (outputFields ++ [(responseName, .null)]) hrestResponse hrestLookups
      hlookupNull
  rw [show executableFieldSelections (field :: rest) =
      executableFieldSelection field :: executableFieldSelections rest by
    rfl]
  simp [visitSubfields, hhead, hrest, fieldResult]

theorem completeValue_previous_null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fuel : Nat) (fieldType : TypeRef)
    (selectionSet : List Selection) (value : ResolverValue ObjectIdentity)
    : completeValue schema resolvers variableValues (fuel + 1) fieldType selectionSet
        value (some .null)
      = .ok (.null, 0) := by
  simp [completeValue]

theorem visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (resolvedValue : ResolverValue ObjectIdentity) (previous : ResponseValue)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hresolve
      : resolvers.resolve parentType fieldName arguments source = some resolvedValue)
    : visitSubfields schema resolvers variableValues (completionDepth + 1 + 1)
        parentType source
        (executableFieldSelections
          [{
            parentType := parentType
            responseName := responseName
            fieldName := fieldName
            arguments := arguments
            selectionSet := selectionSet
          }])
        (.object [(responseName, previous)])
      = mergeResponseFieldResult responseName
          (completeResolvedValue schema resolvers variableValues (completionDepth + 1)
            fieldDefinition.outputType selectionSet resolvedValue (some previous))
          (.object [(responseName, previous)]) := by
  have hexec :
      executeField schema resolvers variableValues (completionDepth + 1)
          source (some previous)
          { parentType := parentType
            responseName := responseName
            fieldName := fieldName
            arguments := arguments
            selectionSet := selectionSet } =
      completeResolvedValue schema resolvers variableValues (completionDepth + 1)
        fieldDefinition.outputType selectionSet resolvedValue (some previous) :=
    executeField_resolved_eq_completeResolvedValue schema resolvers
      variableValues completionDepth source
      { parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := selectionSet }
      fieldDefinition resolvedValue previous hlookup hresolve
  cases previous with
  | null =>
      simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, completeResolvedValue_previous_null, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, resultValueOrNull, resultStatus, visitOk, combineVisitStatus, GraphQL.Execution.Result.combine, hexec]
  | scalar value =>
      cases hcomplete :
          completeResolvedValue schema resolvers variableValues
            (completionDepth + 1) fieldDefinition.outputType selectionSet
            resolvedValue (some (ResponseValue.scalar value)) with
      | error errors =>
          simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, resultValueOrNull, resultStatus, visitOk, combineVisitStatus, GraphQL.Execution.Result.combine, hexec, hcomplete]
      | ok completeResult =>
          rcases completeResult with ⟨completeValue, completeErrors⟩
          simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, resultValueOrNull, resultStatus, visitOk, combineVisitStatus, GraphQL.Execution.Result.combine, hexec, hcomplete]
  | object fields =>
      simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, resultValueOrNull, hexec]
  | list values =>
      simp [visitSubfields, visitSelection, executableFieldSelections, executableFieldSelection, executableField, selectionDirectivesAllowBool_empty, responseObjectField?, lookupResponseField?, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, resultValueOrNull, hexec]

theorem executeRootSelectionSet_executableFieldSelections_append_one_aligned_resolved
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments laterArguments : List Argument)
    (selectionSet laterSelectionSet : List Selection)
    (fields : List ExecutableField)
    (fieldDefinition : FieldDefinition)
    (resolvedValue : ResolverValue ObjectIdentity)
    (hprefixRaw
      : ExecutableFieldsMergedRaw schema resolvers variableValues
          (completionDepth + 1) parentType source responseName
          {
            parentType := parentType
            responseName := responseName
            fieldName := fieldName
            arguments := arguments
            selectionSet := selectionSet
          }
          fields (some resolvedValue))
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hresolveFirst
      : resolvers.resolve parentType fieldName arguments source = some resolvedValue)
    (hresolveLater
      : resolvers.resolve parentType fieldName laterArguments source = some resolvedValue)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolvedValue runtimeType identity
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
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
                        ({
                            parentType := parentType
                            responseName := responseName
                            fieldName := fieldName
                            arguments := arguments
                            selectionSet := selectionSet
                          }
                          :: fields)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolvedValue runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ({
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet
                    }
                    :: fields))
                (.object [])).fst
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) laterSelectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    ({
                        parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet
                      }
                      :: fields))
                  (.object [])).fst).fst)
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolvedValue runtimeType identity
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
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
                        (({
                              parentType := parentType
                              responseName := responseName
                              fieldName := fieldName
                              arguments := arguments
                              selectionSet := selectionSet
                            }
                            :: fields)
                          ++ [{
                                parentType := parentType
                                responseName := responseName
                                fieldName := fieldName
                                arguments := laterArguments
                                selectionSet := laterSelectionSet
                              }])
                  }
                initial := .object []
              })
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 2) parentType source
          (executableFieldSelections
            (({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              ++ [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet
                  }])))
        (GraphQL.Execution.singleFieldResult responseName
          (GraphQL.Execution.completeValue schema resolvers variableValues
            (completionDepth + 1) fieldDefinition.outputType
            (({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              ++ [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet
                  }])
            resolvedValue)) := by
  let prefixFields : List ExecutableField :=
    { parentType := parentType
      responseName := responseName
      fieldName := fieldName
      arguments := arguments
      selectionSet := selectionSet } :: fields
  let later : ExecutableField :=
    { parentType := parentType
      responseName := responseName
      fieldName := fieldName
      arguments := laterArguments
      selectionSet := laterSelectionSet }
  let prefixCompleted :=
    GraphQL.Execution.completeValue schema resolvers variableValues
      (completionDepth + 1) fieldDefinition.outputType prefixFields
      resolvedValue
  let laterCompleted :=
    completeResolvedValue schema resolvers variableValues (completionDepth + 1)
      fieldDefinition.outputType laterSelectionSet resolvedValue
      (some (resultValueOrNull prefixCompleted))
  have hprefix :
      visitSubfields schema resolvers variableValues (completionDepth + 2)
        parentType source (executableFieldSelections prefixFields)
        (.object []) =
      groupedFieldVisitResult responseName
        (GraphQL.Execution.singleFieldResult responseName prefixCompleted) := by
    unfold ExecutableFieldsMergedRaw at hprefixRaw
    simpa [prefixFields, prefixCompleted, GraphQL.Execution.executeField,
      hlookup, hresolveFirst] using hprefixRaw
  have htail :
      visitSubfields schema resolvers variableValues (completionDepth + 2)
        parentType source (executableFieldSelections [later])
        (groupedFieldVisitResult responseName
          (GraphQL.Execution.singleFieldResult responseName prefixCompleted)).fst =
      mergeResponseFieldResult responseName laterCompleted
        (groupedFieldVisitResult responseName
          (GraphQL.Execution.singleFieldResult responseName prefixCompleted)).fst := by
    cases hprefixCompleted : prefixCompleted with
    | error prefixErrors =>
        have hlaterVisit :=
          visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
            schema resolvers variableValues completionDepth parentType source
            responseName fieldName laterArguments laterSelectionSet
            fieldDefinition resolvedValue .null hlookup hresolveLater
        simpa [prefixCompleted, laterCompleted, groupedFieldVisitResult,
          GraphQL.Execution.singleFieldResult, hprefixCompleted,
          resultValueOrNull, later] using hlaterVisit
    | ok prefixResult =>
        rcases prefixResult with ⟨prefixValue, prefixErrors⟩
        have hlaterVisit :=
          visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
            schema resolvers variableValues completionDepth parentType source
            responseName fieldName laterArguments laterSelectionSet
            fieldDefinition resolvedValue prefixValue hlookup hresolveLater
        simpa [prefixCompleted, laterCompleted, groupedFieldVisitResult,
          GraphQL.Execution.singleFieldResult, hprefixCompleted, later,
          resultValueOrNull, Nat.add_assoc] using hlaterVisit
  have haligned :
      ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse prefixCompleted
          laterCompleted)
        (GraphQL.Execution.completeValue schema resolvers variableValues
          (completionDepth + 1) fieldDefinition.outputType (prefixFields ++ [later])
          resolvedValue) := by
    dsimp [prefixCompleted, laterCompleted]
    exact
      completeValue_group_append_one_result_aligned_spec schema resolvers
        variableValues fieldDefinition.outputType (completionDepth + 1)
        resolvedValue prefixFields later
        hprefixChildren hobjects hchildren
  simpa [prefixFields, later, prefixCompleted, laterCompleted,
    executableFieldSelections, List.map_append] using
    executeRootSelectionSet_append_one_aligned_of_complete schema resolvers
      variableValues (completionDepth + 2) parentType source
      (executableFieldSelections prefixFields) (executableFieldSelections [later])
      responseName prefixCompleted laterCompleted
      (GraphQL.Execution.completeValue schema resolvers variableValues
        (completionDepth + 1) fieldDefinition.outputType (prefixFields ++ [later])
        resolvedValue)
      hprefix htail haligned

theorem
    executeRootSelectionSet_executableFieldSelections_append_one_visit_aligned_resolved
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName fieldName : Name)
    (arguments laterArguments : List Argument)
    (selectionSet laterSelectionSet : List Selection) (fields : List ExecutableField)
    (fieldDefinition : FieldDefinition) (resolvedValue : ResolverValue ObjectIdentity)
    (hprefixAligned
      : GroupedFieldVisitAlignedEquivalent responseName
          (visitSubfields schema resolvers variableValues (completionDepth + 2)
            parentType source
            (executableFieldSelections
              ({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields))
            (.object []))
          (GraphQL.Execution.singleFieldResult responseName
            (GraphQL.Execution.completeValue schema resolvers variableValues
              (completionDepth + 1) fieldDefinition.outputType
              ({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              resolvedValue)))
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hresolveLater
      : resolvers.resolve parentType fieldName laterArguments source = some resolvedValue)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolvedValue runtimeType identity
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
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
                        ({
                            parentType := parentType
                            responseName := responseName
                            fieldName := fieldName
                            arguments := arguments
                            selectionSet := selectionSet
                          }
                          :: fields)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolvedValue runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ({
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet
                    }
                    :: fields))
                (.object [])).fst
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) laterSelectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    ({
                        parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet
                      }
                      :: fields))
                  (.object [])).fst).fst)
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolvedValue runtimeType identity
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
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
                        (({
                              parentType := parentType
                              responseName := responseName
                              fieldName := fieldName
                              arguments := arguments
                              selectionSet := selectionSet
                            }
                            :: fields)
                          ++ [{
                                parentType := parentType
                                responseName := responseName
                                fieldName := fieldName
                                arguments := laterArguments
                                selectionSet := laterSelectionSet
                              }])
                  }
                initial := .object []
              })
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 2) parentType source
          (executableFieldSelections
            (({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              ++ [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet
                  }])))
        (GraphQL.Execution.singleFieldResult responseName
          (GraphQL.Execution.completeValue schema resolvers variableValues
            (completionDepth + 1) fieldDefinition.outputType
            (({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              ++ [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet
                  }])
            resolvedValue)) := by
  let prefixFields : List ExecutableField :=
    { parentType := parentType
      responseName := responseName
      fieldName := fieldName
      arguments := arguments
      selectionSet := selectionSet } :: fields
  let later : ExecutableField :=
    { parentType := parentType
      responseName := responseName
      fieldName := fieldName
      arguments := laterArguments
      selectionSet := laterSelectionSet }
  let prefixCompleted :=
    GraphQL.Execution.completeValue schema resolvers variableValues
      (completionDepth + 1) fieldDefinition.outputType prefixFields
      resolvedValue
  let laterCompleted :=
    completeResolvedValue schema resolvers variableValues (completionDepth + 1)
      fieldDefinition.outputType laterSelectionSet resolvedValue
      (some (resultValueOrNull prefixCompleted))
  have hprefix :
      GroupedFieldVisitAlignedEquivalent responseName
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source (executableFieldSelections prefixFields) (.object []))
        (GraphQL.Execution.singleFieldResult responseName prefixCompleted) := by
    simpa [prefixFields, prefixCompleted] using hprefixAligned
  have htail :
      visitSubfields schema resolvers variableValues (completionDepth + 2)
        parentType source (executableFieldSelections [later])
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source (executableFieldSelections prefixFields)
          (.object [])).fst =
      mergeResponseFieldResult responseName laterCompleted
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source (executableFieldSelections prefixFields)
          (.object [])).fst := by
    rw [hprefix.1]
    cases hprefixCompleted : prefixCompleted with
    | error prefixErrors =>
        have hlaterVisit :=
          visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
            schema resolvers variableValues completionDepth parentType source
            responseName fieldName laterArguments laterSelectionSet
            fieldDefinition resolvedValue .null hlookup hresolveLater
        simpa [prefixCompleted, laterCompleted, groupedFieldVisitResult,
          GraphQL.Execution.singleFieldResult, hprefixCompleted,
          resultValueOrNull, later] using hlaterVisit
    | ok prefixResult =>
        rcases prefixResult with ⟨prefixValue, prefixErrors⟩
        have hlaterVisit :=
          visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
            schema resolvers variableValues completionDepth parentType source
            responseName fieldName laterArguments laterSelectionSet
            fieldDefinition resolvedValue prefixValue hlookup hresolveLater
        simpa [prefixCompleted, laterCompleted, groupedFieldVisitResult,
          GraphQL.Execution.singleFieldResult, hprefixCompleted, later,
          resultValueOrNull, Nat.add_assoc] using hlaterVisit
  have haligned :
      ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse prefixCompleted
          laterCompleted)
        (GraphQL.Execution.completeValue schema resolvers variableValues
          (completionDepth + 1) fieldDefinition.outputType (prefixFields ++ [later])
          resolvedValue) := by
    dsimp [prefixCompleted, laterCompleted]
    exact
      completeValue_group_append_one_result_aligned_spec schema resolvers
        variableValues fieldDefinition.outputType (completionDepth + 1)
        resolvedValue prefixFields later
        hprefixChildren hobjects hchildren
  simpa [prefixFields, later, prefixCompleted, laterCompleted,
    executableFieldSelections, List.map_append] using
    executeRootSelectionSet_append_one_visit_aligned_of_complete schema resolvers
      variableValues (completionDepth + 2) parentType source
      (executableFieldSelections prefixFields) (executableFieldSelections [later])
      responseName prefixCompleted laterCompleted
      (GraphQL.Execution.completeValue schema resolvers variableValues
        (completionDepth + 1) fieldDefinition.outputType (prefixFields ++ [later])
        resolvedValue)
      hprefix htail haligned

theorem
    executeRootSelectionSet_executableFieldSelections_append_one_visit_aligned_resolved_of_aligned_children
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName fieldName : Name)
    (arguments laterArguments : List Argument)
    (selectionSet laterSelectionSet : List Selection) (fields : List ExecutableField)
    (fieldDefinition : FieldDefinition) (resolvedValue : ResolverValue ObjectIdentity)
    (hprefixAligned
      : GroupedFieldVisitAlignedEquivalent responseName
          (visitSubfields schema resolvers variableValues (completionDepth + 2)
            parentType source
            (executableFieldSelections
              ({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields))
            (.object []))
          (GraphQL.Execution.singleFieldResult responseName
            (GraphQL.Execution.completeValue schema resolvers variableValues
              (completionDepth + 1) fieldDefinition.outputType
              ({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              resolvedValue)))
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hresolveLater
      : resolvers.resolve parentType fieldName laterArguments source = some resolvedValue)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolvedValue runtimeType identity
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ({
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet
                    }
                    :: fields)))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ({
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet
                    }
                    :: fields))))
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolvedValue runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ({
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet
                    }
                    :: fields))
                (.object [])).fst
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) laterSelectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    ({
                        parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet
                      }
                      :: fields))
                  (.object [])).fst).fst)
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolvedValue runtimeType identity
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (({
                        parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet
                      }
                      :: fields)
                    ++ [{
                          parentType := parentType
                          responseName := responseName
                          fieldName := fieldName
                          arguments := laterArguments
                          selectionSet := laterSelectionSet
                        }])))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (({
                        parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet
                      }
                      :: fields)
                    ++ [{
                          parentType := parentType
                          responseName := responseName
                          fieldName := fieldName
                          arguments := laterArguments
                          selectionSet := laterSelectionSet
                        }]))))
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 2) parentType source
          (executableFieldSelections
            (({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              ++ [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet
                  }])))
        (GraphQL.Execution.singleFieldResult responseName
          (GraphQL.Execution.completeValue schema resolvers variableValues
            (completionDepth + 1) fieldDefinition.outputType
            (({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              ++ [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet
                  }])
            resolvedValue)) := by
  let prefixFields : List ExecutableField :=
    { parentType := parentType
      responseName := responseName
      fieldName := fieldName
      arguments := arguments
      selectionSet := selectionSet } :: fields
  let later : ExecutableField :=
    { parentType := parentType
      responseName := responseName
      fieldName := fieldName
      arguments := laterArguments
      selectionSet := laterSelectionSet }
  let prefixCompleted :=
    GraphQL.Execution.completeValue schema resolvers variableValues
      (completionDepth + 1) fieldDefinition.outputType prefixFields
      resolvedValue
  let laterCompleted :=
    completeResolvedValue schema resolvers variableValues (completionDepth + 1)
      fieldDefinition.outputType laterSelectionSet resolvedValue
      (some (resultValueOrNull prefixCompleted))
  have hprefix :
      GroupedFieldVisitAlignedEquivalent responseName
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source (executableFieldSelections prefixFields) (.object []))
        (GraphQL.Execution.singleFieldResult responseName prefixCompleted) := by
    simpa [prefixFields, prefixCompleted] using hprefixAligned
  have htail :
      visitSubfields schema resolvers variableValues (completionDepth + 2)
        parentType source (executableFieldSelections [later])
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source (executableFieldSelections prefixFields)
          (.object [])).fst =
      mergeResponseFieldResult responseName laterCompleted
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source (executableFieldSelections prefixFields)
          (.object [])).fst := by
    rw [hprefix.1]
    cases hprefixCompleted : prefixCompleted with
    | error prefixErrors =>
        have hlaterVisit :=
          visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
            schema resolvers variableValues completionDepth parentType source
            responseName fieldName laterArguments laterSelectionSet
            fieldDefinition resolvedValue .null hlookup hresolveLater
        simpa [prefixCompleted, laterCompleted, groupedFieldVisitResult,
          GraphQL.Execution.singleFieldResult, hprefixCompleted,
          resultValueOrNull, later] using hlaterVisit
    | ok prefixResult =>
        rcases prefixResult with ⟨prefixValue, prefixErrors⟩
        have hlaterVisit :=
          visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
            schema resolvers variableValues completionDepth parentType source
            responseName fieldName laterArguments laterSelectionSet
            fieldDefinition resolvedValue prefixValue hlookup hresolveLater
        simpa [prefixCompleted, laterCompleted, groupedFieldVisitResult,
          GraphQL.Execution.singleFieldResult, hprefixCompleted, later,
          resultValueOrNull, Nat.add_assoc] using hlaterVisit
  have haligned :
      ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse prefixCompleted
          laterCompleted)
        (GraphQL.Execution.completeValue schema resolvers variableValues
          (completionDepth + 1) fieldDefinition.outputType (prefixFields ++ [later])
          resolvedValue) := by
    dsimp [prefixCompleted, laterCompleted]
    exact
      completeValue_group_append_one_result_aligned_spec_of_aligned_children
        schema resolvers variableValues fieldDefinition.outputType
        (completionDepth + 1) resolvedValue prefixFields later
        hprefixChildren hobjects hchildren
  simpa [prefixFields, later, prefixCompleted, laterCompleted,
    executableFieldSelections, List.map_append] using
    executeRootSelectionSet_append_one_visit_aligned_of_complete schema resolvers
      variableValues (completionDepth + 2) parentType source
      (executableFieldSelections prefixFields) (executableFieldSelections [later])
      responseName prefixCompleted laterCompleted
      (GraphQL.Execution.completeValue schema resolvers variableValues
        (completionDepth + 1) fieldDefinition.outputType (prefixFields ++ [later])
        resolvedValue)
      hprefix htail haligned

theorem
    visitSubfields_executableFieldSelections_append_one_visit_aligned_resolved_of_aligned_children
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName fieldName : Name)
    (arguments laterArguments : List Argument)
    (selectionSet laterSelectionSet : List Selection) (fields : List ExecutableField)
    (fieldDefinition : FieldDefinition) (resolvedValue : ResolverValue ObjectIdentity)
    (hprefixAligned
      : GroupedFieldVisitAlignedEquivalent responseName
          (visitSubfields schema resolvers variableValues (completionDepth + 2)
            parentType source
            (executableFieldSelections
              ({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields))
            (.object []))
          (GraphQL.Execution.singleFieldResult responseName
            (GraphQL.Execution.completeValue schema resolvers variableValues
              (completionDepth + 1) fieldDefinition.outputType
              ({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              resolvedValue)))
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hresolveLater
      : resolvers.resolve parentType fieldName laterArguments source = some resolvedValue)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject (some resolvedValue) runtimeType identity
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ({
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet
                    }
                    :: fields)))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ({
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet
                    }
                    :: fields))))
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject (some resolvedValue) runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ({
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet
                    }
                    :: fields))
                (.object [])).fst
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) laterSelectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet
                    ({
                        parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet
                      }
                      :: fields))
                  (.object [])).fst).fst)
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject (some resolvedValue) runtimeType identity
          -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (({
                        parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet
                      }
                      :: fields)
                    ++ [{
                          parentType := parentType
                          responseName := responseName
                          fieldName := fieldName
                          arguments := laterArguments
                          selectionSet := laterSelectionSet
                        }])))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  (({
                        parentType := parentType
                        responseName := responseName
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet
                      }
                      :: fields)
                    ++ [{
                          parentType := parentType
                          responseName := responseName
                          fieldName := fieldName
                          arguments := laterArguments
                          selectionSet := laterSelectionSet
                        }]))))
    : GroupedFieldVisitAlignedEquivalent responseName
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source
          (executableFieldSelections
            (({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              ++ [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet
                  }]))
          (.object []))
        (GraphQL.Execution.singleFieldResult responseName
          (GraphQL.Execution.completeValue schema resolvers variableValues
            (completionDepth + 1) fieldDefinition.outputType
            (({
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }
                :: fields)
              ++ [{
                    parentType := parentType
                    responseName := responseName
                    fieldName := fieldName
                    arguments := laterArguments
                    selectionSet := laterSelectionSet
                  }])
            resolvedValue)) := by
  let prefixFields : List ExecutableField :=
    { parentType := parentType
      responseName := responseName
      fieldName := fieldName
      arguments := arguments
      selectionSet := selectionSet } :: fields
  let later : ExecutableField :=
    { parentType := parentType
      responseName := responseName
      fieldName := fieldName
      arguments := laterArguments
      selectionSet := laterSelectionSet }
  let prefixCompleted :=
    GraphQL.Execution.completeValue schema resolvers variableValues
      (completionDepth + 1) fieldDefinition.outputType prefixFields
      resolvedValue
  let laterCompleted :=
    completeResolvedValue schema resolvers variableValues (completionDepth + 1)
      fieldDefinition.outputType laterSelectionSet resolvedValue
      (some (resultValueOrNull prefixCompleted))
  have hprefix :
      GroupedFieldVisitAlignedEquivalent responseName
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source (executableFieldSelections prefixFields) (.object []))
        (GraphQL.Execution.singleFieldResult responseName prefixCompleted) := by
    simpa [prefixFields, prefixCompleted] using hprefixAligned
  have htail :
      visitSubfields schema resolvers variableValues (completionDepth + 2)
        parentType source (executableFieldSelections [later])
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source (executableFieldSelections prefixFields)
          (.object [])).fst =
      mergeResponseFieldResult responseName laterCompleted
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source (executableFieldSelections prefixFields)
          (.object [])).fst := by
    rw [hprefix.1]
    cases hprefixCompleted : prefixCompleted with
    | error prefixErrors =>
        have hlaterVisit :=
          visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
            schema resolvers variableValues completionDepth parentType source
            responseName fieldName laterArguments laterSelectionSet
            fieldDefinition resolvedValue .null hlookup hresolveLater
        simpa [prefixCompleted, laterCompleted, groupedFieldVisitResult,
          GraphQL.Execution.singleFieldResult, hprefixCompleted,
          resultValueOrNull, later] using hlaterVisit
    | ok prefixResult =>
        rcases prefixResult with ⟨prefixValue, prefixErrors⟩
        have hlaterVisit :=
          visitSubfields_executableFieldSelections_single_existing_eq_merge_complete
            schema resolvers variableValues completionDepth parentType source
            responseName fieldName laterArguments laterSelectionSet
            fieldDefinition resolvedValue prefixValue hlookup hresolveLater
        simpa [prefixCompleted, laterCompleted, groupedFieldVisitResult,
          GraphQL.Execution.singleFieldResult, hprefixCompleted, later,
          resultValueOrNull, Nat.add_assoc] using hlaterVisit
  have haligned :
      ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse prefixCompleted
          laterCompleted)
        (GraphQL.Execution.completeValue schema resolvers variableValues
          (completionDepth + 1) fieldDefinition.outputType (prefixFields ++ [later])
          resolvedValue) := by
    dsimp [prefixCompleted, laterCompleted]
    exact
      completeValue_group_append_one_result_aligned_spec_of_aligned_children
        schema resolvers variableValues fieldDefinition.outputType
        (completionDepth + 1) resolvedValue prefixFields later
        hprefixChildren hobjects hchildren
  simpa [prefixFields, later, prefixCompleted, laterCompleted,
    executableFieldSelections, List.map_append] using
    visitSubfields_append_one_visit_aligned_of_complete schema resolvers
      variableValues (completionDepth + 2) parentType source
      (executableFieldSelections prefixFields) (executableFieldSelections [later])
      responseName prefixCompleted laterCompleted
      (GraphQL.Execution.completeValue schema resolvers variableValues
        (completionDepth + 1) fieldDefinition.outputType (prefixFields ++ [later])
        resolvedValue)
      hprefix htail haligned

end Eager
end ExecutionUngrouped
end Algorithms

end GraphQL
