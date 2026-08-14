import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ExecutionPrelude

/-!
Field directive execution cases for complete normalization static collection.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

theorem collectFields_field_directives_skipped_eq
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = false
      -> Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = Execution.collectFields schema variableValues parentType source rest := by
  intro hskip
  rw [GroundTypeNormalization.collectFields_cons]
  simp [Execution.collectSelection, hskip]
  exact GroundTypeNormalization.mergeExecutableGroups_nil_left_collectFields_eq
    schema variableValues parentType source rest

theorem executeSelectionSet_field_directives_skipped_eq
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source rest := by
  intro hskip
  apply executeSelectionSet_eq_of_collectFields_eq
  exact collectFields_field_directives_skipped_eq schema variableValues
    parentType source responseName fieldName arguments directives selectionSet
    rest hskip

theorem collectFields_field_directives_allowed_exists
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = true
      -> ∃ sourceFields sourceRest,
          Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (
              responseName,
              {
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              :: sourceFields
            )
            :: sourceRest := by
  intro hallow
  let sourceField : Execution.ExecutableField :=
    {
      parentType := parentType,
      responseName := responseName,
      fieldName := fieldName,
      arguments := arguments,
      selectionSet := selectionSet
    }
  let restGroups :=
    Execution.collectFields schema variableValues parentType source rest
  rcases
      GroundTypeNormalization.mergeExecutableGroups_preserves_head
        responseName [sourceField] [] restGroups with
    ⟨appendedFields, sourceRest, hmerge⟩
  refine ⟨appendedFields, sourceRest, ?_⟩
  rw [GroundTypeNormalization.collectFields_cons]
  simp [Execution.collectSelection, hallow]
  simpa [sourceField, restGroups] using hmerge

theorem collectFields_field_directives_allowed_cons_of_responseName_not_mem
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = true
      -> responseName
          ∉ (Execution.collectFields schema variableValues parentType source rest).map
              Prod.fst
      -> Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (
              responseName,
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }]
            )
            :: Execution.collectFields schema variableValues parentType source rest := by
  intro hallow hnotin
  rw [GroundTypeNormalization.collectFields_cons]
  simp [Execution.collectSelection, hallow]
  rw [mergeExecutableGroups_eq_append_of_namesDisjoint]
  · simp
  · intro name hleft hright
    simp at hleft
    subst name
    exact hnotin hright
  · exact collectFields_namesNodup schema
      variableValues parentType source rest

theorem collectFields_field_directives_allowed_exists_of_case
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.field responseName fieldName arguments directives
                      selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> ∃ sourceFields sourceRest,
          Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (
              responseName,
              {
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              :: sourceFields
            )
            :: sourceRest := by
  intro hagrees hsourceVars hallow
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_field_head
      variableValues boolCase operation responseName fieldName arguments
      directives selectionSet rest hagrees hsourceVars
  have hexecAllow :
      Execution.selectionDirectivesAllowBool variableValues directives =
        true := by
    rw [← hdirectiveEq]
    exact hallow
  exact collectFields_field_directives_allowed_exists schema variableValues
    parentType source responseName fieldName arguments directives selectionSet
    rest hexecAllow

theorem collectFields_field_directives_allowed_cons_of_case_not_mem
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.field responseName fieldName arguments directives
                      selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> responseName
          ∉ (Execution.collectFields schema variableValues parentType source rest).map
              Prod.fst
      -> Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (
              responseName,
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }]
            )
            :: Execution.collectFields schema variableValues parentType source rest := by
  intro hagrees hsourceVars hallow hnotin
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_field_head
      variableValues boolCase operation responseName fieldName arguments
      directives selectionSet rest hagrees hsourceVars
  have hexecAllow :
      Execution.selectionDirectivesAllowBool variableValues directives =
        true := by
    rw [← hdirectiveEq]
    exact hallow
  exact collectFields_field_directives_allowed_cons_of_responseName_not_mem
    schema variableValues parentType source responseName fieldName arguments
    directives selectionSet rest hexecAllow hnotin

theorem collectFields_staticCollectForGround_field_allowed_lookup_none_exists
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : directivesAllowIn boolCase directives = true
      -> schema.lookupField lookupParent fieldName = none
      -> ∃ normalizedFields normalizedRest,
          Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema variables lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet :=
                  normalizeSelectionSetIn schema variables
                    boolCase lookupParent selectionSet
              }
              :: normalizedFields
            )
            :: normalizedRest := by
  intro hallow hlookup
  rw [staticCollectForGround_field_allowed schema variables
    lookupParent groundType responseName fieldName boolCase arguments
    directives selectionSet rest hallow]
  simp [hlookup]
  exact GroundTypeNormalization.collectFields_field_head_exists schema
    variableValues lookupParent source responseName fieldName arguments
    (normalizeSelectionSetIn schema variables boolCase
      lookupParent selectionSet)
    (staticCollectForGround schema variables lookupParent
      groundType boolCase rest)

theorem collectFields_staticCollectForGround_field_allowed_lookup_some_exists
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : directivesAllowIn boolCase directives = true
      -> schema.lookupField lookupParent fieldName = some fieldDefinition
      -> ∃ normalizedFields normalizedRest,
          Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema variables lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet :=
                  normalizeBoolCaseForType schema boolCase
                    fieldDefinition.outputType.namedType selectionSet
              }
              :: normalizedFields
            )
            :: normalizedRest := by
  intro hallow hlookup
  rw [staticCollectForGround_field_allowed schema variables
    lookupParent groundType responseName fieldName boolCase arguments
    directives selectionSet rest hallow]
  simp [hlookup]
  exact GroundTypeNormalization.collectFields_field_head_exists schema
    variableValues lookupParent source responseName fieldName arguments
    (normalizeBoolCaseForType schema boolCase fieldDefinition.outputType.namedType selectionSet)
    (staticCollectForGround schema variables lookupParent
      groundType boolCase rest)

theorem executeSelectionSet_staticCollectForGround_field_allowed_lookup_none_group_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail : List (Name × List Execution.ExecutableField))
    : directivesAllowIn boolCase directives = true
      -> schema.lookupField lookupParent fieldName = none
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema variables lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet :=
                  normalizeSelectionSetIn schema variables
                    boolCase lookupParent selectionSet
              }
              :: normalizedFields
            )
            :: normalizedTail
      -> Execution.collectFields schema variableValues lookupParent source
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              :: sourceFields
            )
            :: sourceTail
      -> Execution.executeCollectedFields schema resolvers variableValues depth source
            normalizedTail
          = Execution.executeCollectedFields schema resolvers variableValues depth
              source sourceTail
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema variables lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hallow hlookup hnormalizedCollect hsourceCollect htail
  have hnormalizedCollect' :
      Execution.collectFields schema variableValues lookupParent source
          (Selection.field responseName fieldName arguments []
            (normalizeSelectionSetIn schema variables
              boolCase lookupParent selectionSet)
            :: staticCollectForGround schema variables
              lookupParent groundType boolCase rest)
        =
        (responseName, {
          parentType := lookupParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet :=
            normalizeSelectionSetIn schema variables
              boolCase lookupParent selectionSet
        } :: normalizedFields) :: normalizedTail := by
    simpa [staticCollectForGround_field_allowed schema variables
      lookupParent groundType responseName fieldName boolCase arguments
      directives selectionSet rest hallow, hlookup] using hnormalizedCollect
  rw [staticCollectForGround_field_allowed schema variables
    lookupParent groundType responseName fieldName boolCase arguments
    directives selectionSet rest hallow]
  simp [hlookup]
  exact executeSelectionSet_field_head_group_eq_of_completeValue
    schema resolvers variableValues depth lookupParent source responseName
    fieldName arguments directives
    (normalizeSelectionSetIn schema variables boolCase
      lookupParent selectionSet)
    selectionSet
    (staticCollectForGround schema variables lookupParent
      groundType boolCase rest)
    rest normalizedFields sourceFields normalizedTail sourceTail
    hnormalizedCollect' hsourceCollect
    (by simp [hlookup]) htail

theorem executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_group_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail : List (Name × List Execution.ExecutableField))
    : directivesAllowIn boolCase directives = true
      -> schema.lookupField lookupParent fieldName = some fieldDefinition
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema variables lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet :=
                  normalizeBoolCaseForType schema boolCase
                    fieldDefinition.outputType.namedType selectionSet
              }
              :: normalizedFields
            )
            :: normalizedTail
      -> Execution.collectFields schema variableValues lookupParent source
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              :: sourceFields
            )
            :: sourceTail
      -> (match Execution.resolveFieldValue schema resolvers variableValues
                  fieldDefinition lookupParent fieldName arguments source with
          | some value =>
              Execution.completeValue schema resolvers variableValues (depth - 1)
                fieldDefinition.outputType
                ({
                    parentType := lookupParent,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet :=
                      normalizeBoolCaseForType schema boolCase
                        fieldDefinition.outputType.namedType selectionSet
                  }
                  :: normalizedFields)
                value
              = Execution.completeValue schema resolvers variableValues (depth - 1)
                  fieldDefinition.outputType
                  ({
                      parentType := lookupParent,
                      responseName := responseName,
                      fieldName := fieldName,
                      arguments := arguments,
                      selectionSet := selectionSet
                    }
                    :: sourceFields)
                  value
          | none => True)
      -> Execution.executeCollectedFields schema resolvers variableValues depth source
            normalizedTail
          = Execution.executeCollectedFields schema resolvers variableValues depth
              source sourceTail
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema variables lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hallow hlookup hnormalizedCollect hsourceCollect hcomplete htail
  have hnormalizedCollect' :
      Execution.collectFields schema variableValues lookupParent source
          (Selection.field responseName fieldName arguments []
            (normalizeBoolCaseForType schema boolCase fieldDefinition.outputType.namedType selectionSet)
            :: staticCollectForGround schema variables
              lookupParent groundType boolCase rest)
        =
        (responseName, {
          parentType := lookupParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet :=
            normalizeBoolCaseForType schema boolCase fieldDefinition.outputType.namedType selectionSet
        } :: normalizedFields) :: normalizedTail := by
    simpa [staticCollectForGround_field_allowed schema variables
      lookupParent groundType responseName fieldName boolCase arguments
      directives selectionSet rest hallow, hlookup] using hnormalizedCollect
  rw [staticCollectForGround_field_allowed schema variables
    lookupParent groundType responseName fieldName boolCase arguments
    directives selectionSet rest hallow]
  simp [hlookup]
  exact executeSelectionSet_field_head_group_eq_of_completeValue
    schema resolvers variableValues depth lookupParent source responseName
    fieldName arguments directives
    (normalizeBoolCaseForType schema boolCase fieldDefinition.outputType.namedType selectionSet)
    selectionSet
    (staticCollectForGround schema variables lookupParent
      groundType boolCase rest)
    rest normalizedFields sourceFields normalizedTail sourceTail
    hnormalizedCollect' hsourceCollect
    (by
      cases hresolved :
          Execution.resolveFieldValue schema resolvers variableValues
            fieldDefinition lookupParent fieldName arguments source with
      | none =>
          simp [Execution.resolveFieldValueByName, hlookup, hresolved]
      | some value =>
          simpa [Execution.resolveFieldValueByName, hlookup, hresolved]
            using hcomplete) htail

theorem
    executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_no_duplicate_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation) (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase) (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.field responseName fieldName arguments directives
                      selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> schema.lookupField lookupParent fieldName = some fieldDefinition
      -> responseName
          ∉ (Execution.collectFields schema variableValues lookupParent source
              (staticCollectForGround schema
                (operationBoolVars operation) lookupParent
                groundType boolCase rest)).map
              Prod.fst
      -> responseName
          ∉ (Execution.collectFields schema variableValues lookupParent source rest).map
              Prod.fst
      -> (match Execution.resolveFieldValue schema resolvers variableValues
                  fieldDefinition lookupParent fieldName arguments source with
          | some value =>
              Execution.completeValue schema resolvers variableValues (depth - 1)
                fieldDefinition.outputType
                [{
                  parentType := lookupParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet :=
                    normalizeBoolCaseForType schema boolCase
                      fieldDefinition.outputType.namedType selectionSet
                }]
                value
              = Execution.completeValue schema resolvers variableValues (depth - 1)
                  fieldDefinition.outputType
                  [{
                    parentType := lookupParent,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := selectionSet
                  }]
                  value
          | none => True)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source rest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hagrees hsourceVars hallow hlookup hnormalizedNotin hsourceNotin
    hcomplete htail
  let normalizedSelectionSet :=
    normalizeBoolCaseForType schema boolCase
      fieldDefinition.outputType.namedType selectionSet
  let normalizedRest :=
    staticCollectForGround schema
      (operationBoolVars operation) lookupParent groundType
      boolCase rest
  have hnormalizedCollect :
      Execution.collectFields schema variableValues lookupParent source
          (staticCollectForGround schema
            (operationBoolVars operation) lookupParent
            groundType boolCase
            (Selection.field responseName fieldName arguments directives
              selectionSet :: rest))
        =
        (responseName, [{
          parentType := lookupParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := normalizedSelectionSet
        }])
          :: Execution.collectFields schema variableValues lookupParent source
            normalizedRest := by
    rw [staticCollectForGround_field_allowed schema
      (operationBoolVars operation) lookupParent groundType
      responseName fieldName boolCase arguments directives selectionSet rest
      hallow]
    simp [hlookup, normalizedSelectionSet, normalizedRest]
    exact GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
      schema variableValues lookupParent source responseName fieldName
      arguments normalizedSelectionSet normalizedRest hnormalizedNotin
  have hsourceCollect :
      Execution.collectFields schema variableValues lookupParent source
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest)
        =
        (responseName, [{
          parentType := lookupParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }])
          :: Execution.collectFields schema variableValues lookupParent source
            rest :=
    collectFields_field_directives_allowed_cons_of_case_not_mem schema
      variableValues operation lookupParent source boolCase responseName
      fieldName arguments directives selectionSet rest hagrees hsourceVars
      hallow hsourceNotin
  have htailCollected :
      Execution.executeCollectedFields schema resolvers variableValues depth
          source
          (Execution.collectFields schema variableValues lookupParent source
            normalizedRest)
        =
      Execution.executeCollectedFields schema resolvers variableValues depth
        source
        (Execution.collectFields schema variableValues lookupParent source
          rest) := by
    simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      normalizedRest] using htail
  apply executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_group_case
    schema resolvers variableValues
    (operationBoolVars operation) depth lookupParent
    groundType source boolCase responseName fieldName arguments directives
    selectionSet rest fieldDefinition [] []
    (Execution.collectFields schema variableValues lookupParent source
      normalizedRest)
    (Execution.collectFields schema variableValues lookupParent source rest)
  · exact hallow
  · exact hlookup
  · simpa [normalizedSelectionSet, normalizedRest] using hnormalizedCollect
  · exact hsourceCollect
  · simpa [normalizedSelectionSet, Execution.mergedFieldSelectionSet]
      using hcomplete
  · exact htailCollected

theorem
    executeSelectionSet_staticCollectForGround_field_allowed_lookup_none_no_duplicate_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation) (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase) (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.field responseName fieldName arguments directives
                      selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> schema.lookupField lookupParent fieldName = none
      -> responseName
          ∉ (Execution.collectFields schema variableValues lookupParent source
              (staticCollectForGround schema
                (operationBoolVars operation) lookupParent
                groundType boolCase rest)).map
              Prod.fst
      -> responseName
          ∉ (Execution.collectFields schema variableValues lookupParent source rest).map
              Prod.fst
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source rest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hagrees hsourceVars hallow hlookup hnormalizedNotin hsourceNotin htail
  let normalizedSelectionSet :=
    normalizeSelectionSetIn schema
      (operationBoolVars operation) boolCase lookupParent
      selectionSet
  let normalizedRest :=
    staticCollectForGround schema
      (operationBoolVars operation) lookupParent groundType
      boolCase rest
  have hnormalizedCollect :
      Execution.collectFields schema variableValues lookupParent source
          (staticCollectForGround schema
            (operationBoolVars operation) lookupParent
            groundType boolCase
            (Selection.field responseName fieldName arguments directives
              selectionSet :: rest))
        =
        (responseName, [{
          parentType := lookupParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := normalizedSelectionSet
        }])
          :: Execution.collectFields schema variableValues lookupParent source
            normalizedRest := by
    rw [staticCollectForGround_field_allowed schema
      (operationBoolVars operation) lookupParent groundType
      responseName fieldName boolCase arguments directives selectionSet rest
      hallow]
    simp [hlookup, normalizedSelectionSet, normalizedRest]
    exact GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
      schema variableValues lookupParent source responseName fieldName
      arguments normalizedSelectionSet normalizedRest hnormalizedNotin
  have hsourceCollect :
      Execution.collectFields schema variableValues lookupParent source
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest)
        =
        (responseName, [{
          parentType := lookupParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }])
          :: Execution.collectFields schema variableValues lookupParent source
            rest :=
    collectFields_field_directives_allowed_cons_of_case_not_mem schema
      variableValues operation lookupParent source boolCase responseName
      fieldName arguments directives selectionSet rest hagrees hsourceVars
      hallow hsourceNotin
  have htailCollected :
      Execution.executeCollectedFields schema resolvers variableValues depth
          source
          (Execution.collectFields schema variableValues lookupParent source
            normalizedRest)
        =
      Execution.executeCollectedFields schema resolvers variableValues depth
        source
        (Execution.collectFields schema variableValues lookupParent source
          rest) := by
    simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      normalizedRest] using htail
  apply executeSelectionSet_staticCollectForGround_field_allowed_lookup_none_group_case
    schema resolvers variableValues
    (operationBoolVars operation) depth lookupParent
    groundType source boolCase responseName fieldName arguments directives
    selectionSet rest [] []
    (Execution.collectFields schema variableValues lookupParent source
      normalizedRest)
    (Execution.collectFields schema variableValues lookupParent source rest)
  · exact hallow
  · exact hlookup
  · simpa [normalizedSelectionSet, normalizedRest] using hnormalizedCollect
  · exact hsourceCollect
  · exact htailCollected

end CompleteNormalization

end NormalForm

end GraphQL
