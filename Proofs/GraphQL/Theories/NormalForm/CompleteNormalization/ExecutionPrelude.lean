import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationWrappers
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ScopedSelections
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FieldOutput
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldCollection
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldSemantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.RuntimeFragmentSemantics
import Proofs.GraphQL.Execution.FieldCollection
import Proofs.GraphQL.Execution.ResolverValue

/-!
Shared collect/execute field-group helpers for complete normalization.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

theorem collectFields_append_left_nil
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (left right : List Selection)
    : Execution.collectFields schema variableValues parentType source left = []
      -> Execution.collectFields schema variableValues parentType source (left ++ right)
          = Execution.collectFields schema variableValues parentType source right := by
  intro hleft
  rw [collectFields_append]
  rw [hleft]
  exact GroundTypeNormalization.mergeExecutableGroups_nil_left_collectFields_eq
    schema variableValues parentType source right

theorem collectFields_append_right_nil
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (left right : List Selection)
    : Execution.collectFields schema variableValues parentType source right = []
      -> Execution.collectFields schema variableValues parentType source (left ++ right)
          = Execution.collectFields schema variableValues parentType source left := by
  intro hright
  rw [collectFields_append]
  rw [hright]
  simp [Execution.mergeExecutableGroups]

theorem collectedResponseSelectionSet_collectFields_allFields_topNoDirectives
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName : Name)
    : ∀ selectionSet,
        selectionsAllFields selectionSet
        -> (∀ candidateResponseName candidateFieldName candidateArguments
              candidateDirectives candidateSubselections,
              Selection.field candidateResponseName candidateFieldName
                  candidateArguments candidateDirectives candidateSubselections
                ∈ selectionSet
              -> candidateDirectives = [])
        -> collectedResponseSelectionSet responseName
              (Execution.collectFields schema variableValues parentType source
                selectionSet)
            = mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  selectionSet)
  | [], _hall, _hdirectives => by
      simp [Execution.collectFields,
        collectedResponseSelectionSet,
        fieldSelectionsWithResponseNameInScope, mergeSelectionSets]
  | selection :: rest, hall, hdirectives => by
      have htailAll : selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      have htailDirectives :
          ∀ candidateResponseName candidateFieldName candidateArguments
              candidateDirectives candidateSubselections,
            Selection.field candidateResponseName candidateFieldName
                candidateArguments candidateDirectives candidateSubselections
                ∈ rest ->
              candidateDirectives = [] := by
        intro candidateResponseName candidateFieldName candidateArguments
          candidateDirectives candidateSubselections hmem
        exact hdirectives candidateResponseName candidateFieldName
          candidateArguments candidateDirectives candidateSubselections
          (List.mem_cons_of_mem selection hmem)
      have hrest :=
        collectedResponseSelectionSet_collectFields_allFields_topNoDirectives
          schema variableValues parentType source responseName rest htailAll
          htailDirectives
      have hheadField : Selection.isField selection :=
        hall selection (by simp)
      cases selection with
      | field fieldResponseName fieldName arguments directives subselections =>
          have hdirectivesHead : directives = [] :=
            hdirectives fieldResponseName fieldName arguments directives
              subselections (by simp)
          subst directives
          rw [GroundTypeNormalization.collectFields_field_noDirectives]
          rw [GroundTypeNormalization.collectedResponseSelectionSet_mergeExecutableGroups]
          · cases hresponse : fieldResponseName == responseName <;>
              simp [collectedResponseSelectionSet,
                fieldSelectionsWithResponseNameInScope, hresponse, hrest,
                mergeSelectionSets, Selection.subselections,
                Execution.mergedFieldSelectionSet]
          · exact collectFields_namesNodup schema
              variableValues parentType source rest
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

theorem
    mergedFieldSelectionSet_field_head_eq_fieldSelectionsWithResponseNameInScope_topNoDirectives
    (schema : Schema) (variableValues : Execution.VariableValues) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) (responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (sourceFields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField))
    : let sourceField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := subselections
        }
      selectionsAllFields
        (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> (∀ candidateResponseName candidateFieldName candidateArguments
            candidateDirectives candidateSubselections,
            Selection.field candidateResponseName candidateFieldName
                candidateArguments candidateDirectives candidateSubselections
              ∈ (Selection.field responseName fieldName arguments [] subselections
                  :: rest)
            -> candidateDirectives = [])
      -> Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments [] subselections :: rest)
          = (responseName, sourceField :: sourceFields) :: sourceRest
      -> Execution.mergedFieldSelectionSet (sourceField :: sourceFields)
          = subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest) := by
  intro sourceField hall hdirectives hcollect
  have hprojection :=
    collectedResponseSelectionSet_collectFields_allFields_topNoDirectives
      schema variableValues parentType source responseName
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      hall hdirectives
  simp [collectedResponseSelectionSet, hcollect,
    fieldSelectionsWithResponseNameInScope, mergeSelectionSets, Selection.subselections]
    at hprojection
  simpa [sourceField] using hprojection

theorem mergedFieldSelectionSet_staticCollect_field_head_eq_staticScopedFields
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields : List Execution.ExecutableField)
    (normalizedTail : List (Name × List Execution.ExecutableField))
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
      -> Execution.mergedFieldSelectionSet
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
          = normalizeBoolCaseForType schema boolCase
              fieldDefinition.outputType.namedType selectionSet
            ++ mergeSelectionSets
                (staticCollectCompleteScopedSelectionSet schema variables groundType
                  boolCase
                  (staticScopedFieldsWithResponseName schema boolCase lookupParent
                    groundType responseName rest)) := by
  intro hallow hlookup hcollect
  let normalizedSelectionSet :=
    normalizeBoolCaseForType schema boolCase fieldDefinition.outputType.namedType selectionSet
  let normalizedRest :=
    staticCollectForGround schema variables lookupParent
      groundType boolCase rest
  let normalizedField : Execution.ExecutableField := {
    parentType := lookupParent,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    selectionSet := normalizedSelectionSet
  }
  have hcollectHead :
      Execution.collectFields schema variableValues lookupParent source
          (Selection.field responseName fieldName arguments []
              normalizedSelectionSet
            :: normalizedRest)
        =
        (responseName, normalizedField :: normalizedFields)
          :: normalizedTail := by
    cases hnormalized :
        normalizeBoolCaseForType schema boolCase
          fieldDefinition.outputType.namedType selectionSet <;>
      simpa [staticCollectForGround_field_allowed schema variables
        lookupParent groundType responseName fieldName boolCase arguments
        directives selectionSet rest hallow, hlookup, normalizedSelectionSet,
        normalizedRest, normalizedField, hnormalized] using hcollect
  have hall :
      selectionsAllFields
        (Selection.field responseName fieldName arguments []
            normalizedSelectionSet
          :: normalizedRest) := by
    intro selection hmem
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst selection
      simp [Selection.isField]
    · exact staticCollectForGround_allFields schema variables
        lookupParent groundType boolCase rest selection htail
  have hdirectives :
      ∀ candidateResponseName candidateFieldName candidateArguments
          candidateDirectives candidateSubselections,
        Selection.field candidateResponseName candidateFieldName
            candidateArguments candidateDirectives candidateSubselections ∈
          (Selection.field responseName fieldName arguments []
              normalizedSelectionSet
            :: normalizedRest) ->
          candidateDirectives = [] := by
    intro candidateResponseName candidateFieldName candidateArguments
      candidateDirectives candidateSubselections hmem
    rcases List.mem_cons.mp hmem with hhead | htail
    · cases hhead
      rfl
    · rcases
        staticCollectForGround_field_shape schema variables
          lookupParent groundType boolCase htail with
        ⟨matchedResponseName, matchedFieldName, matchedArguments,
          matchedSelectionSet, hshape⟩
      cases hshape
      rfl
  have hprojection :=
    mergedFieldSelectionSet_field_head_eq_fieldSelectionsWithResponseNameInScope_topNoDirectives
      schema variableValues lookupParent source responseName fieldName
      arguments normalizedSelectionSet normalizedRest normalizedFields
      normalizedTail hall hdirectives hcollectHead
  simpa [normalizedSelectionSet, normalizedRest, normalizedField,
    fieldSelectionsWithResponseNameInScope_staticCollectForGround_scoped
      schema variables lookupParent lookupParent groundType responseName
      boolCase rest] using hprojection

theorem selectionsAllFields_append {left right : List Selection}
    : selectionsAllFields left
      -> selectionsAllFields right
      -> selectionsAllFields (left ++ right) := by
  intro hleft hright selection hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft selection hmem
  · exact hright selection hmem

theorem staticCollectCompleteScopedSelectionSet_allFields
    (schema : Schema) (variables : List BoolVar)
    (groundType : Name) (boolCase : BoolCase)
    : ∀ scopedSelections,
        selectionsAllFields
          (staticCollectCompleteScopedSelectionSet schema variables groundType
            boolCase scopedSelections)
  | [] => by
      simp [staticCollectCompleteScopedSelectionSet, selectionsAllFields]
  | scopedSelection :: rest => by
      cases scopedSelection with
      | mk lookupParent selection =>
          simp [staticCollectCompleteScopedSelectionSet,
            staticCollectCompleteScopedSelection]
          apply selectionsAllFields_append
          · exact staticCollectForGround_allFields schema variables
              lookupParent groundType boolCase [selection]
          · exact
              staticCollectCompleteScopedSelectionSet_allFields schema
                variables groundType boolCase rest

theorem staticCollectCompleteScopedSelectionSet_fields_no_directives
    (schema : Schema) (variables : List BoolVar)
    (groundType : Name) (boolCase : BoolCase)
    : ∀ {selection scopedSelections},
        selection
          ∈ staticCollectCompleteScopedSelectionSet schema variables groundType
              boolCase scopedSelections
        -> ∃ responseName fieldName arguments selectionSet,
            selection
            = Selection.field responseName fieldName arguments [] selectionSet := by
  intro selection scopedSelections hmem
  induction scopedSelections generalizing selection with
  | nil =>
      simp [staticCollectCompleteScopedSelectionSet] at hmem
  | cons scopedSelection rest ih =>
      cases scopedSelection with
      | mk lookupParent headSelection =>
          have hmem' :
              selection ∈
                  staticCollectForGround schema variables
                    lookupParent groundType boolCase [headSelection]
                ∨
              selection ∈
                  staticCollectCompleteScopedSelectionSet schema variables
                    groundType boolCase rest := by
            simpa [staticCollectCompleteScopedSelectionSet,
              staticCollectCompleteScopedSelection] using hmem
          rcases hmem' with hhead | htail
          · rcases
              staticCollectForGround_field_shape schema variables
                lookupParent groundType boolCase hhead with
              ⟨responseName, fieldName, arguments, selectionSet, hshape⟩
            exact ⟨responseName, fieldName, arguments, selectionSet, hshape⟩
          · exact
              ih htail

theorem staticCollectCompleteScopedSelectionSet_withoutFieldSelectionsWithResponseName
    (schema : Schema) (variables : List BoolVar)
    (groundType : Name) (boolCase : BoolCase)
    (responseName : Name)
    : ∀ scopedSelections,
        withoutFieldSelectionsWithResponseName schema responseName
          (staticCollectCompleteScopedSelectionSet schema variables groundType
            boolCase scopedSelections)
        = staticCollectCompleteScopedSelectionSet schema variables groundType
            boolCase
            (completeScopedSelectionSetWithoutFieldSelectionsWithResponseName schema
              responseName scopedSelections)
  | [] => by
      simp [staticCollectCompleteScopedSelectionSet,
        completeScopedSelectionSetWithoutFieldSelectionsWithResponseName,
        withoutFieldSelectionsWithResponseName]
  | scopedSelection :: rest => by
      cases scopedSelection with
      | mk lookupParent selection =>
          rw [staticCollectCompleteScopedSelectionSet]
          rw [withoutFieldSelectionsWithResponseName_append]
          unfold staticCollectCompleteScopedSelection
          change
            withoutFieldSelectionsWithResponseName schema responseName
                (staticCollectForGround schema variables
                  lookupParent groundType boolCase [selection])
              ++
              withoutFieldSelectionsWithResponseName schema responseName
                (staticCollectCompleteScopedSelectionSet schema variables
                  groundType boolCase rest)
            =
            staticCollectCompleteScopedSelectionSet schema variables groundType
              boolCase
              (completeScopedSelectionSetWithoutFieldSelectionsWithResponseName schema
                responseName
                ({ lookupParent := lookupParent, selection := selection }
                  :: rest))
          rw [← staticCollectForGround_withoutFieldSelectionsWithResponseName]
          rw [staticCollectCompleteScopedSelectionSet_withoutFieldSelectionsWithResponseName
            schema variables groundType boolCase responseName rest]
          cases selection with
          | field fieldResponseName fieldName arguments directives selectionSet =>
              cases hresponse : fieldResponseName == responseName <;>
                simp [completeScopedSelectionSetWithoutFieldSelectionsWithResponseName,
                  staticCollectCompleteScopedSelectionSet,
                  staticCollectCompleteScopedSelection,
                  staticCollectForGround,
                  withoutFieldSelectionsWithResponseName, hresponse]
          | inlineFragment typeCondition directives selectionSet =>
              simp [completeScopedSelectionSetWithoutFieldSelectionsWithResponseName,
                staticCollectCompleteScopedSelectionSet,
                staticCollectCompleteScopedSelection,
                withoutFieldSelectionsWithResponseName]

theorem mergedFieldSelectionSet_staticCollectCompleteScoped_field_head_eq_staticFields
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (execParent lookupParent groundType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection) (rest : List CompleteScopedSelection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields : List Execution.ExecutableField)
    (normalizedTail : List (Name × List Execution.ExecutableField))
    : directivesAllowIn boolCase directives = true
      -> schema.lookupField lookupParent fieldName = some fieldDefinition
      -> Execution.collectFields schema variableValues execParent source
            (staticCollectCompleteScopedSelectionSet schema variables groundType
              boolCase
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.field responseName fieldName arguments directives
                      selectionSet
                }
                :: rest))
          = (
              responseName,
              {
                parentType := execParent,
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
      -> Execution.mergedFieldSelectionSet
            ({
                parentType := execParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet :=
                  normalizeBoolCaseForType schema boolCase
                    fieldDefinition.outputType.namedType selectionSet
              }
              :: normalizedFields)
          = normalizeBoolCaseForType schema boolCase
              fieldDefinition.outputType.namedType selectionSet
            ++ mergeSelectionSets
                (staticCollectCompleteScopedSelectionSet schema variables groundType
                  boolCase
                  (completeScopedSelectionSetStaticFieldsWithResponseName schema
                    boolCase groundType responseName rest)) := by
  intro hallow hlookup hcollect
  let normalizedSelectionSet :=
    normalizeBoolCaseForType schema boolCase fieldDefinition.outputType.namedType selectionSet
  let normalizedRest :=
    staticCollectCompleteScopedSelectionSet schema variables groundType
      boolCase rest
  let normalizedField : Execution.ExecutableField := {
    parentType := execParent,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    selectionSet := normalizedSelectionSet
  }
  have hcollectHead :
      Execution.collectFields schema variableValues execParent source
          (Selection.field responseName fieldName arguments []
              normalizedSelectionSet
            :: normalizedRest)
        =
        (responseName, normalizedField :: normalizedFields)
          :: normalizedTail := by
    rw [staticCollectCompleteScopedSelectionSet,
      staticCollectCompleteScopedSelection] at hcollect
    rw [staticCollectForGround_field_allowed schema variables
      lookupParent groundType responseName fieldName boolCase arguments
      directives selectionSet [] hallow] at hcollect
    simp [hlookup, staticCollectForGround] at hcollect
    cases hnormalized :
        normalizeBoolCaseForType schema boolCase
          fieldDefinition.outputType.namedType selectionSet <;>
      simpa [normalizedSelectionSet, normalizedRest, normalizedField,
        hnormalized] using hcollect
  have hall :
      selectionsAllFields
        (Selection.field responseName fieldName arguments []
            normalizedSelectionSet
          :: normalizedRest) := by
    intro selection hmem
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst selection
      simp [Selection.isField]
    · exact
        staticCollectCompleteScopedSelectionSet_allFields schema variables
          groundType boolCase rest selection htail
  have hdirectives :
      ∀ candidateResponseName candidateFieldName candidateArguments
          candidateDirectives candidateSubselections,
        Selection.field candidateResponseName candidateFieldName
            candidateArguments candidateDirectives candidateSubselections ∈
          (Selection.field responseName fieldName arguments []
              normalizedSelectionSet
            :: normalizedRest) ->
          candidateDirectives = [] := by
    intro candidateResponseName candidateFieldName candidateArguments
      candidateDirectives candidateSubselections hmem
    rcases List.mem_cons.mp hmem with hhead | htail
    · cases hhead
      rfl
    · rcases
        staticCollectCompleteScopedSelectionSet_fields_no_directives schema
          variables groundType boolCase htail with
        ⟨matchedResponseName, matchedFieldName, matchedArguments,
          matchedSelectionSet, hshape⟩
      cases hshape
      rfl
  have hprojection :=
    mergedFieldSelectionSet_field_head_eq_fieldSelectionsWithResponseNameInScope_topNoDirectives
      schema variableValues execParent source responseName fieldName
      arguments normalizedSelectionSet normalizedRest normalizedFields
      normalizedTail hall hdirectives hcollectHead
  simpa [normalizedSelectionSet, normalizedRest, normalizedField,
    fieldSelectionsWithResponseNameInScope_staticCollectCompleteScopedSelectionSet
      schema variables execParent groundType responseName boolCase rest]
    using hprojection

theorem executeSelectionSet_eq_of_collectFields_eq
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (left right : List Selection)
    : Execution.collectFields schema variableValues parentType source left
        = Execution.collectFields schema variableValues parentType source right
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source left
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source right := by
  intro hcollect
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    hcollect]

theorem executeField_cons_eq_cons_of_completeValue
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (responseName : Name)
    (sourceField normalizedField : Execution.ExecutableField)
    (sourceFields normalizedFields : List Execution.ExecutableField)
    : normalizedField.parentType = sourceField.parentType
      -> normalizedField.fieldName = sourceField.fieldName
      -> normalizedField.arguments = sourceField.arguments
      -> (match schema.lookupField sourceField.parentType sourceField.fieldName,
                resolvers.resolve sourceField.parentType sourceField.fieldName
                  sourceField.arguments source with
          | some fieldDefinition, some value =>
              Execution.completeValue schema resolvers variableValues (depth - 1)
                fieldDefinition.outputType (normalizedField :: normalizedFields) value
              = Execution.completeValue schema resolvers variableValues (depth - 1)
                  fieldDefinition.outputType (sourceField :: sourceFields) value
          | _, _ => True)
      -> Execution.executeField schema resolvers variableValues depth source
            responseName (normalizedField :: normalizedFields)
          = Execution.executeField schema resolvers variableValues depth source
              responseName (sourceField :: sourceFields) := by
  intro hparent hfield harguments hcomplete
  cases depth with
  | zero =>
      simp [Execution.executeField]
  | succ fieldDepth =>
      simp [Execution.executeField, hparent, hfield, harguments]
      cases hlookup : schema.lookupField sourceField.parentType sourceField.fieldName with
      | none =>
          simp []
      | some fieldDefinition =>
          cases hresolved
                : resolvers.resolve sourceField.parentType sourceField.fieldName
                    sourceField.arguments source with
          | none =>
              simp []
          | some value =>
              have hcomplete' :
                  Execution.completeValue schema resolvers variableValues
                      fieldDepth fieldDefinition.outputType
                      (normalizedField :: normalizedFields) value =
                    Execution.completeValue schema resolvers variableValues
                      fieldDepth fieldDefinition.outputType
                      (sourceField :: sourceFields) value := by
                simpa [hlookup, hresolved] using hcomplete
              simp [Execution.singleFieldResult, hcomplete']

theorem executeSelectionSet_field_head_group_eq_of_completeValue
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (normalizedSubselections sourceSubselections normalizedRest sourceRest
      : List Selection)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail : List (Name × List Execution.ExecutableField))
    : let normalizedField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := normalizedSubselections
        }
      let sourceField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := sourceSubselections
        }
      Execution.collectFields schema variableValues parentType source
          (Selection.field responseName fieldName arguments [] normalizedSubselections
            :: normalizedRest)
        = (responseName, normalizedField :: normalizedFields) :: normalizedTail
      -> Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments directives
                sourceSubselections
              :: sourceRest)
          = (responseName, sourceField :: sourceFields) :: sourceTail
      -> (match schema.lookupField parentType fieldName,
                resolvers.resolve parentType fieldName arguments source with
          | some fieldDefinition, some value =>
              Execution.completeValue schema resolvers variableValues (depth - 1)
                fieldDefinition.outputType (normalizedField :: normalizedFields) value
              = Execution.completeValue schema resolvers variableValues (depth - 1)
                  fieldDefinition.outputType (sourceField :: sourceFields) value
          | _, _ => True)
      -> Execution.executeCollectedFields schema resolvers variableValues depth source
            normalizedTail
          = Execution.executeCollectedFields schema resolvers variableValues depth
              source sourceTail
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.field responseName fieldName arguments [] normalizedSubselections
              :: normalizedRest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (Selection.field responseName fieldName arguments directives
                  sourceSubselections
                :: sourceRest) := by
  intro normalizedField sourceField hnormalizedCollect hsourceCollect
    hcomplete htail
  have hhead :
      Execution.executeField schema resolvers variableValues depth source
          responseName (normalizedField :: normalizedFields)
        =
      Execution.executeField schema resolvers variableValues depth source
        responseName (sourceField :: sourceFields) := by
    apply executeField_cons_eq_cons_of_completeValue
      schema resolvers variableValues depth source responseName sourceField
      normalizedField sourceFields normalizedFields
    · rfl
    · rfl
    · rfl
    · simpa [normalizedField, sourceField] using hcomplete
  simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    hnormalizedCollect, hsourceCollect]
    using
      GroundTypeNormalization.executeCollectedFields_cons_eq_of_parts
        schema resolvers variableValues depth source
        (responseName, normalizedField :: normalizedFields)
        (responseName, sourceField :: sourceFields)
        normalizedTail sourceTail hhead htail

end CompleteNormalization

end NormalForm

end GraphQL
