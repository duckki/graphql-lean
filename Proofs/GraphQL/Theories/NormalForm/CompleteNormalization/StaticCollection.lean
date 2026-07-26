import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.TypeBranches
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.BoolCaseWrappers
import Proofs.GraphQL.Theories.NormalForm.Shared.DirectiveFree

/-!
Static collection facts for complete normalization.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem staticCollectForGround_nil
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name)
    (boolCase : BoolCase)
    : staticCollectForGround schema variables lookupParent groundType boolCase []
      = [] := by
  simp [staticCollectForGround]

theorem staticCollectForGround_field_allowed
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType responseName fieldName : Name)
    (boolCase : BoolCase) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : directivesAllowIn boolCase directives = true
      -> staticCollectForGround schema variables lookupParent groundType
            boolCase
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (let collectedRest :=
                staticCollectForGround schema variables lookupParent groundType
                  boolCase rest
              match schema.lookupField lookupParent fieldName with
              | none =>
                  let normalizedSelectionSet :=
                    normalizeSelectionSetIn schema variables boolCase
                      lookupParent selectionSet
                  Selection.field responseName fieldName arguments []
                    normalizedSelectionSet
                  :: collectedRest
              | some fieldDefinition =>
                  let returnType := fieldDefinition.outputType.namedType
                  let normalizedSelectionSet :=
                    normalizeBoolCaseForType schema boolCase returnType selectionSet
                  Selection.field responseName fieldName arguments []
                    normalizedSelectionSet
                  :: collectedRest) := by
  intro hallow
  cases hlookup : schema.lookupField lookupParent fieldName with
  | none =>
      simp [staticCollectForGround, normalizeSelectionSetIn, hallow, hlookup]
  | some fieldDefinition =>
      simp [staticCollectForGround, hallow, hlookup]

theorem staticCollectForGround_field_skipped
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType responseName fieldName : Name)
    (boolCase : BoolCase) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : directivesAllowIn boolCase directives = false
      -> staticCollectForGround schema variables lookupParent groundType
            boolCase
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = staticCollectForGround schema variables lookupParent groundType
              boolCase rest := by
  intro hallow
  simp [staticCollectForGround, hallow]

theorem staticCollectForGround_inline_none_allowed
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : directivesAllowIn boolCase directives = true
      -> staticCollectForGround schema variables lookupParent groundType
            boolCase
            (Selection.inlineFragment none directives selectionSet :: rest)
          = staticCollectForGround schema variables lookupParent groundType
              boolCase selectionSet
            ++ staticCollectForGround schema variables lookupParent
                groundType boolCase rest := by
  intro hallow
  simp [staticCollectForGround, hallow]

theorem staticCollectForGround_inline_none_skipped
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : directivesAllowIn boolCase directives = false
      -> staticCollectForGround schema variables lookupParent groundType
            boolCase
            (Selection.inlineFragment none directives selectionSet :: rest)
          = staticCollectForGround schema variables lookupParent groundType
              boolCase rest := by
  intro hallow
  simp [staticCollectForGround, hallow]

theorem staticCollectForGround_inline_some_allowed
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType typeCondition : Name)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : directivesAllowIn boolCase directives = true
      -> schema.typeIncludesObjectBool typeCondition groundType = true
      -> staticCollectForGround schema variables lookupParent groundType
            boolCase
            (Selection.inlineFragment (some typeCondition) directives selectionSet
              :: rest)
          = staticCollectForGround schema variables typeCondition groundType
              boolCase selectionSet
            ++ staticCollectForGround schema variables lookupParent
                groundType boolCase rest := by
  intro hallow hincludes
  simp [staticCollectForGround, hallow, hincludes]

theorem staticCollectForGround_inline_some_skipped
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType typeCondition : Name)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (directivesAllowIn boolCase directives
          && schema.typeIncludesObjectBool typeCondition groundType)
        = false
      -> staticCollectForGround schema variables lookupParent groundType
            boolCase
            (Selection.inlineFragment (some typeCondition) directives selectionSet
              :: rest)
          = staticCollectForGround schema variables lookupParent groundType
              boolCase rest := by
  intro hskip
  simp [staticCollectForGround, hskip]

theorem staticCollectForGround_field_shape
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name)
    (boolCase : BoolCase)
    : ∀ {sourceSelectionSet selection},
        selection
          ∈ staticCollectForGround schema variables lookupParent
              groundType boolCase sourceSelectionSet
        -> ∃ responseName fieldName arguments selectionSet,
            selection = Selection.field responseName fieldName arguments [] selectionSet
  | [], selection, hmem => by
      simp [staticCollectForGround] at hmem
  | sourceSelection :: rest, selection, hmem => by
      cases sourceSelection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hallow : directivesAllowIn boolCase directives with
          | false =>
              simp [staticCollectForGround, hallow] at hmem
              exact staticCollectForGround_field_shape schema
                variables lookupParent groundType boolCase hmem
          | true =>
              cases hlookup : schema.lookupField lookupParent fieldName with
              | none =>
                  simp [staticCollectForGround, hallow, hlookup] at hmem
                  rcases hmem with hhead | htail
                  · subst selection
                    exact ⟨responseName, fieldName, arguments,
                      normalizeSelectionSetIn schema variables boolCase
                        lookupParent selectionSet, rfl⟩
                  · exact staticCollectForGround_field_shape schema
                      variables lookupParent groundType boolCase htail
              | some fieldDefinition =>
                  simp [staticCollectForGround, hallow, hlookup] at hmem
                  rcases hmem with hhead | htail
                  · subst selection
                    exact ⟨responseName, fieldName, arguments,
                      normalizeBoolCaseForType schema boolCase
                        fieldDefinition.outputType.namedType selectionSet,
                      rfl⟩
                  · exact staticCollectForGround_field_shape schema
                      variables lookupParent groundType boolCase htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow : directivesAllowIn boolCase directives
              · simp [staticCollectForGround, hallow] at hmem
                exact staticCollectForGround_field_shape schema
                  variables lookupParent groundType boolCase hmem
              · simp [staticCollectForGround, hallow] at hmem
                rcases hmem with hselection | hrest
                · exact staticCollectForGround_field_shape schema
                    variables lookupParent groundType boolCase hselection
                · exact staticCollectForGround_field_shape schema
                    variables lookupParent groundType boolCase hrest
          | some typeCondition =>
              cases hbranch : directivesAllowIn boolCase directives && schema.typeIncludesObjectBool typeCondition groundType
              · simp [staticCollectForGround, hbranch] at hmem
                exact staticCollectForGround_field_shape schema
                  variables lookupParent groundType boolCase hmem
              · simp [staticCollectForGround, hbranch] at hmem
                rcases hmem with hselection | hrest
                · exact staticCollectForGround_field_shape schema
                    variables typeCondition groundType boolCase hselection
                · exact staticCollectForGround_field_shape schema
                    variables lookupParent groundType boolCase hrest

theorem staticCollectForGround_allFields
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name)
    (boolCase : BoolCase)
    (sourceSelectionSet : List Selection)
    : selectionsAllFields
        (staticCollectForGround schema variables lookupParent groundType
          boolCase sourceSelectionSet) := by
  intro selection hmem
  rcases
      staticCollectForGround_field_shape schema variables
        lookupParent groundType boolCase hmem with
    ⟨responseName, fieldName, arguments, selectionSet, hselection⟩
  subst selection
  simp [Selection.isField]

theorem staticCollectForGround_append
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name)
    (boolCase : BoolCase)
    : ∀ left right,
        staticCollectForGround schema variables lookupParent
          groundType boolCase (left ++ right)
        = staticCollectForGround schema variables lookupParent groundType boolCase left
          ++ staticCollectForGround schema variables lookupParent
              groundType boolCase right
  | [], right => by
      simp [staticCollectForGround]
  | selection :: rest, right => by
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hallow : directivesAllowIn boolCase directives
          · simp [staticCollectForGround, hallow,
              staticCollectForGround_append schema variables
                lookupParent groundType boolCase rest right]
          · cases hlookup : schema.lookupField lookupParent fieldName with
            | none =>
                simp [staticCollectForGround, hallow, hlookup,
                  staticCollectForGround_append schema variables
                    lookupParent groundType boolCase rest right]
                repeat split <;> simp
            | some fieldDefinition =>
                cases hnormalized : normalizeBoolCaseForType schema boolCase
                      fieldDefinition.outputType.namedType selectionSet <;>
                    simp [staticCollectForGround, hallow, hlookup,
                      hnormalized,
                      staticCollectForGround_append schema variables
                        lookupParent groundType boolCase rest right]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow : directivesAllowIn boolCase directives
              · simp [staticCollectForGround, hallow,
                  staticCollectForGround_append schema variables
                    lookupParent groundType boolCase rest right]
              · simp [staticCollectForGround, hallow,
                  staticCollectForGround_append schema variables
                    lookupParent groundType boolCase rest right,
                  List.append_assoc]
          | some typeCondition =>
              cases hbranch : directivesAllowIn boolCase directives && schema.typeIncludesObjectBool typeCondition groundType
              · simp [staticCollectForGround, hbranch,
                  staticCollectForGround_append schema variables
                    lookupParent groundType boolCase rest right]
              · simp [staticCollectForGround, hbranch,
                  staticCollectForGround_append schema variables
                    lookupParent groundType boolCase rest right,
                  List.append_assoc]

theorem withoutFieldSelectionsWithResponseName_append
    (schema : Schema) (responseName : Name)
    : ∀ left right,
        withoutFieldSelectionsWithResponseName schema responseName (left ++ right)
        = withoutFieldSelectionsWithResponseName schema responseName left
          ++ withoutFieldSelectionsWithResponseName schema responseName right
  | [], right => by
      simp [withoutFieldSelectionsWithResponseName]
  | selection :: rest, right => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hresponse : fieldResponseName == responseName <;>
            simp [withoutFieldSelectionsWithResponseName, hresponse,
              withoutFieldSelectionsWithResponseName_append schema responseName rest
                right]
      | inlineFragment typeCondition directives selectionSet =>
          simp [withoutFieldSelectionsWithResponseName,
            withoutFieldSelectionsWithResponseName_append schema responseName rest
              right]

theorem staticCollectForGround_withoutFieldSelectionsWithResponseName
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name)
    (boolCase : BoolCase) (responseName : Name)
    : ∀ selectionSet,
        staticCollectForGround schema variables lookupParent
          groundType boolCase
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
        = withoutFieldSelectionsWithResponseName schema responseName
            (staticCollectForGround schema variables lookupParent
              groundType boolCase selectionSet)
  | [] => by
      simp [staticCollectForGround, withoutFieldSelectionsWithResponseName]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hresponse : fieldResponseName == responseName
          · cases hallow : directivesAllowIn boolCase directives
            · simp [staticCollectForGround,
                withoutFieldSelectionsWithResponseName, hresponse, hallow,
                staticCollectForGround_withoutFieldSelectionsWithResponseName
                  schema variables lookupParent groundType boolCase
                  responseName rest]
            · cases hlookup : schema.lookupField lookupParent fieldName with
              | none =>
                  simp [staticCollectForGround,
                    withoutFieldSelectionsWithResponseName, hresponse, hallow,
                    hlookup,
                    staticCollectForGround_withoutFieldSelectionsWithResponseName
                      schema variables lookupParent groundType boolCase
                      responseName rest]
                  repeat split <;>
                    simp [withoutFieldSelectionsWithResponseName, hresponse]
              | some fieldDefinition =>
                  cases hnormalized : normalizeBoolCaseForType schema boolCase
                        fieldDefinition.outputType.namedType selectionSet <;>
                      simp [staticCollectForGround,
                        withoutFieldSelectionsWithResponseName, hresponse, hallow,
                        hlookup, hnormalized,
                        staticCollectForGround_withoutFieldSelectionsWithResponseName
                          schema variables lookupParent groundType boolCase
                          responseName rest]
          · cases hallow : directivesAllowIn boolCase directives
            · simp [staticCollectForGround,
                withoutFieldSelectionsWithResponseName, hresponse, hallow,
                staticCollectForGround_withoutFieldSelectionsWithResponseName
                  schema variables lookupParent groundType boolCase
                  responseName rest]
            · cases hlookup : schema.lookupField lookupParent fieldName with
              | none =>
                  simp [staticCollectForGround,
                    withoutFieldSelectionsWithResponseName, hresponse, hallow,
                    hlookup,
                    staticCollectForGround_withoutFieldSelectionsWithResponseName
                      schema variables lookupParent groundType boolCase
                      responseName rest]
                  repeat split <;>
                    simp [withoutFieldSelectionsWithResponseName, hresponse]
              | some fieldDefinition =>
                  cases hnormalized : normalizeBoolCaseForType schema boolCase
                        fieldDefinition.outputType.namedType selectionSet <;>
                      simp [staticCollectForGround,
                        withoutFieldSelectionsWithResponseName, hresponse, hallow,
                        hlookup, hnormalized,
                        staticCollectForGround_withoutFieldSelectionsWithResponseName
                          schema variables lookupParent groundType boolCase
                          responseName rest]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow : directivesAllowIn boolCase directives
              · simp [staticCollectForGround,
                  withoutFieldSelectionsWithResponseName, hallow,
                  staticCollectForGround_withoutFieldSelectionsWithResponseName
                    schema variables lookupParent groundType boolCase
                    responseName rest]
              · simp [staticCollectForGround,
                  withoutFieldSelectionsWithResponseName, hallow,
                  staticCollectForGround_withoutFieldSelectionsWithResponseName
                    schema variables lookupParent groundType boolCase
                    responseName selectionSet,
                  staticCollectForGround_withoutFieldSelectionsWithResponseName
                    schema variables lookupParent groundType boolCase
                    responseName rest,
                  withoutFieldSelectionsWithResponseName_append]
          | some typeCondition =>
              cases hbranch : directivesAllowIn boolCase directives && schema.typeIncludesObjectBool typeCondition groundType
              · simp [staticCollectForGround,
                  withoutFieldSelectionsWithResponseName, hbranch,
                  staticCollectForGround_withoutFieldSelectionsWithResponseName
                    schema variables lookupParent groundType boolCase
                    responseName rest]
              · simp [staticCollectForGround,
                  withoutFieldSelectionsWithResponseName, hbranch,
                  staticCollectForGround_withoutFieldSelectionsWithResponseName
                    schema variables typeCondition groundType boolCase
                    responseName selectionSet,
                  staticCollectForGround_withoutFieldSelectionsWithResponseName
                    schema variables lookupParent groundType boolCase
                    responseName rest,
                  withoutFieldSelectionsWithResponseName_append]

theorem normalizeSelectionSetIn_append
    (schema : Schema) (variables : List BoolVar)
    (boolCase : BoolCase) (parentType : Name)
    : ∀ left right,
        normalizeSelectionSetIn schema variables boolCase parentType (left ++ right)
        = normalizeSelectionSetIn schema variables boolCase parentType left
          ++ normalizeSelectionSetIn schema variables boolCase parentType right
  | [], right => by
      simpa [normalizeSelectionSetIn] using
        staticCollectForGround_append schema variables parentType parentType
          boolCase [] right
  | selection :: rest, right => by
      simpa [normalizeSelectionSetIn] using
        staticCollectForGround_append schema variables parentType parentType
          boolCase (selection :: rest) right

theorem boolCaseBranchesForGround_noVariables
    (schema : Schema) (groundType : Name)
    (selectionSet : List Selection)
    : boolCaseBranchesForGround schema groundType [] selectionSet
      = staticCollectForGround schema [] groundType groundType [] selectionSet := by
  unfold boolCaseBranchesForGround
  simp [allBoolCases, wrapWithBoolCase]

end CompleteNormalization

end NormalForm

end GraphQL
