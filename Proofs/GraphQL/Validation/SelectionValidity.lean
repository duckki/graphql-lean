import GraphQL.Theories.NormalForm

/-!
Projection and structural facts for selection validity.

The possible-types validity predicates are defined in `GraphQL.NormalForm`,
because they are normalizer validity assumptions rather than spec validation
rules. The aliases below keep existing validation-facing proof scripts readable
without moving those predicates back into `GraphQL.Validation`.
-/

namespace GraphQL

namespace Validation

abbrev selectionValidInPossibleTypes :=
  NormalForm.selectionValidInPossibleTypes

abbrev selectionSetValidInPossibleTypes :=
  NormalForm.selectionSetValidInPossibleTypes

@[simp]
theorem selectionValidInPossibleTypes_field
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    : selectionValidInPossibleTypes schema variableDefinitions parentType
        (.field responseName fieldName arguments directives selectionSet)
      = (selectionValid schema variableDefinitions parentType
            (.field responseName fieldName arguments directives selectionSet)
          ∧ match schema.lookupField parentType fieldName with
            | none => False
            | some fieldDefinition =>
                ∀ objectType,
                  objectType
                    ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
                  -> selectionSetValidInPossibleTypes schema
                      variableDefinitions objectType selectionSet) := by
  rfl

@[simp]
theorem selectionValidInPossibleTypes_inlineFragment_none
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    : selectionValidInPossibleTypes schema variableDefinitions parentType
        (.inlineFragment none directives selectionSet)
      = (∀ objectType,
          objectType ∈ schema.getPossibleTypes parentType
          -> selectionSetValidInPossibleTypes schema variableDefinitions
              objectType selectionSet) := by
  rfl

@[simp]
theorem selectionValidInPossibleTypes_inlineFragment_some
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType typeCondition : Name)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    : selectionValidInPossibleTypes schema variableDefinitions parentType
        (.inlineFragment (some typeCondition) directives selectionSet)
      = (schema.typesOverlapBool parentType typeCondition = true
          -> ∀ objectType,
              objectType ∈ schema.getPossibleTypes typeCondition
              -> selectionSetValidInPossibleTypes schema variableDefinitions
                  objectType selectionSet) := by
  rfl

@[simp]
theorem selectionSetValidInPossibleTypes_nil
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    : selectionSetValidInPossibleTypes schema variableDefinitions parentType []
      = True := by
  rfl

@[simp]
theorem selectionSetValidInPossibleTypes_cons
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selection : Selection)
    (selectionSet : List Selection)
    : selectionSetValidInPossibleTypes schema variableDefinitions
        parentType (selection :: selectionSet)
      = (selectionValidInPossibleTypes schema variableDefinitions parentType selection
          ∧ selectionSetValidInPossibleTypes schema variableDefinitions
              parentType selectionSet) := by
  rfl

theorem selectionValid_field_directivesValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    : selectionValid schema variableDefinitions parentType
        (.field responseName fieldName arguments directives selectionSet)
      -> directivesValid schema variableDefinitions directives := by
  intro hvalid
  simp [selectionValid] at hvalid
  exact hvalid.1

theorem selectionValid_field_lookup
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    : selectionValid schema variableDefinitions parentType
        (.field responseName fieldName arguments directives selectionSet)
      -> ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          ∧ argumentsValid schema fieldDefinition.arguments variableDefinitions arguments
          ∧ fieldSelectionSetValid schema variableDefinitions
              fieldDefinition selectionSet := by
  intro hvalid
  simp [selectionValid] at hvalid
  exact hvalid.2

theorem selectionValid_inlineFragment_none_selectionSetValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    : selectionValid schema variableDefinitions parentType
        (.inlineFragment none directives selectionSet)
      -> selectionSetValid schema variableDefinitions parentType selectionSet := by
  intro hvalid
  simp [selectionValid] at hvalid
  exact hvalid.2.2

theorem selectionValid_inlineFragment_some_selectionSetValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    : selectionValid schema variableDefinitions parentType
        (.inlineFragment (some typeCondition) directives selectionSet)
      -> selectionSetValid schema variableDefinitions typeCondition selectionSet := by
  intro hvalid
  simp [selectionValid] at hvalid
  exact hvalid.2.2.2.2

theorem fieldSelectionSetValid_outputType
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fieldDefinition : FieldDefinition} {selectionSet : List Selection}
    : fieldSelectionSetValid schema variableDefinitions fieldDefinition selectionSet
      -> fieldDefinition.outputType.isOutputType schema := by
  intro hvalid
  simp [fieldSelectionSetValid] at hvalid
  exact hvalid.1

theorem fieldSelectionSetValid_composite_child
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fieldDefinition : FieldDefinition} {selectionSet : List Selection}
    : fieldSelectionSetValid schema variableDefinitions fieldDefinition selectionSet
      -> schema.isCompositeType fieldDefinition.outputType.namedType
      -> selectionSet ≠ []
      -> selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType selectionSet := by
  intro hvalid hcomposite _hnonempty
  simp [fieldSelectionSetValid] at hvalid
  cases hvalid.2 with
  | inl hleaf =>
      exact False.elim
        (by
          rcases hleaf.1 with ⟨typeDefinition, hlookup, hleafDefinition⟩
          rcases hcomposite with
            ⟨compositeDefinition, hcompositeLookup, hcompositeDefinition⟩
          rw [hlookup] at hcompositeLookup
          cases hcompositeLookup
          cases typeDefinition <;>
            simp [TypeDefinition.isLeafType, TypeDefinition.isCompositeType]
              at hleafDefinition hcompositeDefinition)
  | inr hchild =>
      exact hchild.2.2

theorem selectionSetValid_append
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : selectionSetValid schema variableDefinitions parentType left
      -> selectionSetValid schema variableDefinitions parentType right
      -> selectionSetValid schema variableDefinitions parentType (left ++ right) := by
  intro hleft hright
  simp [selectionSetValid] at hleft
  simp [selectionSetValid] at hright
  simp [selectionSetValid]
  intro selection hselection
  cases hselection with
  | inl hmem =>
      exact hleft selection hmem
  | inr hmem =>
      exact hright selection hmem

theorem selectionSetValid_append_left
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : selectionSetValid schema variableDefinitions parentType (left ++ right)
      -> selectionSetValid schema variableDefinitions parentType left := by
  intro hvalid
  simp [selectionSetValid] at hvalid
  simp [selectionSetValid]
  intro selection hselection
  exact hvalid selection (Or.inl hselection)

theorem selectionSetValid_append_right
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : selectionSetValid schema variableDefinitions parentType (left ++ right)
      -> selectionSetValid schema variableDefinitions parentType right := by
  intro hvalid
  simp [selectionSetValid] at hvalid
  simp [selectionSetValid]
  intro selection hselection
  exact hvalid selection (Or.inr hselection)

theorem selectionSetValid_tail
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection}
    {selectionSet : List Selection}
    : selectionSetValid schema variableDefinitions parentType (selection :: selectionSet)
      -> selectionSetValid schema variableDefinitions parentType selectionSet := by
  intro hvalid
  simp [selectionSetValid] at hvalid ⊢
  intro candidate hcandidate
  exact hvalid.2 candidate hcandidate

theorem selectionSetValid_field_head_lookup
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet rest : List Selection}
    : selectionSetValid schema variableDefinitions parentType
        (.field responseName fieldName arguments directives selectionSet :: rest)
      -> ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          ∧ argumentsValid schema fieldDefinition.arguments variableDefinitions arguments
          ∧ fieldSelectionSetValid schema variableDefinitions
              fieldDefinition selectionSet := by
  intro hvalid
  have hfieldValid :
      selectionValid schema variableDefinitions parentType
        (.field responseName fieldName arguments directives selectionSet) := by
    simp [selectionSetValid] at hvalid
    exact hvalid.1
  exact selectionValid_field_lookup hfieldValid

theorem selectionSetValid_field_head_lookup_none_false
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet rest : List Selection}
    : selectionSetValid schema variableDefinitions parentType
        (.field responseName fieldName arguments directives selectionSet :: rest)
      -> schema.lookupField parentType fieldName = none
      -> False := by
  intro hvalid hnone
  rcases selectionSetValid_field_head_lookup hvalid with
    ⟨fieldDefinition, hlookup, _hargs, _hselectionSet⟩
  rw [hnone] at hlookup
  contradiction

theorem operationDefinitionValid_rootType_eq {schema : Schema} {operation : Operation}
    : operationDefinitionValid schema operation
      -> operation.rootType = schema.queryType := by
  intro hvalid
  exact hvalid.1

theorem operationDefinitionValid_rootTypeComposite
    {schema : Schema} {operation : Operation}
    : operationDefinitionValid schema operation
      -> schema.isCompositeType operation.rootType := by
  intro hvalid
  exact hvalid.2.1

theorem operationDefinitionValid_variableDefinitionsValid
    {schema : Schema} {operation : Operation}
    : operationDefinitionValid schema operation
      -> variableDefinitionsValid schema operation.variableDefinitions := by
  intro hvalid
  exact hvalid.2.2.1

theorem operationDefinitionValid_selectionSetValid
    {schema : Schema} {operation : Operation}
    : operationDefinitionValid schema operation
      -> selectionSetValid schema operation.variableDefinitions operation.rootType
          operation.selectionSet := by
  intro hvalid
  exact hvalid.2.2.2.2.1

theorem operationDefinitionValid_selectionSet_nonempty
    {schema : Schema} {operation : Operation}
    : operationDefinitionValid schema operation -> operation.selectionSet ≠ [] := by
  intro hvalid
  exact hvalid.2.2.2.1

theorem operationDefinitionValid_fieldsInSetCanMerge
    {schema : Schema} {operation : Operation}
    : operationDefinitionValid schema operation
      -> FieldMerge.fieldsInSetCanMerge schema operation.rootType
          operation.selectionSet := by
  intro hvalid
  exact hvalid.2.2.2.2.2.1

theorem operationDefinitionValid_operationVariablesUsed
    {schema : Schema} {operation : Operation}
    : operationDefinitionValid schema operation -> operationVariablesUsed operation := by
  intro hvalid
  exact hvalid.2.2.2.2.2.2

end Validation

end GraphQL
