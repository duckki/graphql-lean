import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.Validation

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

theorem operationDefinitionValid_rootType_eq {schema : Schema} {operation : Operation}
    : operationDefinitionValid schema operation
      -> (operation.rootType schema) = schema.queryType := by
  intro hvalid
  simp [Operation.rootType, OperationType.rootType]

theorem operationDefinitionValid_selectionSetValid
    {schema : Schema} {operation : Operation}
    : operationDefinitionValid schema operation
      -> selectionSetValid schema operation.variableDefinitions
          (operation.rootType schema) operation.selectionSet := by
  intro hvalid
  exact hvalid.2.2.2.2.1

theorem operationDefinitionValid_fieldsInSetCanMerge
    {schema : Schema} {operation : Operation}
    : operationDefinitionValid schema operation
      -> FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
          operation.selectionSet := by
  intro hvalid
  exact hvalid.2.2.2.2.2.1

end GraphQL.Validation
