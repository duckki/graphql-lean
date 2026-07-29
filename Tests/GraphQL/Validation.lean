import Tests.GraphQL.Common
import GraphQL.Validation
import Proofs.GraphQL.Validation.SelectionValidity

namespace GraphQL
namespace Tests
namespace Validation

def episodeVariableDefinition : VariableDefinition :=
  { name := "episode", typeRef := .named "Episode" }

def unusedVariableQuery : Operation :=
  {
    name := some "UnusedVariable"
    rootType := "Query"
    variableDefinitions := [episodeVariableDefinition]
    selectionSet :=
      [.field "hero" "hero" [] [] [.field "name" "name" [] [] []]]
  }

theorem unusedQueryVariableRejected
    : ¬ GraphQL.Validation.operationDefinitionValid sampleSchema unusedVariableQuery := by
  intro hvalid
  have hused :=
    GraphQL.Validation.operationDefinitionValid_operationVariablesUsed hvalid
  have husedEpisode :=
    hused episodeVariableDefinition (by
      simp [unusedVariableQuery, episodeVariableDefinition])
  simp [unusedVariableQuery,
    GraphQL.Validation.selectionSetVariables,
    GraphQL.Validation.selectionVariables,
    GraphQL.Validation.argumentsVariables,
    GraphQL.Validation.directivesVariables] at husedEpisode

def usedVariableLocationsQuery : Operation :=
  {
    name := some "UsedVariableLocations"
    rootType := "Query"
    variableDefinitions :=
      [
        episodeVariableDefinition,
        { name := "included", typeRef := .nonNull (.named "Boolean") },
        { name := "nested", typeRef := .named "Episode" }
      ]
    selectionSet :=
      [.field "hero" "hero"
        [{ name := "episode", value := .variable "episode" }]
        [.include (.variable "included")]
        [.inlineFragment none []
          [.field "name" "name"
            [{
              name := "syntacticNestedInput"
              value := .object [("episodes", .list [.variable "nested"])]
            }]
            [] []]]]
  }

theorem fieldDirectiveAndNestedInputVariablesCountAsUsed
    : GraphQL.Validation.operationVariablesUsed usedVariableLocationsQuery := by
  simp [GraphQL.Validation.operationVariablesUsed, usedVariableLocationsQuery,
    episodeVariableDefinition,
    GraphQL.Validation.selectionSetVariables,
    GraphQL.Validation.selectionVariables,
    GraphQL.Validation.argumentsVariables,
    GraphQL.Validation.argumentVariables,
    GraphQL.Validation.directiveVariables,
    GraphQL.Validation.directivesVariables,
    GraphQL.Validation.inputValueVariables,
    GraphQL.Validation.inputValuesVariables,
    GraphQL.Validation.inputObjectFieldsVariables]

def duplicateEpisodeArguments : List Argument :=
  [
    { name := "episode", value := .enum "NEWHOPE" },
    { name := "episode", value := .enum "NEWHOPE" }
  ]

theorem duplicateArgumentNamesRejected
    : ¬ GraphQL.Validation.argumentsValid sampleSchema
          [testEpisodeArgumentDefinition] [] duplicateEpisodeArguments := by
  simp [GraphQL.Validation.argumentsValid, duplicateEpisodeArguments]

theorem duplicateArgumentOperationSelectionSetRejected
    : ¬ GraphQL.Validation.selectionSetValid sampleSchema []
          sampleDuplicateArgumentQuery.rootType
          sampleDuplicateArgumentQuery.selectionSet := by
  simp [GraphQL.Validation.selectionSetValid,
    GraphQL.Validation.selectionValid,
    GraphQL.Validation.fieldSelectionSetValid,
    GraphQL.Validation.argumentsValid,
    GraphQL.Validation.argumentValid,
    sampleDuplicateArgumentQuery, sampleSchema,
    testObjectFieldDefinition, testEpisodeArgumentDefinition,
    testStringFieldDefinition]

def interfaceDefaultedLimitArgument : InputValueDefinition :=
  {
    name := "limit"
    inputType := .nonNull (.named "Int")
    defaultValue := some (.int 10)
  }

def objectRequiredLimitArgument : InputValueDefinition :=
  { name := "limit", inputType := .nonNull (.named "Int") }

def interfaceImplementationArgumentSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [testObjectFieldDefinition "node" "Node"]
            interfaces := []
          },
        .interface
          {
            name := "Node"
            fields :=
              [{
                name := "value"
                outputType := .named "String"
                arguments := [interfaceDefaultedLimitArgument]
              }]
            interfaces := []
          },
        .object
          {
            name := "Human"
            fields :=
              [{
                name := "value"
                outputType := .named "String"
                arguments := [objectRequiredLimitArgument]
              }]
            interfaces := ["Node"]
          }
      ]
  }

def missingImplementationArgumentQuery : Operation :=
  {
    name := some "MissingImplementationArgument"
    rootType := "Query"
    selectionSet :=
      [.field "node" "node" [] [] [.field "value" "value" [] [] []]]
  }

theorem interfaceImplementationArgumentsRejectedByPossibleTypesAssumption
    : ¬ GraphQL.NormalForm.operationFieldsValidInPossibleTypes
          interfaceImplementationArgumentSchema
          missingImplementationArgumentQuery := by
  intro hfields
  have hrootScope :
      GraphQL.Validation.selectionSetValidInPossibleTypes
        interfaceImplementationArgumentSchema [] "Query"
        [ .field "node" "node" [] [] [
            .field "value" "value" [] [] []
          ] ] := by
    simpa [GraphQL.NormalForm.operationFieldsValidInPossibleTypes,
      missingImplementationArgumentQuery] using hfields
  have hnodeImpl :
      GraphQL.Validation.selectionValidInPossibleTypes
        interfaceImplementationArgumentSchema [] "Query"
        (.field "node" "node" [] [] [
          .field "value" "value" [] [] []
        ]) := by
    simpa [GraphQL.Validation.selectionSetValidInPossibleTypes]
      using hrootScope.1
  have hnodeBranches :
      ∀ objectType,
        objectType ∈ interfaceImplementationArgumentSchema.getPossibleTypes "Node" ->
          GraphQL.Validation.selectionSetValidInPossibleTypes
            interfaceImplementationArgumentSchema [] objectType
            [ .field "value" "value" [] [] [] ] := by
    have hnodeLookup :
        interfaceImplementationArgumentSchema.lookupField "Query" "node" =
          some (testObjectFieldDefinition "node" "Node") := by
      rfl
    have hbranches := hnodeImpl.2
    rw [hnodeLookup] at hbranches
    simpa [testObjectFieldDefinition, TypeRef.namedType] using hbranches
  have hhumanMem :
      "Human" ∈ interfaceImplementationArgumentSchema.getPossibleTypes "Node" := by
    native_decide
  have hhumanValueScope :
      GraphQL.Validation.selectionSetValidInPossibleTypes
        interfaceImplementationArgumentSchema [] "Human"
        [ .field "value" "value" [] [] [] ] :=
    hnodeBranches "Human" hhumanMem
  have hhumanValueImpl :
      GraphQL.Validation.selectionValidInPossibleTypes
        interfaceImplementationArgumentSchema [] "Human"
        (.field "value" "value" [] [] []) := by
    simpa [GraphQL.Validation.selectionSetValidInPossibleTypes]
      using hhumanValueScope.1
  have hhumanValueValid :
      GraphQL.Validation.selectionValid
        interfaceImplementationArgumentSchema [] "Human"
        (.field "value" "value" [] [] []) := by
    simpa [GraphQL.Validation.selectionValidInPossibleTypes,
      interfaceImplementationArgumentSchema] using hhumanValueImpl.1
  have hhumanValueData :
      GraphQL.Validation.directivesValid
        interfaceImplementationArgumentSchema [] []
        ∧ ∃ fieldDefinition,
          interfaceImplementationArgumentSchema.lookupField "Human" "value" =
            some fieldDefinition
            ∧ GraphQL.Validation.argumentsValid
              interfaceImplementationArgumentSchema fieldDefinition.arguments [] []
            ∧ GraphQL.Validation.fieldSelectionSetValid
              interfaceImplementationArgumentSchema [] fieldDefinition [] := by
    simpa [GraphQL.Validation.selectionValid] using hhumanValueValid
  rcases hhumanValueData with ⟨_, fieldDefinition, hlookup,
    harguments, _⟩
  have hfield :
      fieldDefinition =
        { name := "value"
          outputType := .named "String"
          arguments := [objectRequiredLimitArgument] } := by
    have hlookupExpected :
        interfaceImplementationArgumentSchema.lookupField "Human" "value" =
          some
            { name := "value"
              outputType := .named "String"
              arguments := [objectRequiredLimitArgument] } := by
      rfl
    rw [hlookupExpected] at hlookup
    simpa using hlookup.symm
  subst fieldDefinition
  have hrequired :
      GraphQL.Validation.isRequiredArgument objectRequiredLimitArgument := by
    simp [GraphQL.Validation.isRequiredArgument,
      GraphQL.Validation.isRequiredInputValueDefinition,
      InputValueDefinition.isRequired,
      objectRequiredLimitArgument]
  have hmissing :=
    harguments.2.2 objectRequiredLimitArgument (by simp)
      hrequired
  rcases hmissing with ⟨argument, hget, _⟩
  simp [GraphQL.Validation.getArgument?] at hget

end Validation
end Tests
end GraphQL
