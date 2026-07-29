import Tests.GraphQL.Theories.NormalForm.GroundTypeNormalization
import Proofs.GraphQL.Execution.Data
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness

namespace GraphQL
namespace Tests
namespace NormalForm

open GraphQL.NormalForm
open GraphQL.NormalForm.GroundTypeNormalization

def completeNormalizationDirectiveInputQuery : Operation :=
  operationWith
    [.field "hero" "hero" [] []
      [
        .field "id" "id" [] [] [],
        .field "name" "name" [] [.include (.variable "x")] [],
        .inlineFragment none [.skip (.variable "y")]
          [.field "homePlanet" "homePlanet" [] [] []]
      ]]

def completeNormalizationDirectiveOutputSnapshot : Operation :=
  operationWith
    (completeNormalizationRootBoolCaseBranchesFor ["x", "y"]
      (fun
        | [("x", false), ("y", false)] =>
            [.field "hero" "hero" [] []
              [.field "id" "id" [] [] [], .field "homePlanet" "homePlanet" [] [] []]]
        | [("x", false), ("y", true)] =>
            [.field "hero" "hero" [] [] [.field "id" "id" [] [] []]]
        | [("x", true), ("y", false)] =>
            [.field "hero" "hero" [] []
              [
                .field "id" "id" [] [] [],
                .field "name" "name" [] [] [],
                .field "homePlanet" "homePlanet" [] [] []
              ]]
        | [("x", true), ("y", true)] =>
            [.field "hero" "hero" [] []
              [.field "id" "id" [] [] [], .field "name" "name" [] [] []]]
        | _ => []))

theorem completeNormalizationDirectiveSmoke
    : operationWellFormedBool completeNormalizationDirectiveOutputSnapshot = true
      ∧ operationEqBool
          (completeNormalizeOperation groundTypingSchema
            completeNormalizationDirectiveInputQuery)
          completeNormalizationDirectiveOutputSnapshot
        = true := by
  native_decide

def completeNormalizationGlobalVariablesInputQuery : Operation :=
  operationWith
    [
      .field "hero" "hero" [] []
        [
          .field "id" "id" [] [] [],
          .field "name" "name" [] [.include (.variable "y")] []
        ],
      .field "search" "search" [] [] [.field "id" "id" [] [.include (.variable "x")] []]
    ]

def completeNormalizationGlobalVariablesOutputSnapshot : Operation :=
  operationWith
    (completeNormalizationRootBoolCaseBranchesFor ["y", "x"]
      (fun
        | [("y", false), ("x", false)] =>
            [
              .field "hero" "hero" [] [] [.field "id" "id" [] [] []],
              .field "search" "search" [] [] []
            ]
        | [("y", false), ("x", true)] =>
            [
              .field "hero" "hero" [] [] [.field "id" "id" [] [] []],
              .field "search" "search" [] []
                [
                  .inlineFragment (some "Human") [] [.field "id" "id" [] [] []],
                  .inlineFragment (some "Droid") [] [.field "id" "id" [] [] []]
                ]
            ]
        | [("y", true), ("x", false)] =>
            [
              .field "hero" "hero" [] []
                [.field "id" "id" [] [] [], .field "name" "name" [] [] []],
              .field "search" "search" [] [] []
            ]
        | [("y", true), ("x", true)] =>
            [
              .field "hero" "hero" [] []
                [.field "id" "id" [] [] [], .field "name" "name" [] [] []],
              .field "search" "search" [] []
                [
                  .inlineFragment (some "Human") [] [.field "id" "id" [] [] []],
                  .inlineFragment (some "Droid") [] [.field "id" "id" [] [] []]
                ]
            ]
        | _ => []))

theorem completeNormalizationGlobalVariablesSmoke
    : operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationGlobalVariablesInputQuery)
        completeNormalizationGlobalVariablesOutputSnapshot
      = true := by
  native_decide

def completeNormalizationAbstractInputQuery : Operation :=
  operationWith
    [.field "search" "search" [] []
      [
        .field "id" "id" [] [] [],
        .inlineFragment (some "Human") [] [.field "homePlanet" "homePlanet" [] [] []],
        .inlineFragment (some "Droid") [.include (.variable "x")]
          [.field "primaryFunction" "primaryFunction" [] [] []]
      ]]

def completeNormalizationAbstractOutputSnapshot : Operation :=
  operationWith
    (completeNormalizationRootBoolCaseBranchesFor ["x"]
      (fun
        | [("x", false)] =>
            [.field "search" "search" [] []
              [
                .inlineFragment (some "Human") []
                  [.field "id" "id" [] [] [], .field "homePlanet" "homePlanet" [] [] []],
                .inlineFragment (some "Droid") [] [.field "id" "id" [] [] []]
              ]]
        | [("x", true)] =>
            [.field "search" "search" [] []
              [
                .inlineFragment (some "Human") []
                  [.field "id" "id" [] [] [], .field "homePlanet" "homePlanet" [] [] []],
                .inlineFragment (some "Droid") []
                  [
                    .field "id" "id" [] [] [],
                    .field "primaryFunction" "primaryFunction" [] [] []
                  ]
              ]]
        | _ => []))

theorem completeNormalizationAbstractSmoke
    : operationWellFormedBool completeNormalizationAbstractOutputSnapshot = true
      ∧ operationEqBool
          (completeNormalizeOperation groundTypingSchema
            completeNormalizationAbstractInputQuery)
          completeNormalizationAbstractOutputSnapshot
        = true := by
  native_decide

def completeNormalizationNestedDirectiveInputQuery : Operation :=
  operationWith
    [.field "hero" "hero" [] []
      [.field "companion" "companion" [] []
        [.field "id" "id" [] [.include (.variable "x")] []]]]

def completeNormalizationNestedDirectiveOutputSnapshot : Operation :=
  operationWith
    (completeNormalizationRootBoolCaseBranchesFor ["x"]
      (fun
        | [("x", false)] =>
            [.field "hero" "hero" [] [] [.field "companion" "companion" [] [] []]]
        | [("x", true)] =>
            [.field "hero" "hero" [] []
              [.field "companion" "companion" [] []
                [
                  .inlineFragment (some "Human") [] [.field "id" "id" [] [] []],
                  .inlineFragment (some "Droid") [] [.field "id" "id" [] [] []]
                ]]]
        | _ => []))

theorem completeNormalizationNestedDirectiveSmoke
    : operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationNestedDirectiveInputQuery)
        completeNormalizationNestedDirectiveOutputSnapshot
      = true := by
  native_decide

def completeNormalizationDuplicateIncludeInputQuery : Operation :=
  operationWith
    [
      .field "hero" "hero" [] [.include (.variable "x")] [.field "id" "id" [] [] []],
      .field "hero" "hero" [] [.include (.variable "x")] [.field "name" "name" [] [] []]
    ]

def completeNormalizationDuplicateIncludeOutputSnapshot : Operation :=
  operationWith
    [.inlineFragment none [.include (.variable "x")]
      [.field "hero" "hero" [] []
        [.field "id" "id" [] [] [], .field "name" "name" [] [] []]]]

theorem completeNormalizationDuplicateIncludeSmoke
    : operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationDuplicateIncludeInputQuery)
        completeNormalizationDuplicateIncludeOutputSnapshot
      = true := by
  native_decide

def completeNormalizationDuplicateSkipInputQuery : Operation :=
  operationWith
    [
      .field "hero" "hero" [] [.skip (.variable "x")] [.field "id" "id" [] [] []],
      .field "hero" "hero" [] [.skip (.variable "x")] [.field "name" "name" [] [] []]
    ]

def completeNormalizationDuplicateSkipOutputSnapshot : Operation :=
  operationWith
    [.inlineFragment none [.skip (.variable "x")]
      [.field "hero" "hero" [] []
        [.field "id" "id" [] [] [], .field "name" "name" [] [] []]]]

theorem completeNormalizationDuplicateSkipSmoke
    : operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationDuplicateSkipInputQuery)
        completeNormalizationDuplicateSkipOutputSnapshot
      = true := by
  native_decide

def completeNormalizationSpineConflictInputQuery : Operation :=
  operationWith
    [.inlineFragment none [.skip (.variable "x")]
      [
        .field "hero" "hero" [] [] [.field "id" "id" [] [] []],
        .field "hero" "hero" [] [.include (.variable "x")] [.field "name" "name" [] [] []]
      ]]

def completeNormalizationSpineConflictOutputSnapshot : Operation :=
  operationWith
    [.inlineFragment none [.skip (.variable "x")]
      [.field "hero" "hero" [] [] [.field "id" "id" [] [] []]]]

theorem completeNormalizationSpineConflictSmoke
    : operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationSpineConflictInputQuery)
        completeNormalizationSpineConflictOutputSnapshot
      = true := by
  native_decide

def completeNormalizationIncludeSkipInputQuery : Operation :=
  operationWith
    [.field "hero" "hero" [] [.include (.variable "x"), .skip (.variable "y")]
      [.field "id" "id" [] [] []]]

def completeNormalizationIncludeSkipOutputSnapshot : Operation :=
  operationWith
    (completeNormalizationRootBoolCaseBranchesFor ["x", "y"]
      (fun
        | [("x", false), ("y", false)] => []
        | [("x", false), ("y", true)] => []
        | [("x", true), ("y", false)] =>
            [.field "hero" "hero" [] [] [.field "id" "id" [] [] [],]]
        | [("x", true), ("y", true)] => []
        | _ => []))

theorem completeNormalizationIncludeSkipSmoke
    : operationEqBool
        (completeNormalizeOperation groundTypingSchema
          completeNormalizationIncludeSkipInputQuery)
        completeNormalizationIncludeSkipOutputSnapshot
      = true := by
  native_decide

def completeFeasibilitySchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [stringFieldDefinition "value"]
            interfaces := []
          },
        .object
          {
            name := "Other"
            fields := [stringFieldDefinition "value"]
            interfaces := []
          }
      ]
  }

def completeFeasibilityOperation (directives : List DirectiveApplication) : Operation :=
  {
    name := some "CompleteFeasibility"
    variableDefinitions := [booleanVariableDefinition "x"]
    selectionSet := [.field "value" "value" [] directives []]
  }

theorem completeFeasibilitySchema_queryPossibleTypes
    : completeFeasibilitySchema.getPossibleTypes "Query" = ["Query"] := by
  native_decide

theorem completeFeasibilitySchema_otherPossibleTypes
    : completeFeasibilitySchema.getPossibleTypes "Other" = ["Other"] := by
  native_decide

theorem completeFeasibilitySchema_queryTypeConditionFeasible
    : typeConditionStackFeasible completeFeasibilitySchema ["Query"] := by
  refine ⟨"Query", ?_⟩
  intro typeCondition htypeCondition
  simp at htypeCondition
  subst typeCondition
  simp [completeFeasibilitySchema_queryPossibleTypes]

theorem completeFeasibilitySchema_crossTypeConditionInfeasible
    : ¬ typeConditionStackFeasible completeFeasibilitySchema ["Other", "Query"] := by
  intro hfeasible
  rcases hfeasible with ⟨objectType, hall⟩
  have hother := hall "Other" (by simp)
  have hquery := hall "Query" (by simp)
  simp [completeFeasibilitySchema_otherPossibleTypes] at hother
  simp [completeFeasibilitySchema_queryPossibleTypes] at hquery
  exact (by decide : ("Other" : Name) ≠ "Query") (hother.symm.trans hquery)

theorem completeNormalizationBooleanConditionFeasible
    : operationBoolTypeConditionFeasible completeFeasibilitySchema
        (completeFeasibilityOperation [.include (.variable "x")]) := by
  have hqueryRoot : completeFeasibilitySchema.queryType = "Query" := by
    rfl
  simp [operationBoolTypeConditionFeasible, completeFeasibilityOperation,
    operationBoolVars, selectionSetBooleanVariables,
    selectionBooleanVariables, directivesBooleanVariables,
    directiveBooleanVariables, inputValueBooleanVariables, dedupBoolVars,
    boolVariableMem, allBoolCases, selectionBoolTypeConditionFeasible,
    directivesAllowIn, directiveAllowsIn,
    inputValueBoolIn?, BoolCase.lookup?, Operation.rootType,
    OperationType.rootType, hqueryRoot,
    completeFeasibilitySchema_queryTypeConditionFeasible]

def completeNormalizationContradictoryFieldInputQuery : Operation :=
  {
    name := some "CompleteContradictoryField"
    variableDefinitions := [booleanVariableDefinition "x"]
    selectionSet :=
      [
        .field "value" "value" [] [] [],
        .field "conditionalValue" "value" []
          [.include (.variable "x"), .skip (.variable "x")] []
      ]
  }

theorem completeNormalizationContradictoryFieldInfeasible
    : ¬ operationBoolTypeConditionFeasible completeFeasibilitySchema
          completeNormalizationContradictoryFieldInputQuery := by
  simp [operationBoolTypeConditionFeasible,
    completeNormalizationContradictoryFieldInputQuery,
    operationBoolVars, selectionSetBooleanVariables,
    selectionBooleanVariables, directivesBooleanVariables,
    directiveBooleanVariables, inputValueBooleanVariables, dedupBoolVars,
    boolVariableMem, allBoolCases, selectionBoolTypeConditionFeasible,
    directivesAllowIn, directiveAllowsIn,
    inputValueBoolIn?, BoolCase.lookup?]

def completeNormalizationInfeasibleTypeConditionInputQuery : Operation :=
  {
    name := some "CompleteInfeasibleTypeCondition"
    variableDefinitions := []
    selectionSet :=
      [.inlineFragment (some "Other") [] [.field "value" "value" [] [] []]]
  }

theorem completeNormalizationTypeConditionInfeasible
    : ¬ operationBoolTypeConditionFeasible completeFeasibilitySchema
          completeNormalizationInfeasibleTypeConditionInputQuery := by
  have hqueryRoot : completeFeasibilitySchema.queryType = "Query" := by
    rfl
  simp [operationBoolTypeConditionFeasible,
    completeNormalizationInfeasibleTypeConditionInputQuery,
    operationBoolVars, selectionSetBooleanVariables,
    selectionBooleanVariables, directivesBooleanVariables,
    dedupBoolVars, allBoolCases,
    selectionBoolTypeConditionFeasible,
    selectionSetBoolTypeConditionFeasible, selectionAllowsIn,
    directivesAllowIn, Operation.rootType, OperationType.rootType, hqueryRoot,
    completeFeasibilitySchema_crossTypeConditionInfeasible]

theorem completeNormalizationDirectiveVariablesUsed
    (hschema : SchemaWellFormedness.schemaWellFormed completeFeasibilitySchema)
    (hvalid
      : Validation.operationDefinitionValid completeFeasibilitySchema
          (completeFeasibilityOperation [.include (.variable "x")]))
    : Validation.operationVariablesUsed
        (completeNormalizeOperation completeFeasibilitySchema
          (completeFeasibilityOperation [.include (.variable "x")])) :=
  CompleteNormalization.completeNormalizeOperation_operationVariablesUsed
    completeFeasibilitySchema
    (completeFeasibilityOperation [.include (.variable "x")]) hschema hvalid
    completeNormalizationBooleanConditionFeasible

def completeNormalizationResolvers : Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      some <|
        match parentType, fieldName with
        | "Query", "hero" => .object "Human" ()
        | "Query", "search" => .object "Human" ()
        | "Human", "id" => .scalar "human-id"
        | "Human", "name" => .scalar "human-name"
        | "Human", "homePlanet" => .scalar "earth"
        | "Human", "companion" => .object "Droid" ()
        | "Droid", "id" => .scalar "droid-id"
        | "Droid", "name" => .scalar "droid-name"
        | "Droid", "primaryFunction" => .scalar "protocol"
        | _, _ => .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

def completeNormalizationVariableValues : Execution.VariableValues :=
  [("x", .boolean true), ("y", .boolean false)]

def executeCompleteNormalizedWithFuel
    (operation : Operation) (fuel : Nat)
    (source : Execution.ResolverValue)
    : Execution.ResponseValue :=
  Execution.executeQueryDataWithFuel groundTypingSchema
    completeNormalizationResolvers completeNormalizationVariableValues
    (completeNormalizeOperation groundTypingSchema operation) fuel source

theorem completeNormalizationExecutionSmoke
    : responseEqBool
        (Execution.executeQueryDataWithFuel groundTypingSchema
          completeNormalizationResolvers completeNormalizationVariableValues
          completeNormalizationDirectiveInputQuery 12
          (Execution.ResolverValue.object "Query" ()))
        (executeCompleteNormalizedWithFuel
          completeNormalizationDirectiveInputQuery 12
          (Execution.ResolverValue.object "Query" ()))
      = true := by
  native_decide

theorem completeNormalizationNestedExecutionSmoke
    : responseEqBool
        (Execution.executeQueryDataWithFuel groundTypingSchema
          completeNormalizationResolvers completeNormalizationVariableValues
          completeNormalizationNestedDirectiveInputQuery 16
          (Execution.ResolverValue.object "Query" ()))
        (executeCompleteNormalizedWithFuel
          completeNormalizationNestedDirectiveInputQuery 16
          (Execution.ResolverValue.object "Query" ()))
      = true := by
  native_decide

theorem completeNormalizationSmokeInputsHaveCompleteNormalTheorem
    : completeNormalizeOperationNormal groundTypingSchema
        completeNormalizationDirectiveInputQuery
      ∧ completeNormalizeOperationNormal groundTypingSchema
          completeNormalizationGlobalVariablesInputQuery
      ∧ completeNormalizeOperationNormal groundTypingSchema
          completeNormalizationAbstractInputQuery
      ∧ completeNormalizeOperationNormal groundTypingSchema
          completeNormalizationNestedDirectiveInputQuery := by
  exact ⟨
    CompleteNormalization.completeNormalizeOperation_normal
      groundTypingSchema completeNormalizationDirectiveInputQuery,
    CompleteNormalization.completeNormalizeOperation_normal
      groundTypingSchema completeNormalizationGlobalVariablesInputQuery,
    CompleteNormalization.completeNormalizeOperation_normal
      groundTypingSchema completeNormalizationAbstractInputQuery,
    CompleteNormalization.completeNormalizeOperation_normal
      groundTypingSchema completeNormalizationNestedDirectiveInputQuery⟩

#check
  completeNormalOperationsEqualUpToReorderingSemanticallyEquivalent
#check
  CompleteNormalization.complete_normal_operations_equalUpToReordering_semanticallyEquivalent
#check
  CompleteNormalization.operationBoolVarsEquivalent_of_completeNormalOperationsEqualUpToReordering
#check operationsSemanticallyEquivalentForCompleteBoolVars
#check
  completeNormalizeOperationsEqualUpToReorderingSemanticallyEquivalent
#check
  CompleteNormalization.completeNormalizeOperations_equalUpToReordering_semanticallyEquivalent
#check completeNormalOperationsSemanticallyEquivalentEqualUpToReordering
#check
  CompleteNormalization.complete_normal_operations_semanticallyEquivalent_equalUpToReordering
#check CompleteNormalization.operationBoolVarsEquivalent_of_completeNormal_semantics
#check completeNormalizeOperationUniqueUpToReordering
#check
  CompleteNormalization.completeNormalizeOperation_uniqueUpToReordering

end NormalForm
end Tests
end GraphQL
