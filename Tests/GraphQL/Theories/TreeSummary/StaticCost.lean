import GraphQL.Theories.TreeSummary.StaticCost
import Proofs.GraphQL.Theories.TreeSummary.AnnotationErasure
import Proofs.GraphQL.Theories.TreeSummary.StaticCost

namespace GraphQL
namespace Tests
namespace TreeSummary
namespace StaticCost

open GraphQL.TreeSummary.StaticCost
open GraphQL.TreeSummary.StaticCost.ExactCases
open GraphQL.TreeSummary
open GraphQL.AnnotatedExecution

def staticCostSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [
                { name := "book", outputType := .named "Book" },
                { name := "bestsellers", outputType := .list (.named "Book") },
                {
                  name := "newest"
                  outputType := .list (.named "Book")
                  arguments := [{ name := "limit", inputType := .named "Int" }]
                },
                {
                  name := "users"
                  outputType := .list (.named "User")
                  arguments := [{ name := "max", inputType := .named "Int" }]
                },
                {
                  name := "rangeBooks"
                  outputType := .list (.named "Book")
                  arguments :=
                    [
                      { name := "first", inputType := .named "Int" },
                      { name := "last", inputType := .named "Int" }
                    ]
                },
                {
                  name := "container"
                  outputType := .named "Container"
                  arguments := [{ name := "first", inputType := .named "Int" }]
                },
                {
                  name := "defaultContainer"
                  outputType := .named "Container"
                  arguments :=
                    [{
                      name := "first"
                      inputType := .named "Int"
                      defaultValue := some (.int 4)
                    }]
                },
                {
                  name := "listContainer"
                  outputType := .list (.named "Container")
                  arguments := [{ name := "first", inputType := .named "Int" }]
                },
                {
                  name := "fieldWithCost"
                  outputType := .named "Int"
                  arguments := [{ name := "approx", inputType := .named "Boolean" }]
                },
                { name := "publication", outputType := .named "Publication" },
                {
                  name := "inputWithCost"
                  outputType := .named "Int"
                  arguments :=
                    [{ name := "filter", inputType := .named "Filter" }]
                },
                {
                  name := "listInputWithCost"
                  outputType := .named "Int"
                  arguments := [{ name := "ids", inputType := .list (.named "ID") }]
                }
              ]
          },
        .object
          {
            name := "Book"
            interfaces := ["Publication"]
            fields :=
              [
                { name := "title", outputType := .named "String" },
                { name := "author", outputType := .named "Author" },
                { name := "publisher", outputType := .named "Publisher" }
              ]
          },
        .object
          {
            name := "Magazine"
            interfaces := ["Publication"]
            fields := [{ name := "title", outputType := .named "String" }]
          },
        .interface
          {
            name := "Publication"
            fields := [{ name := "title", outputType := .named "String" }]
          },
        .object
          {
            name := "Author"
            fields := [{ name := "name", outputType := .named "String" }]
          },
        .object
          {
            name := "User"
            fields := [{ name := "age", outputType := .named "Int" }]
          },
        .object
          {
            name := "Publisher"
            fields :=
              [
                { name := "name", outputType := .named "String" },
                { name := "address", outputType := .named "Address" }
              ]
          },
        .object
          {
            name := "Address"
            fields := [{ name := "zipCode", outputType := .named "Int" }]
          },
        .object
          {
            name := "Container"
            fields :=
              [
                { name := "page", outputType := .list (.named "Book") },
                { name := "recent", outputType := .list (.named "Book") },
                { name := "metadata", outputType := .named "String" }
              ]
          },
        .inputObject
          {
            name := "Filter"
            inputFields :=
              [
                { name := "approx", inputType := .named "Boolean" },
                { name := "nested", inputType := .named "Filter" }
              ]
          }
      ]
  }

def staticCostModel : CostModel :=
  {
    defaultListSize := 10
    cost :=
      fun coordinate =>
        match coordinate with
        | .typeDefinition "Address" => some 5
        | .typeDefinition "Magazine" => some 7
        | .fieldDefinition { parentType := "Query", fieldName := "fieldWithCost" } =>
            some 5
        | .fieldDefinition { parentType := "Query", fieldName := "inputWithCost" } =>
            some 5
        | .fieldDefinition { parentType := "User", fieldName := "age" } => some 2
        | .argumentDefinition
            { parentType := "Query", fieldName := "fieldWithCost" } "approx" =>
            some (-3)
        | .argumentDefinition
            { parentType := "Query", fieldName := "inputWithCost" } "filter" =>
            some 15
        | .argumentDefinition
            { parentType := "Query", fieldName := "listInputWithCost" } "ids" =>
            some 3
        | .inputFieldDefinition "Filter" "approx" => some (-12)
        | _ => none
    listSize :=
      fun coordinate =>
        match coordinate with
        | { parentType := "Query", fieldName := "bestsellers" } =>
            some { assumedSize := some 5 }
        | { parentType := "Query", fieldName := "newest" } =>
            some { slicingArguments := ["limit"] }
        | { parentType := "Query", fieldName := "users" } =>
            some { slicingArguments := ["max"] }
        | { parentType := "Query", fieldName := "rangeBooks" } =>
            some
              {
                assumedSize := some 2
                slicingArguments := ["first", "last"]
                requireOneSlicingArgument := false
              }
        | { parentType := "Query", fieldName := "container" } =>
            some
              {
                slicingArguments := ["first"]
                sizedFields := ["page"]
                requireOneSlicingArgument := false
              }
        | { parentType := "Query", fieldName := "defaultContainer" } =>
            some
              {
                slicingArguments := ["first"]
                sizedFields := ["page"]
              }
        | { parentType := "Query", fieldName := "listContainer" } =>
            some
              {
                slicingArguments := ["first"]
                sizedFields := ["page"]
              }
        | _ => none
  }

def defaultedNestedFilterDefinition : InputValueDefinition :=
  {
    name := "nested"
    inputType := .named "DefaultedNestedFilter"
    defaultValue := some (.object [])
  }

def defaultedFilterArgumentDefinition : InputValueDefinition :=
  {
    name := "filter"
    inputType := .named "DefaultedFilter"
    defaultValue := some (.object [])
  }

-- Focused schema for execution-spec GraphQL argument coercion. The argument default
-- introduces `nested`, whose default in turn introduces `approx`.
def defaultedInputSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [{
                name := "search"
                outputType := .named "Int"
                arguments := [defaultedFilterArgumentDefinition]
              }]
          },
        .inputObject
          {
            name := "DefaultedFilter"
            inputFields := [defaultedNestedFilterDefinition]
          },
        .inputObject
          {
            name := "DefaultedNestedFilter"
            inputFields :=
              [{
                name := "approx"
                inputType := .named "Boolean"
                defaultValue := some (.boolean true)
              }]
          }
      ]
  }

def defaultedInputCostModel : CostModel :=
  {
    defaultListSize := 1
    cost :=
      fun coordinate =>
        match coordinate with
        | .fieldDefinition { parentType := "Query", fieldName := "search" } =>
            some 5
        | .argumentDefinition { parentType := "Query", fieldName := "search" } "filter" =>
            some 15
        | .inputFieldDefinition "DefaultedFilter" "nested" => some 4
        | .inputFieldDefinition "DefaultedNestedFilter" "approx" => some (-12)
        | _ => none
  }

def zeroListCostModel : CostModel :=
  {
    staticCostModel with
      listSize :=
        fun coordinate =>
          match coordinate with
          | { parentType := "Query", fieldName := "bestsellers" } =>
              some { assumedSize := some 0 }
          | _ => staticCostModel.listSize coordinate
  }

-- Regression model for IBM's signed type weights. The negative `Book` contribution
-- must offset the positive `String` contribution instead of being clamped on lookup.
def negativeTypeCostModel : CostModel :=
  {
    defaultListSize := 10
    cost :=
      fun coordinate =>
        match coordinate with
        | .typeDefinition "Book" => some (-7)
        | .typeDefinition "String" => some 5
        | _ => none
  }

def negativeFactoringCostModel : CostModel :=
  {
    defaultListSize := 10
    cost :=
      fun coordinate =>
        match coordinate with
        | .typeDefinition "Query" => some 0
        | .typeDefinition "Book" => some (-7)
        | .typeDefinition "String" => some 5
        | _ => none
  }

def operation (selectionSet : List Selection) : Operation :=
  { selectionSet }

def field (fieldName : Name) (arguments : List Argument := [])
    (selectionSet : List Selection := [])
    : Selection :=
  .field fieldName fieldName arguments [] selectionSet

def bookSelections : List Selection :=
  [
    field "title",
    field "author" [] [field "name"],
    field "publisher" [] [field "name", field "address" [] [field "zipCode"]]
  ]

def weightedApproxVariableOperation : Operation :=
  {
    variableDefinitions := [{ name := "approx", typeRef := .named "Boolean" }]
    selectionSet :=
      [field "fieldWithCost" [{ name := "approx", value := .variable "approx" }]]
  }

def weightedInputFieldVariableOperation : Operation :=
  {
    variableDefinitions := [{ name := "approx", typeRef := .named "Boolean" }]
    selectionSet :=
      [field "inputWithCost"
        [{
          name := "filter"
          value := .object [("approx", .variable "approx")]
        }]]
  }

def defaultedFilterVariableOperation (defaultValue : Option ConstInputValue := none)
    : Operation :=
  {
    variableDefinitions :=
      [{
        name := "filter"
        typeRef := .named "DefaultedFilter"
        defaultValue
      }]
    selectionSet :=
      [field "search" [{ name := "filter", value := .variable "filter" }]]
  }

def defaultedNestedVariableOperation : Operation :=
  {
    variableDefinitions :=
      [{ name := "nested", typeRef := .named "DefaultedNestedFilter" }]
    selectionSet :=
      [field "search"
        [{
          name := "filter"
          value := .object [("nested", .variable "nested")]
        }]]
  }

theorem defaultAndTypeCostsSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation [field "book" [] bookSelections])
      = { typeCost := 9, fieldCost := 4 } := by
  native_decide

theorem abstractTypeUsesMaximumPossibleObjectWeightRegression
    : namedTypeCost staticCostSchema staticCostModel "Publication" = 7 := by
  native_decide

theorem abstractOutputUsesMaximumPossibleObjectWeightRegression
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation [field "publication" [] [field "title"]])
      = { typeCost := 8, fieldCost := 1 } := by
  native_decide

theorem negativeTypeWeightIsPreservedRegression
    : namedTypeCost staticCostSchema negativeTypeCostModel "Book" = -7 := by
  native_decide

theorem negativeTypeWeightOffsetsChildCostRegression
    : estimateOperationWithVariables staticCostSchema negativeTypeCostModel []
        (operation [field "book" [] [field "title"]])
      = { typeCost := 1, fieldCost := 1 } := by
  native_decide

theorem syntacticSignedTypeCostSmoke
    : GraphQL.TreeSummary.StaticCost.Syntactic.estimateOperationWithVariables
        staticCostSchema negativeTypeCostModel []
        (operation [field "book" [] [field "title"]])
      = { typeCost := 1, fieldCost := 1 } := by
  native_decide

def splitConditionalBookOperation : Operation :=
  {
    variableDefinitions :=
      [
        { name := "a", typeRef := .named "Boolean" },
        { name := "b", typeRef := .named "Boolean" }
      ]
    selectionSet :=
      [
        .field "book" "book" [] [.include (.variable "a")] [field "title"],
        .field "book" "book" [] [.include (.variable "b")]
          [field "author" [] [field "name"]]
      ]
  }

-- Regression: Syntactic remains a distinct backend for signed type costs. Its generic
-- soundness theorem deliberately requires nonnegative type costs because factoring the
-- two selected field pieces duplicates the negative `Book` contribution here.
theorem syntacticNegativeTypeCostDoesNotFallbackRegression
    : GraphQL.TreeSummary.StaticCost.Syntactic.estimateOperationWithVariables
        staticCostSchema negativeFactoringCostModel
        [("a", .boolean true), ("b", .boolean true)] splitConditionalBookOperation
      = { typeCost := 0, fieldCost := 3 } := by
  native_decide

theorem exactCasesSignedTypeCostRegression
    : estimateOperationWithVariables staticCostSchema negativeFactoringCostModel
        [("a", .boolean true), ("b", .boolean true)] splitConditionalBookOperation
      = { typeCost := 4, fieldCost := 2 } := by
  native_decide

theorem assumedListSizeSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation [field "bestsellers" [] bookSelections])
      = { typeCost := 41, fieldCost := 16 } := by
  native_decide

theorem nullableZeroSizedListIsAdmissibleSmoke
    : responseFieldAdmissible staticCostSchema zeroListCostModel
        {
          parentType := "Query"
          fieldName := "bestsellers"
          originalArguments := []
          coercedArguments := .success []
        }
        .null .empty [] := by
  have hlookup : staticCostSchema.lookupField "Query" "bestsellers"
      = some { name := "bestsellers", outputType := .list (.named "Book") } := by
    rfl
  simp [responseFieldAdmissible, hlookup, zeroListCostModel, staticCostModel,
    expectedListSize?, ListSize.expectedSize?, staticInstanceCount,
    actualInstanceCount, ResponseObservation.empty]

theorem numericSlicingArgumentSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation [field "newest" [{ name := "limit", value := .int 3 }] bookSelections])
      = { typeCost := 25, fieldCost := 10 } := by
  native_decide

-- IBM Cost Directives specification, Static Query Analysis example.
theorem ibmStaticFieldCostExample
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation [field "users" [{ name := "max", value := .int 5 }] [field "age"]])
      = { typeCost := 6, fieldCost := 11 } := by
  native_decide

theorem operationVariableDefaultUsedForSlicingSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        {
          variableDefinitions :=
            [{
              name := "limit"
              typeRef := .named "Int"
              defaultValue := some (.int 3)
            }]
          selectionSet :=
            [field "newest" [{ name := "limit", value := .variable "limit" }]
              bookSelections]
        }
      = { typeCost := 25, fieldCost := 10 } := by
  native_decide

theorem sizedFieldSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation
          [field "container" [{ name := "first", value := .int 3 }]
            [field "page" [] [field "title"], field "recent" [] [field "title"]]])
      = { typeCost := 15, fieldCost := 3 } := by
  native_decide

theorem slicingArgumentUsesSchemaDefaultSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation [field "defaultContainer" [] [field "page" [] [field "title"]]])
      = { typeCost := 6, fieldCost := 2 } := by
  native_decide

-- IBM treats an undefined variable as an omitted argument, so the schema argument
-- default still supplies the list bound. Explicit `null` remains distinct from this
-- case and does not activate the schema default.
theorem slicingArgumentUsesSchemaDefaultForUndefinedVariableRegression
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        {
          variableDefinitions := [{ name := "first", typeRef := .named "Int" }]
          selectionSet :=
            [field "defaultContainer" [{ name := "first", value := .variable "first" }]
              [field "page" [] [field "title"]]]
        }
      = { typeCost := 6, fieldCost := 2 } := by
  native_decide

theorem explicitNullSlicingArgumentSuppressesSchemaDefaultRegression
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation
          [field "defaultContainer" [{ name := "first", value := .null }]
            [field "page" [] [field "title"]]])
      = { typeCost := 12, fieldCost := 2 } := by
  native_decide

theorem multipleSlicingArgumentsUseMaximumRegression
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation
          [field "rangeBooks"
            [{ name := "first", value := .int 3 }, { name := "last", value := .int 5 }]
            [field "title"]])
      = { typeCost := 6, fieldCost := 1 } := by
  native_decide

theorem slicingArgumentTakesPrecedenceOverAssumedSizeRegression
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation
          [field "rangeBooks" [{ name := "first", value := .int 1 }] [field "title"]])
      = { typeCost := 2, fieldCost := 1 } := by
  native_decide

theorem sizedFieldsRedirectsSizeFromAnnotatedListSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation
          [field "listContainer" [{ name := "first", value := .int 3 }]
            [field "page" [] [field "title"]]])
      = { typeCost := 41, fieldCost := 11 } := by
  native_decide

theorem fieldCallCostIsNotMultipliedSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation [field "fieldWithCost"])
      = { typeCost := 1, fieldCost := 5 } := by
  native_decide

-- IBM's negative-argument example: the signed argument reduces the containing field
-- before the complete field-call result is clamped.
theorem negativeArgumentReducesFieldCostRegression
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation [field "fieldWithCost" [{ name := "approx", value := .boolean true }]])
      = { typeCost := 1, fieldCost := 2 } := by
  native_decide

-- Undefined is omission, not a leaf value. Without a schema default the argument
-- coordinate is absent; explicit `null` is present and still pays its signed weight.
theorem undefinedWeightedArgumentIsOmittedRegression
    : estimateOperationWithVariables staticCostSchema staticCostModel []
          weightedApproxVariableOperation
        = { typeCost := 1, fieldCost := 5 }
      ∧ estimateOperationWithVariables staticCostSchema staticCostModel
          [("approx", .null)] weightedApproxVariableOperation
        = { typeCost := 1, fieldCost := 2 } := by
  native_decide

theorem signedInputCostIsClampedAtFieldBoundarySmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation
          [field "inputWithCost"
            [{ name := "filter", value := .object [("approx", .boolean true)] }]])
      = { typeCost := 1, fieldCost := 8 } := by
  native_decide

theorem undefinedInputFieldWithoutDefaultIsOmittedRegression
    : estimateOperationWithVariables staticCostSchema staticCostModel []
          weightedInputFieldVariableOperation
        = { typeCost := 1, fieldCost := 20 }
      ∧ estimateOperationWithVariables staticCostSchema staticCostModel
          [("approx", .null)] weightedInputFieldVariableOperation
        = { typeCost := 1, fieldCost := 8 } := by
  native_decide

theorem coercedArgumentValuesMaterializeNestedDefaultsRegression
    : Argument.argumentsEquivalent
        (argumentCoercionResultArguments
          (Execution.coerceArgumentValues defaultedInputSchema []
            [defaultedFilterArgumentDefinition] []))
        [{
          name := "filter"
          value := .object [("nested", .object [("approx", .boolean true)])]
        }] := by
  native_decide

-- StaticCost consumes the coerced map without sorting input-object fields. Semantic
-- order invariance is a proof property of the sizing and cost folds, not a runtime
-- normalization pass.
theorem argumentValuesPreserveInputObjectFieldOrderRegression
    : argumentValues
        [{
          name := "filter"
          value := .object [("nested", .object []), ("approx", .boolean true)]
        }]
        "filter"
      = [.object [("nested", .object []), ("approx", .boolean true)]] := by
  rfl

-- An omitted argument and an argument whose variable is undefined both activate the
-- schema argument default. Nested input-field defaults are materialized before weights
-- are folded. Both TreeSummary backends consume the same StaticCost algebra.
theorem weightedInputDefaultsApplyToOmittedAndUndefinedArgumentsRegression
    : estimateOperationWithVariables defaultedInputSchema defaultedInputCostModel []
          (operation [field "search"])
        = { typeCost := 1, fieldCost := 12 }
      ∧ estimateOperationWithVariables defaultedInputSchema defaultedInputCostModel []
          defaultedFilterVariableOperation
        = { typeCost := 1, fieldCost := 12 }
      ∧ GraphQL.TreeSummary.StaticCost.Syntactic.estimateOperationWithVariables
          defaultedInputSchema defaultedInputCostModel []
          (operation [field "search"])
        = { typeCost := 1, fieldCost := 12 }
      ∧ GraphQL.TreeSummary.StaticCost.Syntactic.estimateOperationWithVariables
          defaultedInputSchema defaultedInputCostModel []
          defaultedFilterVariableOperation
        = { typeCost := 1, fieldCost := 12 } := by
  native_decide

theorem suppliedVariableInputObjectMaterializesFieldDefaultsRegression
    : estimateOperationWithVariables defaultedInputSchema defaultedInputCostModel
          [("filter", .object [])] defaultedFilterVariableOperation
        = { typeCost := 1, fieldCost := 12 }
      ∧ GraphQL.TreeSummary.StaticCost.Syntactic.estimateOperationWithVariables
          defaultedInputSchema defaultedInputCostModel [("filter", .object [])]
          defaultedFilterVariableOperation
        = { typeCost := 1, fieldCost := 12 } := by
  native_decide

-- The same missing-value rule applies at an input-object field. Explicit `null` is a
-- present value: it pays the containing coordinate but suppresses that field's default
-- and the nested `approx` contribution introduced by the default.
theorem nestedUndefinedUsesDefaultButExplicitNullSuppressesItRegression
    : estimateOperationWithVariables defaultedInputSchema defaultedInputCostModel []
          defaultedNestedVariableOperation
        = { typeCost := 1, fieldCost := 12 }
      ∧ estimateOperationWithVariables defaultedInputSchema defaultedInputCostModel []
          (operation
            [field "search" [{ name := "filter", value := .object [("nested", .null)] }]])
        = { typeCost := 1, fieldCost := 24 }
      ∧ estimateOperationWithVariables defaultedInputSchema defaultedInputCostModel []
          (operation [field "search" [{ name := "filter", value := .null }]])
        = { typeCost := 1, fieldCost := 20 } := by
  native_decide

theorem operationDefaultAndSuppliedNullPrecedenceForWeightedInputRegression
    : estimateOperationWithVariables defaultedInputSchema defaultedInputCostModel []
          (defaultedFilterVariableOperation (some (.object [("nested", .null)])))
        = { typeCost := 1, fieldCost := 24 }
      ∧ estimateOperationWithVariables defaultedInputSchema defaultedInputCostModel
          [("filter", .null)]
          (defaultedFilterVariableOperation (some (.object [("nested", .null)])))
        = { typeCost := 1, fieldCost := 20 } := by
  native_decide

-- The concrete annotated-response interpretation consumes the same schema-coerced
-- resolver argument map as the abstract estimators.
theorem responseFieldCostUsesCoercedArgumentsRegression
    : responseFieldCost defaultedInputSchema defaultedInputCostModel
          {
            parentType := "Query"
            fieldName := "search"
            originalArguments := []
            coercedArguments :=
              Execution.coerceArgumentValues defaultedInputSchema []
                [defaultedFilterArgumentDefinition] []
          }
          (.scalar "result") .empty []
        = { typeCost := 0, fieldCost := 12 }
      ∧ responseFieldCost defaultedInputSchema defaultedInputCostModel
          {
            parentType := "Query"
            fieldName := "search"
            originalArguments :=
              [{ name := "filter", value := .variable "undefined" }]
            coercedArguments :=
              Execution.coerceArgumentValues defaultedInputSchema []
                [defaultedFilterArgumentDefinition]
                [{ name := "filter", value := .variable "undefined" }]
          }
          (.scalar "result") .empty []
        = { typeCost := 0, fieldCost := 12 }
      ∧ responseFieldCost defaultedInputSchema defaultedInputCostModel
          {
            parentType := "Query"
            fieldName := "search"
            originalArguments := [{ name := "filter", value := .null }]
            coercedArguments :=
              Execution.coerceArgumentValues defaultedInputSchema []
                [defaultedFilterArgumentDefinition]
                [{ name := "filter", value := .null }]
          }
          (.scalar "result") .empty []
        = { typeCost := 0, fieldCost := 20 } := by
  native_decide

theorem recursiveInputObjectCostTerminatesSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation
          [field "inputWithCost"
            [{
              name := "filter"
              value := .object [("nested", .object [("approx", .boolean true)])]
            }]])
      = { typeCost := 1, fieldCost := 9 } := by
  native_decide

theorem listArgumentWeightIsPaidOnceSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation
          [field "listInputWithCost"
            [{ name := "ids", value := .list [.string "a", .string "b", .string "c"] }]])
      = { typeCost := 1, fieldCost := 3 } := by
  native_decide

theorem duplicateCollectedFieldCostsOnceSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        (operation [field "book" [] [field "title"], field "book" [] [field "title"]])
      = { typeCost := 2, fieldCost := 1 } := by
  native_decide

def defaultPrunedOperation : Operation :=
  {
    variableDefinitions :=
      [{
        name := "skipBook"
        typeRef := .named "Boolean"
        defaultValue := some (.boolean true)
      }]
    selectionSet :=
      [.field "book" "book" [] [.skip (.variable "skipBook")] bookSelections]
  }

theorem operationVariableDefaultPrunesCostSmoke
    : estimateOperationWithVariables staticCostSchema staticCostModel []
        defaultPrunedOperation
      = { typeCost := 1, fieldCost := 0 } := by
  native_decide

theorem syntacticVariableDefaultPrunesCostSmoke
    : GraphQL.TreeSummary.StaticCost.Syntactic.estimateOperationWithVariables
        staticCostSchema staticCostModel [] defaultPrunedOperation
      = { typeCost := 1, fieldCost := 0 } := by
  native_decide

def staticCostResolvers : Execution.Resolvers PUnit :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "bestsellers" =>
            some (.list [.object "Book" (), .object "Book" (), .object "Book" ()])
        | "Query", "users" =>
            some (.list [.object "User" (), .object "User" (), .object "User" ()])
        | "User", "age" => some (.scalar "42")
        | "Book", "title" => some (.scalar "title")
        | "Book", "author" => some (.object "Author" ())
        | "Book", "publisher" => some (.object "Publisher" ())
        | "Author", "name" => some (.scalar "author")
        | "Publisher", "name" => some (.scalar "publisher")
        | "Publisher", "address" => some (.object "Address" ())
        | "Address", "zipCode" => some (.scalar "12345")
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intro parentType fieldName firstArguments laterArguments source _hequivalent
      rfl
  }

def negativeTypeCostResolvers : Execution.Resolvers PUnit :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "book" => some (.object "Book" ())
        | "Book", "title" => some (.scalar "title")
        | "Book", "author" => some (.object "Author" ())
        | "Author", "name" => some (.scalar "author")
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intro parentType fieldName firstArguments laterArguments source _hequivalent
      rfl
  }

def bestsellersExecution : Execution.Response :=
  Execution.executeQuery staticCostSchema staticCostResolvers []
    (operation [field "bestsellers" [] bookSelections]) (.object "Query" ())

def bestsellersAnnotatedResponse : AnnotatedResponse :=
  executeQueryAnnotated staticCostSchema staticCostResolvers []
    (operation [field "bestsellers" [] bookSelections]) (.object "Query" ())

def usersAnnotatedResponse : AnnotatedResponse :=
  executeQueryAnnotated staticCostSchema staticCostResolvers []
    (operation [field "users" [{ name := "max", value := .int 5 }] [field "age"]])
    (.object "Query" ())

def nullCostedFieldAnnotatedResponse : AnnotatedResponse :=
  executeQueryAnnotated staticCostSchema staticCostResolvers []
    (operation [field "fieldWithCost"]) (.object "Query" ())

def negativeTypeCostAnnotatedResponse : AnnotatedResponse :=
  executeQueryAnnotated staticCostSchema negativeTypeCostResolvers []
    (operation [field "book" [] [field "title"]]) (.object "Query" ())

def splitConditionalBookAnnotatedResponse : AnnotatedResponse :=
  executeQueryAnnotated staticCostSchema negativeTypeCostResolvers
    [("a", .boolean true), ("b", .boolean true)] splitConditionalBookOperation
    (.object "Query" ())

theorem annotatedResponseErasesToExecution
    : bestsellersAnnotatedResponse.toResponse = bestsellersExecution := by
  exact executeQueryAnnotated_toResponse staticCostSchema staticCostResolvers []
    (operation [field "bestsellers" [] bookSelections]) (.object "Query" ())

def newestVariableField : Execution.ExecutableField :=
  {
    parentType := "Query"
    responseName := "newest"
    fieldName := "newest"
    arguments := [{ name := "limit", value := .variable "limit" }]
    selectionSet := []
  }

def newestVariableFieldArguments : Option (List Argument) :=
  match staticCostSchema.lookupField "Query" "newest" with
  | none => none
  | some fieldDefinition =>
      match singleAnnotatedResponseFieldResult staticCostSchema [("limit", .int 3)]
              fieldDefinition "newest" newestVariableField (.ok (.null, 0)) with
      | .ok ([.resolved _responseName definition _value], _errors) =>
          some (argumentCoercionResultArguments definition.coercedArguments)
      | _ => none

theorem annotatedResponseArgumentsAreResolved
    : newestVariableFieldArguments = some [{ name := "limit", value := .int 3 }] := by
  simp [newestVariableFieldArguments, staticCostSchema, newestVariableField,
    singleAnnotatedResponseFieldResult, resolvedFieldProvenance,
    argumentCoercionResultArguments, Schema.lookupField, Schema.lookupType,
    Schema.lookupInputObject,
    Schema.allTypes, Schema.builtinScalarDefinitions, TypeDefinition.fields?,
    TypeDefinition.name, BuiltinScalar.name, List.find?, Argument.lookupValue?,
    ConstInputValue.toInputValue, ConstInputValue.ofInputValue?,
    Execution.CoercedArgument.toArgument, Execution.coerceArgumentValues,
    Execution.coerceArgumentValue,
    Execution.coerceInputValue, Execution.coerceInputValueFuel,
    Execution.schemaInputCoercionFuel, Execution.typeDefinitionsInputCoercionFuel,
    Execution.typeDefinitionInputCoercionFuel, Execution.fieldDefinitionsInputCoercionFuel,
    Execution.inputValueDefinitionsCoercionFuel,
    Execution.inputValueDefinitionCoercionFuel,
    Execution.referencedVariableValuesCoercionFuel,
    Execution.inputValueCoercionFuel, Execution.coerceInputValueBounded,
    Execution.lookupVariableValue?]

theorem actualResponseCostSmoke
    : actualCost staticCostSchema staticCostModel bestsellersAnnotatedResponse
      = { typeCost := 25, fieldCost := 10 } := by
  native_decide

theorem negativeTypeWeightReducesActualCostRegression
    : actualCost staticCostSchema negativeTypeCostModel negativeTypeCostAnnotatedResponse
      = { typeCost := -1, fieldCost := 1 } := by
  native_decide

theorem splitConditionalBookActualCostRegression
    : actualCost staticCostSchema negativeFactoringCostModel
        splitConditionalBookAnnotatedResponse
      = { typeCost := 4, fieldCost := 2 } := by
  native_decide

theorem syntacticNegativeTypeCostCanUnderestimateRegression
    : ¬ actualCost staticCostSchema negativeFactoringCostModel
          splitConditionalBookAnnotatedResponse
        ≤ GraphQL.TreeSummary.StaticCost.Syntactic.estimateOperationWithVariables
            staticCostSchema negativeFactoringCostModel
            [("a", .boolean true), ("b", .boolean true)]
            splitConditionalBookOperation := by
  native_decide

theorem nullFieldStillPaysResolverCostSmoke
    : actualCost staticCostSchema staticCostModel nullCostedFieldAnnotatedResponse
      = { typeCost := 1, fieldCost := 5 } := by
  native_decide

-- IBM Cost Directives specification, Query Response Analysis example.
theorem ibmResponseFieldCostExample
    : actualCost staticCostSchema staticCostModel usersAnnotatedResponse
      = { typeCost := 4, fieldCost := 7 } := by
  native_decide

theorem executedResponseCostBoundedSmoke
    : actualCost staticCostSchema staticCostModel bestsellersAnnotatedResponse
      ≤ estimateOperationWithVariables staticCostSchema staticCostModel []
          (operation [field "bestsellers" [] bookSelections]) := by
  native_decide

theorem syntacticSoundnessWitnessSmoke
    : GraphQL.TreeSummary.StaticCost.Syntactic.SoundWithVariables
        staticCostSchema staticCostModel
        (operation [field "bestsellers" [] bookSelections]) :=
  GraphQL.TreeSummary.StaticCost.Syntactic.soundWithVariables
    staticCostSchema staticCostModel
    (operation [field "bestsellers" [] bookSelections])

theorem summaryOptimalWithVariablesApiSmoke (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : ExactCases.SummaryOptimalWithVariables schema model variableValues operation :=
  ExactCases.summaryOptimalWithVariables schema model variableValues operation

end StaticCost
end TreeSummary
end Tests
end GraphQL
