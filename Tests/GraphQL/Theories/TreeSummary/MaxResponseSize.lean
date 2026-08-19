import Proofs.GraphQL.Theories.TreeSummary.MaxResponseSize

namespace GraphQL
namespace Tests
namespace TreeSummary
namespace MaxResponseSize

open GraphQL.TreeSummary
open GraphQL.TreeSummary.MaxResponseSize
open GraphQL.AnnotatedExecution

def smokeSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [.object
        {
          name := "Query"
          fields := [{ name := "answer", outputType := .named "String" }]
        }]
  }

def smokeAnnotatedResponse : AnnotatedResponse :=
  {
    data :=
      .object "Query"
        [.resolved "answer"
          {
            parentType := "Query"
            fieldName := "answer"
            originalArguments := []
            coercedArguments := .success []
          }
          (.scalar "42")]
  }

def smokeResponse : Execution.Response :=
  smokeAnnotatedResponse.toResponse

theorem actualSizeSmoke : actualSize smokeResponse = 1 := by
  native_decide

theorem annotatedSizeErasureSmoke
    : actualSize smokeResponse = annotatedSize smokeSchema smokeAnnotatedResponse := by
  exact actualSize_toResponse_eq_annotatedSize smokeSchema smokeAnnotatedResponse

theorem nestedResolverListsBoundedSmoke
    : resolverValueListsBounded 2
        ((.list [.list [.scalar "a", .scalar "b"], .list []])
          : Execution.ResolverValue PUnit) := by
  simp [resolverValueListsBounded, resolverValuesListsBounded]

theorem responseWithinListSizeSmoke
    : ResponseWithinListSize smokeSchema 10 smokeAnnotatedResponse := by
  have fieldLookup :
      smokeSchema.lookupField "Query" "answer" =
        some ({ name := "answer", outputType := .named "String" }
          : FieldDefinition) := by
    rfl
  simp [ResponseWithinListSize,
    GraphQL.TreeSummary.MaxResponseSize.foldAnnotatedResponse,
    smokeAnnotatedResponse,
    concreteAlgebra, responseFieldObservation, listMultiplier,
    responseValueChildMultiplicity, ResponseObservation.empty,
    ResponseObservation.combine, TreeSummary.foldAnnotatedResponse,
    foldAnnotatedResponseValueChildren, foldAnnotatedResponseFields,
    fieldLookup]

def complementaryBooleanBranchesOperation : Operation :=
  {
    selectionSet :=
      [
        .field "a" "answer" [] [.include (.variable "x")] [],
        .field "b" "answer" [] [.skip (.variable "x")] []
      ]
  }

-- Complementary siblings are alternative global Boolean cases, so they are joined
-- rather than counted together.
theorem complementaryBooleanBranchesEstimateOne
    : ExactCases.estimateOperation smokeSchema 10 complementaryBooleanBranchesOperation
      = 1 := by
  native_decide

theorem syntacticComplementaryBooleanBranchesEstimateOne
    : GraphQL.TreeSummary.MaxResponseSize.Syntactic.estimateOperation
        smokeSchema 10 complementaryBooleanBranchesOperation
      = 1 := by
  native_decide

def compatibleBooleanBranchesOperation : Operation :=
  {
    selectionSet :=
      [
        .field "a" "answer" [] [.include (.variable "x")] [],
        .field "b" "answer" [] [.include (.variable "y")] []
      ]
  }

-- Independent siblings have a compatible assignment where both are selected.
theorem compatibleBooleanBranchesEstimateTwo
    : ExactCases.estimateOperation smokeSchema 10 compatibleBooleanBranchesOperation
      = 2 := by
  native_decide

theorem syntacticCompatibleBooleanBranchesEstimateTwo
    : GraphQL.TreeSummary.MaxResponseSize.Syntactic.estimateOperation
        smokeSchema 10 compatibleBooleanBranchesOperation
      = 2 := by
  native_decide

-- Supplying values refines both backends by pruning known-false branches.
theorem exactVariablesPruneCompatibleBooleanBranches
    : ExactCases.estimateOperationWithVariables smokeSchema 10
        [("x", .boolean false), ("y", .boolean false)]
        compatibleBooleanBranchesOperation
      = 0 := by
  native_decide

theorem syntacticVariablesPruneCompatibleBooleanBranches
    : GraphQL.TreeSummary.MaxResponseSize.Syntactic.estimateOperationWithVariables
        smokeSchema 10 [("x", .boolean false), ("y", .boolean false)]
        compatibleBooleanBranchesOperation
      = 0 := by
  native_decide

theorem syntacticSoundApiSmoke (schema : Schema) (listSize : Nat) (operation : Operation)
    : GraphQL.TreeSummary.MaxResponseSize.Syntactic.Sound schema listSize operation :=
  Syntactic.sound schema listSize operation

theorem syntacticSoundWithVariablesApiSmoke
    (schema : Schema) (listSize : Nat) (operation : Operation)
    : GraphQL.TreeSummary.MaxResponseSize.Syntactic.SoundWithVariables schema listSize
        operation :=
  Syntactic.soundWithVariables schema listSize operation

def selectedOutputSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [
                { name := "node", outputType := .named "Node" },
                { name := "nodes", outputType := .list (.named "Node") }
              ]
          },
        .object
          {
            name := "Node"
            fields := [{ name := "name", outputType := .named "String" }]
          }
      ]
  }

def selectedOutputOperation : Operation :=
  { selectionSet := [.field "node" "node" [] [] [.field "name" "name" [] [] []]] }

-- The unrelated list-returning `nodes` field must not multiply the child summary of
-- the selected singular `node` field.
theorem fieldOutputTypesUseSelectedFieldNames
    : ExactCases.estimateOperation selectedOutputSchema 10 selectedOutputOperation
      = 2 := by
  native_decide

def sharedNestedBooleanOperation : Operation :=
  {
    variableDefinitions :=
      [{ name := "x", typeRef := .named "Boolean", defaultValue := none }]
    selectionSet :=
      [
        .field "left" "node" [] []
          [.field "name" "name" [] [.include (.variable "x")] []],
        .field "right" "node" [] [] [.field "name" "name" [] [.skip (.variable "x")] []]
      ]
  }

-- One operation-level assignment is shared by both recursively summarized child
-- selections. The two nested fields are complementary, so no feasible case contains
-- both: the two root fields contribute two and at most one child contributes one.
theorem nestedSelectionsShareOneBooleanCase
    : ExactCases.estimateOperation selectedOutputSchema 10 sharedNestedBooleanOperation
      = 3 := by
  native_decide

theorem nestedSelectionsShareSuppliedBooleanValue
    : ExactCases.estimateOperationWithVariables selectedOutputSchema 10
          [("x", .boolean true)] sharedNestedBooleanOperation
        = 3
      ∧ ExactCases.estimateOperationWithVariables selectedOutputSchema 10
          [("x", .boolean false)] sharedNestedBooleanOperation
        = 3 := by
  native_decide

-- A missing nullable Boolean input behaves as false: `@include` rejects the left
-- nested field while `@skip` selects the right one.
theorem nestedSelectionsShareMissingBooleanValue
    : ExactCases.estimateOperationWithVariables selectedOutputSchema 10 []
        sharedNestedBooleanOperation
      = 3 := by
  native_decide

theorem summaryOptimalApiSmoke (schema : Schema) (listSize : Nat) (operation : Operation)
    : ExactCases.SummaryOptimal schema listSize operation :=
  ExactCases.summaryOptimal schema listSize operation

theorem summaryOptimalWithVariablesApiSmoke (schema : Schema) (listSize : Nat)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : ExactCases.SummaryOptimalWithVariables schema listSize variableValues operation :=
  ExactCases.summaryOptimalWithVariables schema listSize variableValues operation

end MaxResponseSize
end TreeSummary
end Tests
end GraphQL
