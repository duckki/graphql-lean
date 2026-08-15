import GraphQL.Theories.TreeSummary.ExactCases
import GraphQL.Theories.TreeSummary.Syntactic
import Tests.GraphQL.Theories.ConditionTree
import Tests.GraphQL.Theories.TreeSummary.AnnotationErasure
import Tests.GraphQL.Theories.TreeSummary.StaticCost
import Tests.GraphQL.Theories.TreeSummary.MaxResponseSize

namespace GraphQL
namespace Tests
namespace TreeSummary

open GraphQL.TreeSummary
open GraphQL.Tests.ConditionTree

def operationWithSelections (selectionSet : List Selection) : Operation :=
  {
    name := some "TreeSummarySmoke"
    selectionSet
  }

def animalsField (selectionSet : List Selection) : Selection :=
  .field "animals" "animals" [] [] selectionSet

theorem maxResponseSizeNestedSmoke
    : MaxResponseSize.ExactCases.estimateOperation conditionSchema 1
        (operationWithSelections [animalsField [nameSelection, idSelection]])
      = (3 : Nat) := by
  native_decide

def unrelatedListSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [{ name := "node", outputType := .named "Node" }]
          },
        .object
          {
            name := "Node"
            fields := [{ name := "name", outputType := .named "String" }]
          },
        .object
          {
            name := "Unrelated"
            fields :=
              [{ name := "large", outputType := .list (.list (.named "String")) }]
          }
      ]
  }

theorem unrelatedSchemaOutputsDoNotInflateSummarySmoke
    : MaxResponseSize.ExactCases.estimateOperation unrelatedListSchema 10
        (operationWithSelections
          [.field "node" "node" [] [] [.field "name" "name" [] [] []]])
      = 2 := by
  native_decide

theorem collectedResponseNameCountsOnceSmoke
    : MaxResponseSize.ExactCases.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField [.field "label" "name" [] [] [], .field "label" "name" [] [] []]])
      = (2 : Nat) := by
  native_decide

theorem sameResponseNameInCompatibleConditionsIsGloballyGroupedSmoke
    : ExactCases.summarizeSelectionSet (MaxResponseSize.algebra conditionSchema 1)
        conditionSchema "Animal" []
        [
          .field "label" "name" [] [] [],
          .inlineFragment (some "Dog") [] [.field "label" "id" [] [] []]
        ]
        ExactCases.BooleanEnvironment.unknown
      = (1 : Nat) := by
  native_decide

-- The structural backend visits both syntactic response-name groups independently.
-- For response-size counting this produces the expected less precise result.
theorem syntacticSameResponseNameKeepsSeparateContributionsSmoke
    : Syntactic.summarizeSelectionSet (MaxResponseSize.algebra conditionSchema 1)
        conditionSchema "Animal" []
        [
          .field "label" "name" [] [] [],
          .inlineFragment (some "Dog") [] [.field "label" "id" [] [] []]
        ]
      = (2 : Nat) := by
  native_decide

def repeatedConditionalResponseNameTree : ConditionTree.Tree :=
  ConditionTree.ofSelectionSet conditionSchema "Animal"
    [
      .field "label" "name" [] [.include (.variable "x")] [],
      .field "label" "name" [] [.include (.variable "y")] []
    ]

-- One feasible exact case globally merges matching response names before analysis.
theorem repeatedConditionalResponseNameCaseIsGloballyGrouped
    : let conditionTree := repeatedConditionalResponseNameTree
      let caseForest :=
        (ExactCases.CaseForest.ofConditionTree conditionTree).resolveBranches
          conditionTree.condition.possibleTypes
          [("x", .boolean true), ("y", .boolean true)]
      (caseForest.fieldGroups [.positive "x", .positive "y"]
        conditionTree.condition.possibleTypes).map
        (fun group => (group.responseName, group.fields.length))
      = [("label", 2)] := by
  native_decide

theorem exactCasesCountRepeatedConditionalResponseNameOnce
    : ExactCases.summarizeConditionTree
        (MaxResponseSize.algebra conditionSchema 1) conditionSchema "Animal" []
        repeatedConditionalResponseNameTree
        ExactCases.BooleanEnvironment.unknown
      = (1 : Nat) := by
  native_decide

theorem syntacticSummaryCountsRepeatedConditionalResponseNameTwice
    : Syntactic.summarizeConditionTree
        (MaxResponseSize.algebra conditionSchema 1) conditionSchema "Animal" []
        repeatedConditionalResponseNameTree []
      = (2 : Nat) := by
  native_decide

def nestedConditionalResponseNameTree : ConditionTree.Tree :=
  ConditionTree.ofSelectionSet conditionSchema "Animal"
    [
      .field "label" "name" [] [] [],
      .inlineFragment none [.include (.variable "x")]
        [.field "label" "id" [] [.include (.variable "y")] []]
    ]

-- Selecting `x` creates a case forest containing the retained root and the
-- selected condition-tree subtree. Its nested `y` condition remains a local frontier,
-- so the analysis re-enters that forest before globally grouping the two
-- `label` fields.
theorem nestedConditionCompositionRecursesOnCaseForest
    : let conditionTree := nestedConditionalResponseNameTree
      let scope := conditionTree.condition.possibleTypes
      let initial := ExactCases.CaseForest.ofConditionTree conditionTree
      let afterX := initial.resolveBranches scope [("x", .boolean true)]
      let afterY :=
        afterX.resolveBranches scope [("y", .boolean true), ("x", .boolean true)]
      (
        afterX.hasUnresolvedBranches,
        afterY.hasUnresolvedBranches,
        (afterY.fieldGroups [.positive "x", .positive "y"] scope).map
          (fun group => (group.responseName, group.fields.length))
      )
      = (true, false, [("label", 2)]) := by
  native_decide

theorem nestedConditionCompositionCountsResponseNameOnce
    : ExactCases.summarizeConditionTree
        (MaxResponseSize.algebra conditionSchema 1) conditionSchema "Animal" []
        nestedConditionalResponseNameTree
        ExactCases.BooleanEnvironment.unknown
      = (1 : Nat) := by
  native_decide

abbrev collectedCaseSizesAlgebra : Algebra :=
  {
    Summary := List Nat
    empty := [0]
    field := fun _group _children => [1]
    combine := fun left right => left.flatMap fun l => right.map fun r => l + r
    join := List.append
  }

def complementaryConditionalFieldsTree : ConditionTree.Tree :=
  ConditionTree.ofSelectionSet conditionSchema "Animal"
    [
      .field "included" "name" [] [.include (.variable "x")] [],
      .field "skipped" "id" [] [.skip (.variable "x")] []
    ]

-- Missing nullable Booleans behave as false. Missing, supplied false, and supplied true
-- therefore each select exactly one polarity, producing three cases of size one.
theorem unresolvedBooleanIsASeparateCase
    : ExactCases.summarizeConditionTree collectedCaseSizesAlgebra conditionSchema
        "Animal" [] complementaryConditionalFieldsTree
        ExactCases.BooleanEnvironment.unknown
      = [1, 1, 1] := by
  native_decide

-- Immediate branches with opposite literals of one variable are simultaneous only
-- within their matching value; the syntactic backend combines each side and joins the
-- two alternatives without enumerating assignments.
theorem syntacticComplementaryBooleanBranchesJoinSmoke
    : Syntactic.summarizeConditionTree collectedCaseSizesAlgebra conditionSchema
        "Animal" [] complementaryConditionalFieldsTree []
      = [1, 1] := by
  native_decide

theorem lazyBooleanDecisionSplitsOnlyWhenReached
    : let variables := ["x"]
      let environment : ExactCases.BooleanEnvironment :=
        {
          statuses := [("x", .unresolved)]
          variableValues := []
          fixedVariableValues := []
        }
      let decision :=
        ExactCases.summarizeConditionTreeDecision collectedCaseSizesAlgebra
          conditionSchema "Animal" [] complementaryConditionalFieldsTree variables
          environment
      (decision.nodeCount, decision.collapse collectedCaseSizesAlgebra)
      = (3, [1, 1]) := by
  native_decide

theorem explicitMissingBooleanContextSelectsNegativePolarity
    : ExactCases.summarizeConditionTree collectedCaseSizesAlgebra
        conditionSchema "Animal" [] complementaryConditionalFieldsTree
        {
          statuses := [("x", .missing)]
          variableValues := []
          fixedVariableValues := []
        }
      = [1] := by
  native_decide

theorem explicitKnownBooleanContextSelectsOnePolarity
    : ExactCases.summarizeConditionTree collectedCaseSizesAlgebra
        conditionSchema "Animal" [] complementaryConditionalFieldsTree
        {
          statuses := [("x", .known false)]
          variableValues := [("x", .boolean false)]
          fixedVariableValues := [("x", .boolean false)]
        }
      = [1] := by
  native_decide

theorem summarizeSelectionSetUsesInheritedBooleanConditionSmoke
    : ExactCases.summarizeSelectionSet (MaxResponseSize.algebra conditionSchema 1)
        conditionSchema "Animal"
        [.positive "x"]
        [
          .field "excluded" "name" [] [.skip (.variable "x")] [],
          .field "included" "id" [] [] []
        ]
        ExactCases.BooleanEnvironment.unknown
      = (1 : Nat) := by
  native_decide

theorem conditionBranchJoinsSkippedAndTakenSmoke
    : MaxResponseSize.ExactCases.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField [nameSelection, .inlineFragment (some "Dog") [] [idSelection]]])
      = (3 : Nat) := by
  native_decide

-- Distinct object-type siblings cannot occur for the same runtime object and are
-- therefore joined, not added.
theorem disjointObjectTypeBranchesJoinSmoke
    : MaxResponseSize.ExactCases.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField
            [
              .inlineFragment (some "Dog") [] [nameSelection],
              .inlineFragment (some "Cat") [] [idSelection]
            ]])
      = (2 : Nat) := by
  native_decide

-- Overlapping abstract-type siblings have a concrete `Dog` case where both branches
-- apply, so that compatible combination is composed before alternatives are joined.
theorem overlappingInterfaceTypeBranchesCombineSmoke
    : MaxResponseSize.ExactCases.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField
            [
              .inlineFragment (some "I") [] [nameSelection],
              .inlineFragment (some "J") [] [idSelection]
            ]])
      = (3 : Nat) := by
  native_decide

-- The syntactic backend reuses each branch summary, then combines the two summaries
-- for the concrete `Dog` case where both interface conditions hold.
theorem syntacticOverlappingInterfaceTypeBranchesCombineSmoke
    : MaxResponseSize.Syntactic.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField
            [
              .inlineFragment (some "I") [] [nameSelection],
              .inlineFragment (some "J") [] [idSelection]
            ]])
      = (3 : Nat) := by
  native_decide

def repeatedTypeActivationBranches
    : List (Syntactic.TypeBranchSummary collectedCaseSizesAlgebra.Summary) :=
  [{ possibleTypes := ["Dog", "Cat"], summary := [1] }]

-- `Dog` and `Cat` activate the same immediate branch product. The symbolic region
-- traversal evaluates that materializable product once; `Fox` forms the inactive region
-- and therefore contributes no alternative.
theorem syntacticTypeCasesEnumerateMaterializableProductsOnce
    : Syntactic.typeBranchRegions
          (conditionSchema.getPossibleTypes "Animal") repeatedTypeActivationBranches
        = [["Dog", "Cat"], ["Fox"]]
      ∧ Syntactic.typeRuntimeCaseSummaries collectedCaseSizesAlgebra
          (conditionSchema.getPossibleTypes "Animal") repeatedTypeActivationBranches
        = [[1]]
      ∧ Syntactic.summarizeTypeRuntimeCases collectedCaseSizesAlgebra
          (conditionSchema.getPossibleTypes "Animal") repeatedTypeActivationBranches
        = [1] := by
  native_decide

def mixedImmediateBranchTree : ConditionTree.Tree :=
  ConditionTree.ofSelectionSet conditionSchema "Animal"
    [
      .inlineFragment (some "Dog") [] [nameSelection],
      .inlineFragment none [.include (.variable "x")] [idSelection]
    ]

-- The compact node scan places each immediate branch in exactly one family. Known-false
-- Boolean branches and type branches outside the inherited scope are omitted eagerly.
theorem syntacticImmediateBranchesArePartitionedInOnePass
    : let tree := mixedImmediateBranchTree
      let all :=
        Syntactic.summarizeImmediateBranches collectedCaseSizesAlgebra conditionSchema
          "Animal" [] tree.branches [] tree.condition.possibleTypes
      let knownFalse :=
        Syntactic.summarizeImmediateBranches collectedCaseSizesAlgebra conditionSchema
          "Animal" [] tree.branches [("x", .boolean false)]
          tree.condition.possibleTypes
      let narrowed :=
        Syntactic.summarizeImmediateBranches collectedCaseSizesAlgebra conditionSchema
          "Animal" [] tree.branches [] ["Cat"]
      (all.typeBranches.length, all.booleanBranches.length) = (1, 1)
      ∧ (knownFalse.typeBranches.length, knownFalse.booleanBranches.length) = (1, 0)
      ∧ (narrowed.typeBranches.length, narrowed.booleanBranches.length) = (0, 1) := by
  native_decide

-- No runtime object activates both concrete object branches, so their summaries remain
-- alternatives in the symbolic type-region evaluator.
theorem syntacticDisjointObjectTypeBranchesJoinSmoke
    : MaxResponseSize.Syntactic.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField
            [
              .inlineFragment (some "Dog") [] [nameSelection],
              .inlineFragment (some "Cat") [] [idSelection]
            ]])
      = (2 : Nat) := by
  native_decide

-- The exact runtime cases include executions in which both the type and Boolean
-- conditions hold, so both response fields can occur simultaneously.
theorem typeAndBooleanBranchesTraverseSeparatelySmoke
    : MaxResponseSize.ExactCases.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField
            [
              .inlineFragment (some "I") [] [nameSelection],
              .inlineFragment none [.include (.variable "x")] [idSelection]
            ]])
      = (3 : Nat) := by
  native_decide

-- Entering `I` starts a new local node analysis, where `Dog` is then considered under
-- the already-narrowed `I` scope.
theorem nestedTypeConditionUsesInheritedScopeSmoke
    : MaxResponseSize.ExactCases.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField
            [.inlineFragment (some "I") []
              [nameSelection, .inlineFragment (some "Dog") [] [idSelection]]]])
      = (3 : Nat) := by
  native_decide

-- The `Cat` branch and the `Dog` branch below its Boolean sibling cannot describe one
-- runtime object. Passing the `Cat` case into the Boolean child prevents their sizes
-- from being combined.
theorem disjointTypeConditionsAcrossBooleanEdgeDoNotCombineSmoke
    : MaxResponseSize.ExactCases.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField
            [
              .inlineFragment (some "Cat") [] [nameSelection],
              .inlineFragment none [.include (.variable "x")]
                [.inlineFragment (some "Dog") [] [idSelection]]
            ]])
      = (2 : Nat) := by
  native_decide

-- The inherited `I` case still overlaps `J` below the selected Boolean sibling on
-- `Dog`, so the compatible contributions are combined.
theorem overlappingTypeConditionsAcrossBooleanEdgeCombineSmoke
    : MaxResponseSize.ExactCases.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField
            [
              .inlineFragment (some "I") [] [nameSelection],
              .inlineFragment none [.include (.variable "x")]
                [.inlineFragment (some "J") [] [idSelection]]
            ]])
      = (3 : Nat) := by
  native_decide

-- The assignment selected for `x` at the parent is inherited by its child. The nested
-- complementary edge is therefore unreachable and cannot be combined with `name`.
theorem nestedBooleanCaseInheritsParentAssignmentSmoke
    : MaxResponseSize.ExactCases.estimateOperation conditionSchema 1
        (operationWithSelections
          [animalsField
            [.inlineFragment none [.include (.variable "x")]
              [
                nameSelection,
                .inlineFragment none [.skip (.variable "x")] [idSelection]
              ]]])
      = (2 : Nat) := by
  native_decide

def bottomUpTraceAlgebra : Algebra :=
  {
    Summary := List Name
    empty := []
    field := fun group child => child ++ [group.responseName]
    combine := List.append
    join := fun left _right => left
  }

def bottomUpTrace (schema : Schema) (operation : Operation) : List Name :=
  ExactCases.summarizeOperation bottomUpTraceAlgebra schema operation

theorem childStateReachesParentFieldHandlerSmoke
    : bottomUpTrace conditionSchema
        (operationWithSelections [animalsField [nameSelection]])
      = ["name", "animals"] := by
  native_decide

def variableIncludeOperation (defaultValue : Option ConstInputValue) : Operation :=
  {
    name := some "VariableAwareTreeSummary"
    variableDefinitions :=
      [{
        name := "showName"
        typeRef := .named "Boolean"
        defaultValue
      }]
    selectionSet :=
      [animalsField
        [.inlineFragment none [.include (.variable "showName")] [nameSelection]]]
  }

def variableSkipOperation (defaultValue : Option ConstInputValue) : Operation :=
  {
    name := some "VariableAwareTreeSummary"
    variableDefinitions :=
      [{
        name := "skipName"
        typeRef := .named "Boolean"
        defaultValue
      }]
    selectionSet :=
      [animalsField [.inlineFragment none [.skip (.variable "skipName")] [nameSelection]]]
  }

theorem suppliedTrueTakesBooleanBranchSmoke
    : ExactCases.summarizeOperationWithVariables
        (fun _variableValues => MaxResponseSize.algebra conditionSchema 1)
        conditionSchema
        [("showName", .boolean true)] (variableIncludeOperation none)
      = 2 := by
  native_decide

theorem suppliedFalseSkipsBooleanBranchSmoke
    : ExactCases.summarizeOperationWithVariables
        (fun _variableValues => MaxResponseSize.algebra conditionSchema 1)
        conditionSchema
        [("showName", .boolean false)] (variableIncludeOperation none)
      = 1 := by
  native_decide

theorem operationVariableDefaultTakesBooleanBranchSmoke
    : ExactCases.summarizeOperationWithVariables
        (fun _variableValues => MaxResponseSize.algebra conditionSchema 1)
        conditionSchema []
        (variableIncludeOperation (some (.boolean true)))
      = 2 := by
  native_decide

theorem suppliedValueOverridesOperationVariableDefaultSmoke
    : ExactCases.summarizeOperationWithVariables
        (fun _variableValues => MaxResponseSize.algebra conditionSchema 1)
        conditionSchema
        [("showName", .boolean false)]
        (variableIncludeOperation (some (.boolean true)))
      = 1 := by
  native_decide

theorem negativeLiteralUsesOperationVariableDefaultSmoke
    : ExactCases.summarizeOperationWithVariables
        (fun _variableValues => MaxResponseSize.algebra conditionSchema 1)
        conditionSchema []
        (variableSkipOperation (some (.boolean true)))
      = 1 := by
  native_decide

theorem syntacticSuppliedFalseSkipsBooleanBranchSmoke
    : Syntactic.summarizeOperationWithVariables
        (fun _variableValues => MaxResponseSize.algebra conditionSchema 1)
        conditionSchema [("showName", .boolean false)] (variableIncludeOperation none)
      = 1 := by
  native_decide

theorem syntacticOperationDefaultTakesBooleanBranchSmoke
    : Syntactic.summarizeOperationWithVariables
        (fun _variableValues => MaxResponseSize.algebra conditionSchema 1)
        conditionSchema [] (variableIncludeOperation (some (.boolean true)))
      = 2 := by
  native_decide

abbrev visitedResponseNamesAlgebra : Algebra :=
  {
    Summary := List Name
    empty := []
    field := fun group children => group.responseName :: children
    combine := List.append
    join := List.append
  }

def conditionallyVisitedNameSelection : List Selection :=
  [.field "name" "name" [] [.include (.variable "showName")] []]

-- Backend summaries expose that known-false pruning makes the field handler unreachable.
-- The known-true case deliberately retains and visits the condition edge.
theorem knownFalsePruningSkipsFieldHandlersSmoke
    : ExactCases.summarizeSelectionSet visitedResponseNamesAlgebra conditionSchema
          "Animal" [] conditionallyVisitedNameSelection
          (ExactCases.BooleanEnvironment.ofCompleteValues ["showName"]
            [("showName", .boolean false)])
        = []
      ∧ ExactCases.summarizeSelectionSet visitedResponseNamesAlgebra conditionSchema
          "Animal" [] conditionallyVisitedNameSelection
          (ExactCases.BooleanEnvironment.ofCompleteValues ["showName"]
            [("showName", .boolean true)])
        = ["name"]
      ∧ Syntactic.summarizeSelectionSet visitedResponseNamesAlgebra conditionSchema
          "Animal" [] conditionallyVisitedNameSelection [("showName", .boolean false)]
        = []
      ∧ Syntactic.summarizeSelectionSet visitedResponseNamesAlgebra conditionSchema
          "Animal" [] conditionallyVisitedNameSelection [("showName", .boolean true)]
        = ["name"] := by
  native_decide

end TreeSummary
end Tests
end GraphQL
