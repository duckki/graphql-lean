import Proofs.GraphQL.Theories.ConditionTree.Execution
import Proofs.GraphQL.Theories.ConditionTree.ExecutionEquivalence
import Proofs.GraphQL.Theories.ConditionTree.Reduce
import Proofs.GraphQL.Theories.ConditionTree.Soundness

namespace GraphQL
namespace Tests
namespace ConditionTree

open GraphQL.ConditionTree

def stringField (name : Name) : FieldDefinition :=
  { name, outputType := .named "String" }

def conditionSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [{ name := "animals", outputType := .named "Animal" }]
          },
        .interface
          {
            name := "Animal"
            fields := [stringField "name", stringField "id"]
          },
        .interface
          {
            name := "I"
            fields := [stringField "name", stringField "id"]
          },
        .interface
          {
            name := "J"
            fields := [stringField "name", stringField "id"]
          },
        .interface
          {
            name := "K"
            fields := [stringField "name", stringField "id"]
          },
        .object
          {
            name := "Dog"
            fields := [stringField "name", stringField "id"]
            interfaces := ["Animal", "I", "J", "K"]
          },
        .object
          {
            name := "Cat"
            fields := [stringField "name", stringField "id"]
            interfaces := ["Animal", "I", "K"]
          },
        .object
          {
            name := "Fox"
            fields := [stringField "name", stringField "id"]
            interfaces := ["Animal", "J"]
          }
      ]
  }

def nameSelection : Selection :=
  .field "name" "name" [] [] []

def idSelection : Selection :=
  .field "id" "id" [] [] []

def equivalentSourceConditionTree : Tree :=
  ofSelectionSet conditionSchema "Animal"
    [
      .inlineFragment (some "I") [] [.inlineFragment (some "J") [] [nameSelection]],
      .inlineFragment (some "J") [] [.inlineFragment (some "K") [] [idSelection]]
    ]

theorem equivalentConditionsShareOnePathSmoke
    : equivalentSourceConditionTree.branches.length = 1
      ∧ (equivalentSourceConditionTree.branches.map
          fun branch => branch.body.branches.length)
        = [0]
      ∧ (equivalentSourceConditionTree.branches.map fun branch => branch.condition)
        = [.typeCondition "Dog"] := by
  native_decide

theorem equivalentConditionsMergeFieldsSmoke
    : (equivalentSourceConditionTree.branches.flatMap
        fun branch => branch.body.fields.map FieldGroup.responseName)
      = ["name", "id"] := by
  native_decide

def abstractThenObjectConditionTree : Tree :=
  ofSelectionSet conditionSchema "Animal"
    [
      .inlineFragment (some "I") [] [.inlineFragment (some "J") [] [nameSelection]],
      .inlineFragment (some "Dog") [] [idSelection]
    ]

def objectThenAbstractConditionTree : Tree :=
  ofSelectionSet conditionSchema "Animal"
    [
      .inlineFragment (some "Dog") [] [nameSelection],
      .inlineFragment (some "I") [] [.inlineFragment (some "J") [] [idSelection]]
    ]

def singletonObjectBranchResponseNames (tree : Tree) : List Name :=
  tree.branches.flatMap
    fun branch =>
      branch.body.fields.map FieldGroup.responseName

theorem abstractThenObjectMergesAtObjectNodeSmoke
    : (abstractThenObjectConditionTree.branches.map fun branch => branch.condition)
        = [.typeCondition "Dog"]
      ∧ singletonObjectBranchResponseNames abstractThenObjectConditionTree
        = ["name", "id"] := by
  native_decide

theorem objectThenAbstractMergesAtObjectNodeSmoke
    : (objectThenAbstractConditionTree.branches.map fun branch => branch.condition)
        = [.typeCondition "Dog"]
      ∧ singletonObjectBranchResponseNames objectThenAbstractConditionTree
        = ["name", "id"] := by
  native_decide

def redundantParentConditionTree : Tree :=
  ofSelectionSet conditionSchema "Animal"
    [.inlineFragment (some "Animal") [] [.inlineFragment (some "Dog") [] [nameSelection]]]

theorem redundantParentConditionIsRemovedSmoke
    : (redundantParentConditionTree.branches.map fun branch => branch.condition)
      = [.typeCondition "Dog"] := by
  native_decide

def canonicalBooleanTree : Tree :=
  ofSelectionSet conditionSchema "Animal"
    [.inlineFragment none
      [.skip (.variable "y"), .include (.variable "x")]
      [nameSelection]]

theorem booleanConditionIsCanonicalSmoke
    : (canonicalBooleanTree.branches.flatMap
        fun branch =>
          branch.body.branches.map fun nested => nested.body.condition.booleanCondition)
      = [[.positive "x", .negative "y"]] := by
  native_decide

def compoundInlineConditionTree : Tree :=
  ofSelectionSet conditionSchema "Animal"
    [.inlineFragment (some "Dog")
      [.skip (.variable "y"), .include (.variable "x")]
      [nameSelection]]

def branchConditionsAtDepth : Nat -> Tree -> List BranchCondition
  | 0, _tree => []
  | depth + 1, tree =>
      if depth = 0 then
        tree.branches.map fun branch => branch.condition
      else
        tree.branches.flatMap fun branch => branchConditionsAtDepth depth branch.body

theorem compoundInlineConditionHasDeterministicBranchesSmoke
    : branchConditionsAtDepth 1 compoundInlineConditionTree = [.typeCondition "Dog"]
      ∧ branchConditionsAtDepth 2 compoundInlineConditionTree
        = [.booleanLiteral (.negative "y")]
      ∧ branchConditionsAtDepth 3 compoundInlineConditionTree
        = [.booleanLiteral (.positive "x")] := by
  native_decide

def fieldDirectiveTree : Tree :=
  ofSelectionSet conditionSchema "Animal"
    [.field "name" "name" [] [.skip (.variable "y"), .include (.variable "x")] []]

theorem fieldDirectivesBecomeDeterministicBranchesSmoke
    : branchConditionsAtDepth 1 fieldDirectiveTree = [.booleanLiteral (.negative "y")]
      ∧ branchConditionsAtDepth 2 fieldDirectiveTree
        = [.booleanLiteral (.positive "x")] := by
  native_decide

def fieldDirectiveLeafSelections : List Selection :=
  fieldDirectiveTree.branches.flatMap
    fun branch =>
      branch.body.branches.flatMap
        fun nested =>
          nested.body.fields.flatMap FieldGroup.selections

def retainedFieldHasNoDirectives : Bool :=
  match fieldDirectiveLeafSelections with
  | [.field responseName fieldName arguments directives selectionSet] =>
      responseName == "name"
      && fieldName == "name"
      && arguments.isEmpty
      && directives.isEmpty
      && selectionSet.isEmpty
  | _ => false

theorem retainedFieldHasNoDirectivesSmoke : retainedFieldHasNoDirectives = true := by
  native_decide

theorem fieldDirectiveTreeWellFormedSmoke
    : fieldDirectiveTree.WellFormed conditionSchema [] := by
  apply ofSelectionSetInScope_wellFormed conditionSchema "Animal" []
  · native_decide
  · native_decide

def fieldDirectiveRuntimeResponseNames (variableValues : Execution.VariableValues)
    : List Name :=
  (fieldDirectiveTree.collectRuntimeFields variableValues "Animal" "Dog").map
    fun field => field.responseName

theorem fieldDirectiveBranchesControlExecutionSmoke
    : fieldDirectiveRuntimeResponseNames [("x", .boolean true), ("y", .boolean false)]
        = ["name"]
      ∧ fieldDirectiveRuntimeResponseNames [("x", .boolean false), ("y", .boolean false)]
        = []
      ∧ fieldDirectiveRuntimeResponseNames [("x", .boolean true), ("y", .boolean true)]
        = [] := by
  native_decide

def knownFalsePrunedIncludedFieldTree (variableValues : Execution.VariableValues)
    : Tree :=
  ofSelectionSetInScopeWithKnownFalsePruning conditionSchema "Animal" [] variableValues
    [.field "name" "name" [] [.include (.variable "x")] []]

def knownFalsePrunedSkippedFieldTree (variableValues : Execution.VariableValues) : Tree :=
  ofSelectionSetInScopeWithKnownFalsePruning conditionSchema "Animal" [] variableValues
    [.field "name" "name" [] [.skip (.variable "x")] []]

theorem knownFalseIncludeIsPrunedSmoke
    : let tree := knownFalsePrunedIncludedFieldTree [("x", .boolean false)]
      tree.fields = [] ∧ tree.branches = [] := by
  native_decide

-- A known-active directive deliberately remains an edge. Removing it would change
-- response-name grouping and can change summaries for non-idempotent algebras.
theorem knownTrueIncludeEdgeIsRetainedSmoke
    : (knownFalsePrunedIncludedFieldTree [("x", .boolean true)]).branches.map
        (fun branch => branch.condition)
      = [.booleanLiteral (.positive "x")] := by
  native_decide

theorem missingIncludeEdgeIsRetainedSmoke
    : (knownFalsePrunedIncludedFieldTree []).branches.map (fun branch => branch.condition)
      = [.booleanLiteral (.positive "x")] := by
  native_decide

theorem knownTrueSkipIsPrunedSmoke
    : let tree := knownFalsePrunedSkippedFieldTree [("x", .boolean true)]
      tree.fields = [] ∧ tree.branches = [] := by
  native_decide

theorem knownFalseSkipEdgeIsRetainedSmoke
    : (knownFalsePrunedSkippedFieldTree [("x", .boolean false)]).branches.map
        (fun branch => branch.condition)
      = [.booleanLiteral (.negative "x")] := by
  native_decide

def knownFalsePrunedInlineTree (variableValues : Execution.VariableValues) : Tree :=
  ofSelectionSetInScopeWithKnownFalsePruning conditionSchema "Animal" [] variableValues
    [.inlineFragment (some "Dog") [.include (.variable "x")] [nameSelection]]

theorem knownFalseInlineFragmentSubtreeIsPrunedSmoke
    : (knownFalsePrunedInlineTree [("x", .boolean false)]).branches = [] := by
  native_decide

def knownFalsePrunedNestedTree (variableValues : Execution.VariableValues) : Tree :=
  ofSelectionSetInScopeWithKnownFalsePruning conditionSchema "Query" [] variableValues
    [.field "animals" "animals" [] []
      [.field "name" "name" [] [.include (.variable "x")] []]]

def knownFalsePrunedNestedChildBranches (variableValues : Execution.VariableValues)
    : List BranchCondition :=
  match (knownFalsePrunedNestedTree variableValues).fields with
  | [group] =>
      (ofSelectionSetInScopeWithKnownFalsePruning conditionSchema "Animal" []
        variableValues group.mergedSelectionSet).branches.map
        fun branch => branch.condition
  | _groups => []

def knownFalsePrunedNestedChildShape (variableValues : Execution.VariableValues)
    : Nat × Nat :=
  match (knownFalsePrunedNestedTree variableValues).fields with
  | [group] =>
      let childTree :=
        ofSelectionSetInScopeWithKnownFalsePruning conditionSchema "Animal" []
          variableValues group.mergedSelectionSet
      (childTree.fields.length, childTree.branches.length)
  | _groups => (0, 0)

theorem nestedSelectionSetUsesKnownFalsePruningSmoke
    : knownFalsePrunedNestedChildBranches [("x", .boolean false)] = []
      ∧ knownFalsePrunedNestedChildBranches [("x", .boolean true)]
        = [.booleanLiteral (.positive "x")] := by
  native_decide

-- A known-inactive child is absent structurally, while a known-active directive remains
-- an explicit edge for response-name grouping and non-idempotent summary algebras.
theorem nestedKnownFalsePruningShapeSmoke
    : knownFalsePrunedNestedChildShape [("x", .boolean false)] = (0, 0)
      ∧ knownFalsePrunedNestedChildShape [("x", .boolean true)] = (0, 1) := by
  native_decide

def knownFalsePruningDefaultOperation : Operation :=
  {
    variableDefinitions :=
      [{
        name := "x"
        typeRef := .named "Boolean"
        defaultValue := some (.boolean false)
      }]
    selectionSet :=
      [.field "animals" "animals" [] [.include (.variable "x")] []]
  }

theorem operationDefaultsParticipateInKnownFalsePruningSmoke
    : let operation := knownFalsePruningDefaultOperation
      let variableValues := Execution.coerceVariableValues operation []
      let tree :=
        ofSelectionSetInScopeWithKnownFalsePruning conditionSchema
          (operation.rootType conditionSchema) [] variableValues operation.selectionSet
      tree.fields = [] ∧ tree.branches = [] := by
  native_decide

def repeatedResponseNameTree : Tree :=
  ofSelectionSet conditionSchema "Animal"
    [.field "label" "name" [] [] [], .field "label" "id" [] [] []]

theorem fieldsAreCollectedByUniqueResponseNameSmoke
    : repeatedResponseNameTree.fields.map FieldGroup.responseName = ["label"]
      ∧ repeatedResponseNameTree.fields.map (fun group => group.selections.length)
        = [2] := by
  native_decide

def parentChildRepeatedResponseNameTree : Tree :=
  ofSelectionSet conditionSchema "Animal"
    [
      .field "label" "name" [] [] [],
      .inlineFragment (some "Dog") [] [.field "label" "id" [] [] []]
    ]

-- The parent occurrence fixes the group's position. The matching child occurrence is
-- merged into that group rather than becoming a second executable visit.
theorem parentResponseNameIsExcludedFromChildGroupsSmoke
    : let groups :=
        parentChildRepeatedResponseNameTree.collectRuntimeFieldGroups [] "Animal" "Dog"
      groups.map Prod.fst = ["label"]
      ∧ groups.map (fun group => group.2.length) = [2] := by
  native_decide

def conditionTreeResolvers : Execution.Resolvers Unit :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        if parentType == "Query" && fieldName == "animals" then
          some (.object "Dog" ())
        else if parentType == "Dog" && fieldName == "name" then
          some (.scalar "Fido")
        else if parentType == "Dog" && fieldName == "id" then
          some (.scalar "dog-1")
        else
          none
    resolve_argumentsEquivalent := by
      intro parentType fieldName firstArguments laterArguments source _hequivalent
      rfl
  }

def nestedTreeOperation : Operation :=
  {
    selectionSet :=
      [.field "animals" "animals" [] [] [.field "name" "name" [] [] []]]
  }

def nestedTreeExecutionHasExpectedShape : Bool :=
  let response :=
    executeQuery conditionSchema conditionTreeResolvers [] nestedTreeOperation
      (.object "Query" ())
  response.errors == 0
  && match response.data with
      | .object [(animalsName, .object [(nameName, .scalar value)])] =>
          animalsName == "animals" && nameName == "name" && value == "Fido"
      | _ => false

theorem executeAcceptsSelectionSetSmoke
    : Execution.selectionSetResultToResponse
        (executeSelectionSet conditionSchema conditionTreeResolvers []
          "Query" "Query" "Query" (.object "Query" ())
          nestedTreeOperation.selectionSet)
      = executeQuery conditionSchema conditionTreeResolvers []
          nestedTreeOperation (.object "Query" ()) := by
  rfl

-- Nested object completion re-enters `executeSelectionSet` with the merged child
-- selection set; it does not delegate to the fuel-bounded specification executor.
theorem nestedTreeExecutionIsRecursiveAndFuelFreeSmoke
    : nestedTreeExecutionHasExpectedShape = true := by
  native_decide

def inheritedLiteralTree : Tree :=
  ofSelectionSetInScope conditionSchema "Animal" [.positive "x"]
    [
      .inlineFragment none [.include (.variable "x")] [nameSelection],
      .inlineFragment none [.skip (.variable "x")] [idSelection]
    ]

theorem inheritedLiteralIsNotRepeatedSmoke
    : inheritedLiteralTree.fields.map FieldGroup.responseName = ["name"]
      ∧ inheritedLiteralTree.branches.length = 0 := by
  native_decide

theorem inheritedLiteralTreeWellFormedSmoke
    : inheritedLiteralTree.WellFormed conditionSchema [.positive "x"] := by
  apply ofSelectionSetInScope_wellFormed conditionSchema "Animal"
    [.positive "x"]
  · native_decide
  · native_decide

def fieldConditionFeasibilityTree : Tree :=
  ofSelectionSetInScope conditionSchema "Animal" [.positive "x"]
    [.inlineFragment none [.include (.variable "y")]
      [
        .field "inheritedConflict" "name" [] [.skip (.variable "x")] [],
        .field "nodeConflict" "id" [] [.skip (.variable "y")] [],
        .field "kept" "name" [] [.include (.variable "x"), .include (.variable "y")] []
      ]]

theorem infeasibleFieldConditionsAreOmittedSmoke
    : (fieldConditionFeasibilityTree.branches.flatMap
        fun branch => branch.body.fields.map FieldGroup.responseName)
      = ["kept"] := by
  native_decide

theorem fieldConditionFeasibilityTreeWellFormedSmoke
    : fieldConditionFeasibilityTree.WellFormed conditionSchema [.positive "x"] := by
  apply ofSelectionSetInScope_wellFormed conditionSchema "Animal"
    [.positive "x"]
  · native_decide
  · native_decide

theorem extractionCorrectApiSmoke
    : ExtractionCorrect conditionSchema "Animal" []
        [nameSelection, .inlineFragment (some "Dog") [] [idSelection]] :=
  extraction_correct conditionSchema "Animal" [] _

theorem extractionSoundnessApiSmoke
    : ExtractionSound conditionSchema "Animal" []
        [
          nameSelection,
          .inlineFragment (some "Dog") [.include (.variable "x")] [idSelection]
        ] :=
  extraction_sound conditionSchema "Animal" [] _

theorem extractionGroupsEquivalentApiSmoke
    : ExtractionGroupsEquivalent conditionSchema "Animal" []
        [
          nameSelection,
          .inlineFragment (some "Dog") [.include (.variable "x")] [idSelection]
        ] :=
  extraction_groups_equivalent conditionSchema "Animal" [] _

theorem executionEquivalentApiSmoke
    : ExecutionEquivalent conditionSchema nestedTreeOperation :=
  ExecutionEquivalence.execution_equivalent conditionSchema nestedTreeOperation

theorem executionEquivalentAtFuelApiSmoke
    : ExecutionEquivalentAtFuel conditionSchema nestedTreeOperation
        (GraphQL.Execution.executeQueryFuelBound conditionSchema nestedTreeOperation) :=
  ExecutionEquivalence.execution_equivalent_of_sufficient_fuel conditionSchema
    nestedTreeOperation
    (GraphQL.Execution.executeQueryFuelBound conditionSchema nestedTreeOperation)
    (GraphQL.Execution.doesNotExhaustFuel conditionSchema nestedTreeOperation)

def reductionSourceOperation : Operation :=
  {
    selectionSet :=
      [.field "animals" "animals" [] []
        [
          nameSelection,
          .inlineFragment (some "Dog") [.include (.variable "x")] [idSelection]
        ]]
  }

def reducedOperation : Operation :=
  reduceOperation conditionSchema reductionSourceOperation

theorem reduceOperationUsesSelectionSetReduce
    : reducedOperation.selectionSet
      = reduce conditionSchema "Query" reductionSourceOperation.selectionSet :=
  rfl

def reductionHasExpectedShape : Bool :=
  match reducedOperation.selectionSet with
  | [.field responseName fieldName [] []
      [
        .field childResponseName childFieldName [] [] [],
        .inlineFragment (some typeCondition) []
          [.inlineFragment none [.include (.variable variableName)]
            [.field nestedResponseName nestedFieldName [] [] []]]
      ]] =>
      responseName == "animals"
      && fieldName == "animals"
      && childResponseName == "name"
      && childFieldName == "name"
      && typeCondition == "Dog"
      && variableName == "x"
      && nestedResponseName == "id"
      && nestedFieldName == "id"
  | _ => false

-- Reduction starts at the operation's root tree, then uses the selected field's named
-- output type to extract and reduce its child boundary. The type and Boolean branches
-- in that child become nested inline fragments.
theorem reductionRecursesFromParentFieldToChildSmoke
    : reductionHasExpectedShape = true := by
  native_decide

def reductionSoundnessApiSmoke : Prop :=
  ReductionSound conditionSchema "Query" reductionSourceOperation.selectionSet

def reduceOperationSoundnessApiSmoke : Prop :=
  ReduceOperationSound conditionSchema reductionSourceOperation

theorem reductionSoundnessWitnessSmoke : reductionSoundnessApiSmoke :=
  reduction_sound conditionSchema "Query" reductionSourceOperation.selectionSet

theorem reduceOperationSoundnessWitnessSmoke : reduceOperationSoundnessApiSmoke :=
  reduceOperation_sound conditionSchema reductionSourceOperation

def repeatedParentFieldOperation : Operation :=
  {
    selectionSet :=
      [
        .field "animals" "animals" [] [] [nameSelection],
        .field "animals" "animals" [] [] [idSelection]
      ]
  }

def repeatedParentFieldReductionHasMergedChild : Bool :=
  match (reduceOperation conditionSchema repeatedParentFieldOperation).selectionSet with
  | [.field responseName fieldName [] []
      [
        .field firstResponseName firstFieldName [] [] [],
        .field secondResponseName secondFieldName [] [] []
      ]] =>
      responseName == "animals"
      && fieldName == "animals"
      && firstResponseName == "name"
      && firstFieldName == "name"
      && secondResponseName == "id"
      && secondFieldName == "id"
  | _ => false

-- The two parent occurrences are captured as one response-name group before their
-- child selections are concatenated and recursively captured.
theorem reductionMergesFieldGroupChildrenBeforeRecursingSmoke
    : repeatedParentFieldReductionHasMergedChild = true := by
  native_decide

def mergedAliasBranchOperation : Operation :=
  {
    variableDefinitions := [{ name := "x", typeRef := .named "Boolean" }]
    selectionSet :=
      [
        .field "pet" "animals" [] [] [nameSelection],
        .field "pet" "animals" [] []
          [.inlineFragment (some "Dog") [.include (.variable "x")] [idSelection]]
      ]
  }

def reductionExecutionFingerprint (variableValues : Execution.VariableValues)
    (fuel : Nat) (operation : Operation)
    : String :=
  reprStr
  <| Execution.executeQueryWithFuel conditionSchema conditionTreeResolvers
      variableValues operation fuel (.object "Query" ())

def mergedAliasBranchReductionPreservesFuel
    (variableValues : Execution.VariableValues) (fuel : Nat)
    : Bool :=
  reductionExecutionFingerprint variableValues fuel mergedAliasBranchOperation
  == reductionExecutionFingerprint variableValues fuel
      (reduceOperation conditionSchema mergedAliasBranchOperation)

def mergedAliasBranchReductionRegression : Bool :=
  let fuels := List.range 12
  fuels.all (mergedAliasBranchReductionPreservesFuel [("x", .boolean false)])
  && fuels.all (mergedAliasBranchReductionPreservesFuel [("x", .boolean true)])

-- A concrete all-small-fuels check covers both exclusion/inclusion of the Boolean
-- branch while the two aliased parent occurrences are merged before child reduction.
theorem mergedAliasBranchReductionPreservesExecutionSmoke
    : mergedAliasBranchReductionRegression = true := by
  native_decide

end ConditionTree
end Tests
end GraphQL
