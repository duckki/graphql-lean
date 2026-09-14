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
    foldAnnotatedResponseValue, foldAnnotatedResponseFields,
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

theorem syntacticAnalysisSoundApiSmoke
    (schema : Schema) (listSize : Nat) (operation : Operation)
    : GraphQL.TreeSummary.MaxResponseSize.Syntactic.AnalysisSound schema listSize
        operation :=
  Syntactic.analysisSound schema listSize operation

theorem syntacticAnalysisWithVariablesSoundApiSmoke
    (schema : Schema) (listSize : Nat) (operation : Operation)
    : GraphQL.TreeSummary.MaxResponseSize.Syntactic.AnalysisWithVariablesSound schema
        listSize operation :=
  Syntactic.analysisWithVariablesSound schema listSize operation

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

def multiplierStaticDefinition : FieldDefinition :=
  {
    name := "values"
    outputType := .list (.list (.named "String"))
  }

def multiplierImplementationA : FieldDefinition :=
  {
    name := "values"
    outputType := .nonNull (.list (.nonNull (.list (.nonNull (.named "String")))))
  }

def multiplierImplementationB : FieldDefinition :=
  {
    name := "values"
    outputType := .list (.nonNull (.list (.named "String")))
  }

def multiplierSchema : Schema :=
  {
    queryType := "A"
    types :=
      [
        .object
          {
            name := "A"
            fields := [multiplierImplementationA]
          },
        .object
          {
            name := "B"
            fields := [multiplierImplementationB]
          }
      ]
  }

def multiplierGroup : CollectedFieldGroup :=
  {
    inheritedBooleanCondition := []
    condition :=
      {
        possibleTypes := ["A", "A", "B"]
        booleanCondition := []
      }
    fieldGroup :=
      {
        responseName := "values"
        first :=
          {
            fieldName := "values"
            arguments := []
            selectionSet := []
          }
        rest := []
      }
  }

private theorem stringOutputTypeSubtypeSelf
    : multiplierSchema.outputTypeSubtype (.named "String") (.named "String") := by
  simp [Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype, Schema.isLeafType,
    Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
    BuiltinScalar.name, TypeDefinition.name, TypeDefinition.isLeafType,
    multiplierSchema]

private theorem multiplierRuntimeDefinitionsCovariant
    : ∀ parentType ∈ multiplierGroup.condition.possibleTypes,
      ∃ implementation,
        multiplierSchema.lookupField parentType
            multiplierGroup.representativeField.fieldName = some implementation
        ∧ multiplierSchema.outputTypeSubtype implementation.outputType
            multiplierStaticDefinition.outputType := by
  intro parentType hparentType
  have hparent : parentType = "A" ∨ parentType = "B" := by
    simpa [multiplierGroup] using hparentType
  rcases hparent with rfl | rfl
  · refine ⟨multiplierImplementationA, ?_, ?_⟩
    · rfl
    · simpa [multiplierImplementationA, multiplierStaticDefinition,
        Schema.outputTypeSubtype] using stringOutputTypeSubtypeSelf
  · refine ⟨multiplierImplementationB, ?_, ?_⟩
    · rfl
    · simpa [multiplierImplementationB, multiplierStaticDefinition,
        Schema.outputTypeSubtype] using stringOutputTypeSubtypeSelf

private theorem multiplierDefinitionsCompatible :
    multiplierGroup.FieldDefinitionsCompatible multiplierSchema :=
  ⟨multiplierStaticDefinition.outputType, multiplierRuntimeDefinitionsCovariant⟩

theorem fieldListMultiplierReferenceEquivalenceSmoke :
    fieldListMultiplierForAllDefinitions multiplierSchema 3 multiplierGroup =
      fieldListMultiplier multiplierSchema 3 multiplierGroup := by
  apply fieldListMultiplierForAllDefinitions_eq_fieldListMultiplier
  · simp [multiplierGroup]
  · exact multiplierDefinitionsCompatible

-- The old scan and the definition-based shortcut agree for multiple runtime parents,
-- duplicate output definitions, and strengthened nullability at several wrapper levels.
theorem fieldListMultiplierDefinitionShortcutSmoke
    : fieldListMultiplier multiplierSchema 3 multiplierGroup =
        fieldListMultiplierForDefinition 3 multiplierStaticDefinition := by
  apply fieldListMultiplier_eq_forDefinition
  · simp [multiplierGroup]
  · exact multiplierRuntimeDefinitionsCovariant

-- Bounds zero and one retain the fold's minimum multiplier of one; a larger bound is
-- raised once for each nested list wrapper.
theorem fieldListMultiplierDefinitionBoundarySmoke
    : fieldListMultiplierForDefinition 0 multiplierStaticDefinition = 1
      ∧ fieldListMultiplierForDefinition 1 multiplierStaticDefinition = 1
      ∧ fieldListMultiplierForDefinition 3 multiplierStaticDefinition = 9 := by
  native_decide

theorem singularFieldListMultiplierDefinitionSmoke
    : fieldListMultiplierForDefinition 3
        ({ name := "value", outputType := .named "String" } : FieldDefinition) = 1 := by
  native_decide

-- Covariance may also narrow the named output while preserving the enclosing list
-- shape; the proof does not require equality of the names.
theorem covariantNamedOutputsPreserveListMultiplierSmoke (schema : Schema)
    (hsubtype : schema.outputTypeSubtype
      (.list (.named "Implementation")) (.list (.named "Expected")))
    : listMultiplier 3 (.list (.named "Implementation")) =
        listMultiplier 3 (.list (.named "Expected")) :=
  listMultiplier_eq_of_outputTypeSubtype schema 3 hsubtype

def emptyMultiplierGroup : CollectedFieldGroup :=
  {
    multiplierGroup with
      condition := { multiplierGroup.condition with possibleTypes := [] }
  }

-- The nonempty-runtime-type premise is necessary: the original empty fold returns one,
-- while a static nested-list definition can have a larger multiplier.
theorem emptyFieldListMultiplierDoesNotUseStaticDefinition
    : fieldListMultiplier multiplierSchema 3 emptyMultiplierGroup = 1
      ∧ fieldListMultiplierForDefinition 3 multiplierStaticDefinition = 9 := by
  native_decide

theorem fieldListMultiplierSchemaCorollaryApiSmoke
    (schema : Schema) (listSize : Nat) (group : CollectedFieldGroup)
    (staticParentType : Name) (definition : FieldDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hdefinition : schema.lookupField staticParentType
      group.representativeField.fieldName = some definition)
    (hpossible : ∀ parentType ∈ group.condition.possibleTypes,
      parentType ∈ schema.getPossibleTypes staticParentType)
    (hnonempty : group.condition.possibleTypes ≠ [])
    : fieldListMultiplier schema listSize group =
        fieldListMultiplierForDefinition listSize definition :=
  fieldListMultiplier_eq_forDefinition_of_schemaWellFormed schema listSize group
    staticParentType definition hschema hdefinition hpossible hnonempty

theorem analysisOptimalApiSmoke (schema : Schema) (listSize : Nat) (operation : Operation)
    : ExactCases.AnalysisOptimal schema listSize operation :=
  ExactCases.analysisOptimal schema listSize operation

theorem analysisWithVariablesOptimalApiSmoke (schema : Schema) (listSize : Nat)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : ExactCases.AnalysisWithVariablesOptimal schema listSize variableValues operation :=
  ExactCases.analysisWithVariablesOptimal schema listSize variableValues operation

end MaxResponseSize
end TreeSummary
end Tests
end GraphQL
