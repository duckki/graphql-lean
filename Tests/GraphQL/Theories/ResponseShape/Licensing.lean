import Proofs.GraphQL.Theories.ResponseShape.Relations.Operation
import Tests.GraphQL.Theories.ResponseShape.PremiseSatisfiability

/-!
Concrete licensing-chain coverage for the repository's minimal operation.
The test supplies every validity, computation, subset, and Boolean-completeness
premise before selecting the licensed provider path.
-/

namespace GraphQL
namespace Tests
namespace ResponseShape

open GraphQL.ResponseShape
open NormalForm

private def licensingLeafStep : PathStep :=
  {
    parentObject := "Query"
    responseName := "left"
    field := { fieldName := "left", arguments := [], outputType := .named "String" }
  }

private theorem minimalOperationBooleanVariablesEmpty
    : operationBoolVars minimalOperation = [] := by
  simp [operationBoolVars, minimalOperation, selectionSetBooleanVariables,
    selectionBooleanVariables, directivesBooleanVariables,
    CompleteNormalization.dedupBoolVars]

private theorem emptyAssignmentIsComplete
    : completeNormalBoolCase [] ([] : BoolCase) := by
  refine ⟨List.nodup_nil, List.nodup_nil, ?_⟩
  intro varName
  simp

private theorem minimalOperationSelectsItsLeaf
    : operationSelectsPath minimalSchema minimalOperation [] [licensingLeafStep] := by
  simp [operationSelectsPath, minimalOperation, minimalSchema, minimalQueryType,
    minimalField, licensingLeafStep, boolCaseVariableValues, Operation.rootType,
    OperationType.rootType, Schema.typeIncludesObject, Schema.getPossibleTypes,
    Schema.lookupField, Schema.lookupType, Schema.allTypes,
    Schema.builtinScalarDefinitions, List.find?, TypeDefinition.name,
    TypeDefinition.fields?, BuiltinScalar.name, Execution.collectFields,
    Execution.collectSelection, Execution.selectionDirectivesAllowBool,
    Execution.directiveAllowsSelectionBool, Execution.inputValueBoolean?,
    Execution.lookupVariableValue?, Execution.mergeExecutableGroups,
    collectedFieldsSelectPath,
    executableFieldMatchesPathStep, Argument.argumentsEquivalent,
    Argument.equivalent, InputValue.equivalent]

/-- `shapeSubset_selectsEquivalentPath` yields an actual provider path once
all of its minimal-fixture premises are discharged. -/
theorem minimalFixtureLicensingSelectsEquivalentPath
    : ∃ providedPath,
        operationSelectsPath minimalSchema minimalOperation [] providedPath
        ∧ PathsSemanticallyEquivalent [licensingLeafStep] providedPath := by
  rcases computeOperationShape_total minimalSchema minimalOperation
      minimalSchemaWellFormed minimalOperationValid with
    ⟨shape, hcompute, _hwellFormed, _hfullMinterm, hsupport⟩
  have hsupportEmpty : shape.boolSupport = [] := by
    rw [hsupport, minimalOperationBooleanVariablesEmpty]
  have hunion : supportUnion shape.boolSupport shape.boolSupport = [] := by
    rw [hsupportEmpty]
    rfl
  have hcomplete : completeNormalBoolCase
      (supportUnion shape.boolSupport shape.boolSupport) ([] : BoolCase) := by
    rw [hunion]
    exact emptyAssignmentIsComplete
  exact shapeSubset_selectsEquivalentPath minimalSchema
    minimalOperation minimalOperation shape shape
    [] [licensingLeafStep]
    minimalSchemaWellFormed minimalOperationValid minimalOperationValid
    hcompute hcompute
    (shapeSubset_refl minimalSchema shape)
    hcomplete
    minimalOperationSelectsItsLeaf

end ResponseShape
end Tests
end GraphQL
