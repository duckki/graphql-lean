import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.ResponsePath.ReferenceChecker
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.CompleteNormalization.Validity.Variables

namespace GraphQL.QueryInclusion

open Execution
open ResponsePath

-- Root-level path bookkeeping supplied by the talk scaffold.
theorem includes_of_complete_reference_checks {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hroot : left.rootType schema = right.rootType schema)
    (hdefinitions
      : sharedVariableDefinitionsSyntacticallyCompatible
          left.variableDefinitions right.variableDefinitions)
    (hselectionChecks
      : ∀ assignment : BoolCase,
          boolVarsComplete
            (comparisonConditionVariables left.selectionSet right.selectionSet)
            (boolCaseVariableValues assignment)
          -> selectionSetIncludesBoolWithFuel schema (right.size + 1)
                (right.rootType schema) (boolCaseVariableValues assignment)
                left.selectionSet right.selectionSet
              = true)
    : includes schema left right := by
  refine ⟨hdefinitions, ?_⟩
  intro assignment hcomplete path hrightPath
  cases path with
  | nil => exact hrightPath.elim
  | cons step rest =>
      have hrightObject : schema.objectType (right.rootType schema) :=
        NormalForm.CompleteNormalization.operation_root_object_of_valid hschema hrightValid
      obtain ⟨hstepIncludes, hrightSel⟩ := hrightPath
      have hscope : step.parentObject = right.rootType schema := by
        have hmem : step.parentObject ∈ schema.getPossibleTypes (right.rootType schema) := hstepIncludes
        rw [getPossibleTypes_eq_singleton_of_object schema hrightObject] at hmem
        simpa using hmem
      rw [hscope] at hrightSel
      have hleftSel := selectsPath_of_selectionSetIncludesBoolWithFuel schema hschema
        (boolCaseVariableValues assignment) rest step (right.size + 1)
        (right.rootType schema) left.selectionSet right.selectionSet hrightObject
        (by
          rw [← hroot]
          exact NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
            hschema hleftValid)
        (by
          rw [← hroot]
          exact Validation.operationDefinitionValid_fieldsInSetCanMerge hleftValid)
        (NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
          hschema hrightValid)
        (Validation.operationDefinitionValid_fieldsInSetCanMerge hrightValid)
        (hselectionChecks assignment hcomplete) hscope hrightSel
      refine ⟨?_, ?_⟩
      · rw [hroot]; exact hstepIncludes
      · rw [hroot, hscope]; exact hleftSel

end GraphQL.QueryInclusion
