import Proofs.GraphQL.Theories.ResponsePath.ReferenceChecker
import Proofs.GraphQL.Theories.ResponsePath.SemanticToSyntactic
import Proofs.GraphQL.Theories.QueryInclusion.Completeness

/-! The syntactic-to-semantic correspondence direction of path-based query inclusion. -/

namespace GraphQL
namespace ResponsePath

open Execution
open QueryInclusion

-- Under the premises of `QueryInclusion.IncludesBoolComplete`, semantic query inclusion
-- implies path-based syntactic inclusion. Witnesses
-- `ResponsePath.IncludesSyntacticToSemantic`.
theorem includesSyntacticToSemantic {schema : Schema} {left right : Operation}
    : IncludesSyntacticToSemantic schema left right := by
  intro hschema hleftValid hrightValid hleftInhabited hrightInhabited hcoercible
    hincludes
  have hcheck : includesBool schema left right = true :=
    QueryInclusion.includesBool_complete hschema hleftValid hrightValid hleftInhabited
      hrightInhabited hcoercible hincludes
  rcases QueryInclusion.includesBool_to_selectionSetChecks hschema hleftValid
      hrightValid hcheck with
    ⟨hroot, _hdefinitions, hselectionChecks⟩
  refine ⟨hincludes.1, ?_⟩
  intro assignment hcomplete path hrightPath
  cases path with
  | nil => exact hrightPath.elim
  | cons step rest =>
      have hrightObject : schema.objectType (right.rootType schema) :=
        NormalForm.CompleteNormalization.operation_root_object_of_valid hschema
          hrightValid
      obtain ⟨hstepIncludes, hrightSel⟩ := hrightPath
      have hscope : step.parentObject = right.rootType schema := by
        have hmem : step.parentObject
            ∈ schema.getPossibleTypes (right.rootType schema) := hstepIncludes
        rw [getPossibleTypes_eq_singleton_of_object schema hrightObject] at hmem
        simpa using hmem
      rw [hscope] at hrightSel
      have haccept := hselectionChecks (boolCaseVariableValues assignment) hcomplete
      have hleftSel := selectsPath_of_selectionSetIncludesBoolWithFuel schema hschema
        (boolCaseVariableValues assignment) rest step (right.size + 1)
        (right.rootType schema) left.selectionSet right.selectionSet hrightObject
        (by
          rw [← hroot]
          exact
            NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
              hschema hleftValid)
        (by
          rw [← hroot]
          exact Validation.operationDefinitionValid_fieldsInSetCanMerge hleftValid)
        (NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
          hschema hrightValid)
        (Validation.operationDefinitionValid_fieldsInSetCanMerge hrightValid)
        haccept hscope hrightSel
      refine ⟨?_, ?_⟩
      · rw [hroot]
        exact hstepIncludes
      · rw [hroot, hscope]
        exact hleftSel

end ResponsePath
end GraphQL
