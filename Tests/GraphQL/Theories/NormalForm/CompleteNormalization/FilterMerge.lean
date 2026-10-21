import Tests.GraphQL.Validation.FieldMerge
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.FilterMerge
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Operation

namespace GraphQL.Tests.NormalForm.CompleteNormalization.FilterMerge

open GraphQL.NormalForm
open GraphQL.NormalForm.CompleteNormalization
open GraphQL.Tests.Validation.FieldMerge

private def leftBranch : List Selection :=
  [.field "user" "user" [] [.include (.variable "flag")] directName]

private def rightBranch : List Selection :=
  [.field "user" "user" [] [.skip (.variable "flag")] fragmentName]

private theorem source_canMerge
    : GraphQL.FieldMerge.fieldsInSetCanMerge returnScopeSchema "Query"
        (leftBranch ++ rightBranch) := by
  refine .intro _ _ ?_
  dsimp
  intro left hleft right hright hresponse
  have hcollect : GraphQL.FieldMerge.collectFields returnScopeSchema "Query"
        (leftBranch ++ rightBranch)
      = GraphQL.FieldMerge.collectFields returnScopeSchema "Query"
          returnScopeQuery.selectionSet := by
    simp [leftBranch, rightBranch, returnScopeQuery, GraphQL.FieldMerge.collectFields]
  exact GraphQL.FieldMerge.fieldsInSetCanMerge_pair returnScopeQuery_canMerge
    (hcollect ▸ hleft) (hcollect ▸ hright) hresponse

theorem differentAssignments_canMerge (leftCase rightCase : BoolCase)
    : GraphQL.FieldMerge.fieldsInSetCanMerge returnScopeSchema "Query"
        (filterSelectionSetBoolCase leftCase leftBranch
          ++ filterSelectionSetBoolCase rightCase rightBranch) :=
  fieldsInSetCanMerge_filterSelectionSetBoolCase_pair returnScopeSchema
    leftCase rightCase source_canMerge

theorem differentAssignments_retainBothDeclaredReturns
    : filterSelectionSetBoolCase [("flag", true)] leftBranch
        ++ filterSelectionSetBoolCase [("flag", false)] rightBranch
      = returnScopeQuery.selectionSet := by
  simp [leftBranch, rightBranch, returnScopeQuery, directName, fragmentName,
    filterSelectionSetBoolCase, directivesAllowIn, directiveAllowsIn,
    inputValueBoolIn?, BoolCase.lookup?]

theorem differentAssignments_declaredReturnScope
    : GraphQL.FieldMerge.fieldsInSetCanMerge returnScopeSchema "Query"
        returnScopeQuery.selectionSet := by
  rw [← differentAssignments_retainBothDeclaredReturns]
  exact differentAssignments_canMerge [("flag", true)] [("flag", false)]

theorem completeValidity_contract (schema : Schema) (operation : Operation)
    : completeNormalizeOperationValid schema operation :=
  completeNormalizeOperation_valid schema operation

end GraphQL.Tests.NormalForm.CompleteNormalization.FilterMerge
