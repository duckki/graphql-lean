import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryEntryCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Actual plan coverage retains nullable errors across immediate and deferred partitions. -/

namespace GraphQL.IncrementalDelivery.Tests.FieldExecutionCoverage
open GraphQL.IncrementalDelivery.Execution
open Correctness

private def schema : Schema :=
  {
    queryType := "Query",
    types :=
      [.object
        {
          name := "Query",
          fields :=
            [
              { name := "a", outputType := .named "String" },
              { name := "b", outputType := .named "String" }
            ]
        }]
  }

private def resolvers : Resolvers Nat :=
  { resolve := fun _ _ _ _ => none, resolve_argumentsEquivalent := by intros; rfl }

private def selections : List Selection :=
  [defer [field "a" [] [] (some "late")], field "b" [] [] (some "now")]

private def source : ResolverValue Nat := .object "Query" 0

private def completed :=
  ((executeRootSelectionSetCore schema resolvers [] 1 "Query" source selections).run 0).1

private def reference : List (Name × ResponseValue) := [("late", .null), ("now", .null)]

/-- Exhausted recursive value fuel still proves coverage of nullable field-error results.
The ordinary reference and initial response both have counted errors, not zero-error data.
-/
private theorem fieldWitness (containers : Bool)
    : ResponseFieldCoverage containers schema resolvers [] 1 "Query" source :=
  responseFieldCoverage_of_values containers schema resolvers [] 0
    (valueCompletionCoverage_zero containers schema resolvers []) "Query" source

/-- Ordinary execution sees both nullable errors; the initial result keeps only now.
The deferred partition is computed and retained rather than assumed correct.
-/
example
    : GraphQL.Execution.executeRootSelectionSet schema resolvers [] 1 "Query" source
          (SelectionSet.eraseIncrementalDirectives selections)
        = .ok (reference, 2)
      ∧ completed.result = .ok ([("now", .null)], 1) := by
  constructor <;> cbv

/-- General actual root/plan comparison supplies the reference's covered typed entries. -/
private theorem rootCovered (containers : Bool)
    : EntriesCovered containers (TypedResponse.fields [] reference)
        (preparedFieldPositions containers [] [("now", .null)] completed.work)
        completed.work := by
  have covered := executeRoot_entriesCovered_of_fields containers schema resolvers [] 1
    "Query" source selections (by cbv) (fieldWitness containers) 0
  obtain ⟨initial, errors, same, covered⟩ := covered reference 2 (by cbv)
  have actual : completed.result = .ok ([("now", .null)], 1) := by cbv
  change completed.result = .ok (initial, errors) at same
  rw [actual] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same).symm
  exact covered

/-- Full prepared coverage does not assume initial/reference error-count agreement.
Actual collection, partitioning, execution, and alias assembly supply the certificate.
-/
example (containers : Bool)
    : PreparedResponseCovers (.object reference)
        { data := .object [("now", .null)], errors := 1 } completed.work containers := by
  apply EntriesCovered.to_prepared
  · exact (rootCovered containers).object reference [("now", .null)]
  · decide

/-- The reusable actual-root bridge supplies the same arbitrary-error certificate. -/
example (containers : Bool)
    : PreparedResponseCovers (.object reference)
        (selectionSetResultToResponse completed.result) completed.work containers :=
  executeRoot_preparedCovers_of_fields containers schema resolvers [] 1 "Query" source
    selections (by cbv) (fieldWitness containers) 0 reference 2 (by cbv)

#print axioms executeCollectedFields_entriesCovered_of_fields
#print axioms collectExecutionGroups_entriesCovered_of_fields
#print axioms executePlan_entriesCovered_of_fields
#print axioms executeRoot_entriesCovered_of_fields
#print axioms responseFieldCoverage_of_values
#print axioms executeRoot_preparedCovers_of_fields
#print axioms ResponsePositionsDeliveredOrFailed_of_fields

end GraphQL.IncrementalDelivery.Tests.FieldExecutionCoverage
