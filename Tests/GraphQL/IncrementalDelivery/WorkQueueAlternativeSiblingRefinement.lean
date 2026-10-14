import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledSiblingRefinement
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Conditional sibling composition applied to generated recursive child runs.
The finite leaves compute their relation at arbitrary paired supplies; no desired
child refinement, independently chosen outcome or native trace is a test premise. -/

namespace AlternativeSiblingRefinementChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open ScheduledErrors

private def streamField : FieldDetails :=
  { fieldName := "values", arguments := [], directives := [.stream], selectionSet := [] }

private def userField : FieldDetails :=
  {
    fieldName := "user",
    arguments := [],
    selectionSet :=
      [
        Tests.field "required" [] [] (some "first"),
        Tests.field "required" [] [] (some "second"),
        Tests.field "values" [] [.stream]
      ]
  }

private def fields : CollectedFieldsMap :=
  [("user", [userField]), ("values", [streamField])]

private def child (cancel : Bool) (name : GraphQL.Name) (field : FieldDetails) :=
  let execute :=
    if cancel then
      @ScheduledExecution.executeResponseField Nat
    else
      @Semantics.executeResponseField Nat
  execute Tests.schema Tests.resolvers [] 7 "Query" (.object "Query" 0) name [field] [] []
    []

private theorem user_refines
    : ActionRefines (fun _ _ => True)
        (child true "user" userField) (child false "user" userField) := by
  intro left right _
  refine ⟨?_, trivial, ?_⟩
  · cbv; rfl
  · exact (ScheduledExecution.executeResponseField_positive Tests.schema Tests.resolvers [] 7
      "Query" (.object "Query" 0) "user" [userField] [] [] [] left).1

private theorem stream_refines
    : ActionRefines (fun _ _ => True)
        (child true "values" streamField) (child false "values" streamField) := by
  intro left right _
  refine ⟨?_, trivial, ?_⟩
  · cbv; rfl
  · exact (ScheduledExecution.executeResponseField_positive Tests.schema Tests.resolvers [] 7
      "Query" (.object "Query" 0) "values" [streamField] [] [] [] left).1

private theorem paired
    : PairedActions (fun _ _ => True)
        (ScheduledExecution.fieldActions Tests.schema Tests.resolvers [] 7 "Query"
          (.object "Query" 0) fields [] [] [])
        (fieldActions Tests.schema Tests.resolvers [] 7 "Query" (.object "Query" 0) fields
          [] [] []) :=
  .cons user_refines (.cons stream_refines .nil)

private def run (cancel : Bool) (supply : Nat) :=
  let execute :=
    if cancel then
      @ScheduledExecution.executeCollectedFields Nat
    else
      @Execution.executeCollectedFields Nat
  (execute Tests.schema Tests.resolvers [] 7 "Query" (.object "Query" 0) fields [] []
    []).run
    supply

-- The generic reduction is used, with constructed finite recursive leaves. The outer
-- scope is healthy, but its child's caught cut changes counts and key supplies.
example (left right : Nat)
    : ResultRefines (run true left).1.result (run false right).1.result :=
  ScheduledExecution.executeCollectedFields_result_refines_of_children Tests.schema
    Tests.resolvers [] 7 "Query" (.object "Query" 0) fields fields [] [] [] [] []
    (fun _ _ => True) left right paired trivial

example : countedErrors (run true 17).1.result = 1 := by cbv
example : countedErrors (run false 17).1.result = 2 := by cbv
example : (run true 17).2 = 18 := by cbv
example : (run false 17).2 = 19 := by cbv

private def item (cancel : Bool) (ref index : Nat) :=
  let complete :=
    if cancel then
      @ScheduledExecution.completeValue Nat
    else
      @Execution.completeValue Nat
  complete Tests.schema Tests.resolvers [] 7 (.nonNull (.named "User")) [userField]
    (.object "User" ref) [.index index] [] [] false

private theorem item_refines (ref index : Nat)
    : ActionRefines (fun _ _ => True) (item true ref index) (item false ref index) := by
  intro left right _
  refine ⟨?_, trivial, ?_⟩
  · cbv; rfl
  · exact (ScheduledExecution.completeValue_positive Tests.schema Tests.resolvers [] 7
      (.nonNull (.named "User")) [userField] (.object "User" ref) [.index index]
      [] [] false left).1

private def values : List (ResolverValue Nat) := [.object "User" 1, .object "User" 2]

private theorem pairedItems
    : PairedActions (fun _ _ => True)
        (ScheduledExecution.listActions Tests.schema Tests.resolvers [] 7
          (.nonNull (.named "User")) [userField] [] [] [] values 0)
        (listActions Tests.schema Tests.resolvers [] 7 (.nonNull (.named "User"))
          [userField] [] [] [] values 0) :=
  .cons (item_refines 1 0) (.cons (item_refines 2 1) .nil)

private def listRun (cancel : Bool) (supply : Nat) :=
  let complete :=
    if cancel then
      @ScheduledExecution.completeListValue Nat
    else
      @Execution.completeListValue Nat
  (complete Tests.schema Tests.resolvers [] 7 (.nonNull (.named "User")) [userField]
    values [] 0 [] []).run
    supply

-- These values are the actual finite resolver list, not independently selected results.
example
    : Tests.resolvers.resolve "Query" "users" [] (.object "Query" 0)
      = some (.list values) := by cbv

-- Changed recursive item outcomes compose through the real ordinary-list call site;
-- its first fatal object also cancels the second item.
example (left right : Nat)
    : ResultRefines (listRun true left).1.result (listRun false right).1.result :=
  ScheduledExecution.completeListValue_result_refines_of_children Tests.schema
    Tests.resolvers [] 7 (.nonNull (.named "User")) [userField] [userField] values [] 0 []
    [] [] [] (fun _ _ => True) left right pairedItems trivial

example : countedErrors (listRun true 17).1.result = 1 := by cbv
example : countedErrors (listRun false 17).1.result = 4 := by cbv

-- Exact statement check, including the explicitly conditional paired-child obligation.
example : SiblingResultRefinement := siblingResultRefinement_holds

-- Raw zero-count fatal cuts cannot preserve error presence if a skipped sibling fails.
example
    : ¬ ResultRefines (Except.error 0 : Result Nat)
          (Result.combine Nat.add (.error 0) (.error 1)) := by
  simp [ResultRefines, SameData, Result.combine, countedErrors]

-- Error presence cannot vanish across nullable completion.
example
    : ¬ ResultRefines (Except.ok (.null, 0) : Result ResponseValue) (.ok (.null, 2)) := by
  simp [ResultRefines, SameData, countedErrors]

-- Counts alone cannot license which originating errors were omitted. This weaker
-- relation permits 1 versus 2; preservation of prior records needs the separate ledger.
example : ResultRefines (Except.error 1 : Result ResponseValue) (.error 2) := by
  simp [ResultRefines, SameData, countedErrors]

#print axioms ResultRefines.combine
#print axioms ResultRefines.fatal_cut
#print axioms ResultRefines.completion_map
#print axioms ResultRefines.catchNull
#print axioms ResultRefines.nonNull
#print axioms siblingResultRefinement_holds
#print axioms ScheduledExecution.executeResponseField_failure_form
#print axioms ScheduledExecution.executeCollectedFields_actions
#print axioms ScheduledExecution.completeListValue_actions
#print axioms ScheduledExecution.executeCollectedFields_result_refines_of_children
#print axioms ScheduledExecution.completeListValue_result_refines_of_children

end AlternativeSiblingRefinementChecks
