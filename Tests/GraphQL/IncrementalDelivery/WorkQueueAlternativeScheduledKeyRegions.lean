import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledActionSupply
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutRecordingHistory
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Generated recursive key-region certificates and their actual scope-witness consumer.
The all-sibling comparison driver keeps recursively cut children: its error count is
not the public eager count. No native originating-error or whole-query map claim is made. -/

namespace AlternativeScheduledKeyRegionChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement ScheduledErrors
open Semantics.RefRegions

example : ScheduledExecution.RecursiveScheduledKeyRegions :=
  ScheduledExecution.recursiveScheduledKeyRegions_holds

-- All keys in actual root work are fresh and bounded; no output invariant is a premise.
example (schema : GraphQL.Schema) (resolvers : Resolvers Nat)
    (variables : VariableValues) (fuel : Nat) (parentType : GraphQL.Name)
    (source : ResolverValue Nat) (selections : List Selection) (supply key : Nat)
    (present
      : key
        ∈ allRefs
            ((ScheduledExecution.executeRootSelectionSetCore schema resolvers
                variables fuel parentType source selections).run
              supply).1.work)
    : supply ≤ key
      ∧ key
        < ((ScheduledExecution.executeRootSelectionSetCore schema resolvers
              variables fuel parentType source selections).run
            supply).2 :=
  (ScheduledExecution.recursiveScheduledKeyRegions_holds Nat schema resolvers variables
    fuel parentType source selections supply).all_fresh
    key present

private def streamField : FieldDetails :=
  { fieldName := "values", arguments := [], directives := [.stream], selectionSet := [] }

private def requiredField : FieldDetails :=
  { fieldName := "required", arguments := [], selectionSet := [] }

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
  [
    ("user", [userField]),
    ("required", [requiredField]),
    ("later", [requiredField]),
    ("values", [streamField])
  ]

private def actions :=
  ScheduledExecution.fieldActions Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) fields [] [] []

private def plan := completionPlan ((observeActions actions).run 17).1 0

private def actual :=
  (ScheduledExecution.executeCollectedFields Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) fields [] [] []).run
    17

example : actual.1.result = .error 2 := by cbv
example : actual.2 = 17 := by cbv
example : countedErrors (eager plan) = 3 := by cbv
example : ((observeActions actions).run 17).2 = 18 := by cbv

example
    : (executeCollectedFields Tests.schema Tests.resolvers [] 7 "Query"
          (.object "Query" 0) fields [] [] []
        |>.run 17).1.result
      = .error 4 := by cbv

-- The prior nullable count is itself computed by recursive cancellation. The same
-- constructed scope records it and the fatal field, omits only untouched sibling slots,
-- and constructs the gap to the all-sibling driver without a monotonicity premise.
example
    : ∃ recording,
        RecordingHistory plan recording
        ∧ recording.scope.pending = []
        ∧ recording.available = []
        ∧ recording.recorded = [(0, 0), (1, 0)]
        ∧ recording.omitted = [(2, 0)]
        ∧ recording.observe plan = some (.error 2)
        ∧ recording.recorded.length = countedErrors actual.1.result
        ∧ (recording.recorded ++ recording.omitted).Nodup
        ∧ SupplyExtension 17 actual.2 ((observeActions actions).run 17).2 := by
  obtain ⟨recording, history, complete, accounted, recorded, omitted, trace, observed,
      balanced, unique, extension⟩ :=
    atomicCutWitness_holds _ actions 17 0
      (ScheduledExecution.fieldActions_monotone Tests.schema Tests.resolvers [] 7 "Query"
        (.object "Query" 0) fields [] [] [] 17 (by simp))
  refine ⟨recording, history, complete, accounted, ?_, ?_, ?_, ?_, unique, ?_⟩
  · rw [recorded]; cbv
  · rw [omitted]; cbv
  · unfold plan
    rw [observed]; cbv
  · rw [recorded]; cbv
  · simpa only [actual, ScheduledExecution.executeCollectedFields_actions, cutActions,
      Semantics.run_bind, StateT.run_pure, Semantics.id_pure_eq, actions] using extension

#print axioms ScheduledExecution.planKeyRegions_holds
#print axioms ScheduledExecution.recursiveScheduledKeyRegions_holds
#print axioms ScheduledExecution.fieldActions_monotone
#print axioms ScheduledExecution.listActions_monotone
#print axioms ScheduledExecution.executeCollectedFields_cut_supply
#print axioms ScheduledExecution.completeListValue_cut_supply

end AlternativeScheduledKeyRegionChecks
