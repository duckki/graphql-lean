import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingCutHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutKeySupply
import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamAllocations
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Constructed atomic-action cuts. The key-shift witness uses original public field
actions and nullable completion, not arbitrary Work or a claimed concrete host trace.
-/

namespace AlternativeSiblingCutChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement.ScheduledErrors
open Semantics.GeneralScheduling

private def streamField : FieldDetails :=
  { fieldName := "values", arguments := [], directives := [.stream], selectionSet := [] }

private def fatalFields : CollectedFieldsMap :=
  [
    ("required", [{ fieldName := "required", arguments := [], selectionSet := [] }]),
    ("cancelled", [streamField])
  ]

private def fatalActions :=
  fieldActions Tests.schema Tests.resolvers [] 4 "Query" (.object "Query" 0)
    fatalFields [.field "parent"] [] []

private def cut := (observeUntilFatal fatalActions).run 17

private def eagerFields :=
  (executeCollectedFields Tests.schema Tests.resolvers [] 4 "Query" (.object "Query" 0)
    fatalFields [.field "parent"] [] []).run
    17

private theorem constructed_cut : ActionCut fatalActions 17 cut.1.1 cut.1.2 cut.2 :=
  observeUntilFatal_cut ..

-- The skipped public stream action would allocate a key despite its enclosing failure.
example : cut.1.1.length = 1 := by cbv
example : cut.1.2.length = 1 := by cbv
example : cut.2 = 17 := by cbv
example : eagerFields.2 = 18 := by cbv
example : eagerFields.1.result = .error 1 := by cbv
example : eagerFields.1.work = .empty := by cbv

example
    : countedErrors (foldCompletions List.append [] cut.1.1).result
        + countedErrors
            (foldCompletions List.append [] ((observeActions cut.1.2).run cut.2).1).result
      = countedErrors eagerFields.1.result := by
  unfold eagerFields
  rw [executeCollectedFields_actions]
  exact constructed_cut.error_accounting List.append []

example
    : (foldCompletions List.append [] cut.1.1).work = .empty
      ∧ (executeActions List.append [] fatalActions |>.run 17).1.work = .empty :=
  constructed_cut.fatal_no_children List.append [] (by cbv)

private def eagerParent : StateM Nat (Completion ResponseValue) := do
  let completed ←
    executeCollectedFields Tests.schema Tests.resolvers [] 4 "Query" (.object "Query" 0)
      fatalFields [.field "parent"] [] []
  return completed.catchNull ResponseValue.object

private def cutParent : StateM Nat (Completion ResponseValue) := do
  let completed ← cutActions List.append [] fatalActions
  return completed.catchNull ResponseValue.object

private def survivingStream :=
  executeField Tests.schema Tests.resolvers [] 4 "Query" (.object "Query" 0)
    { name := "values", outputType := .list (.named "String") }
    "survivor" [streamField] [] [] []

private def eagerOuter :=
  (executeActions List.cons [] [eagerParent, survivingStream]).run 17

private def cutOuter := (executeActions List.cons [] [cutParent, survivingStream]).run 17

-- A caught nullable cut preserves data and errors here, but shifts a later live stream.
example : eagerOuter.1.result = cutOuter.1.result := by cbv
example : eagerOuter.2 = 19 := by cbv
example : cutOuter.2 = 18 := by cbv
example : streamAllocationRefs eagerOuter.1.work = [18] := by cbv
example : streamAllocationRefs cutOuter.1.work = [17] := by cbv

-- One map through retained work repairs this actual allocation shift, not its supply.
example
    : AlternativeWorkQueue.NativeRefinement.KeyRenaming.work (fun key => key + 1)
        cutOuter.1.work
      = eagerOuter.1.work := by cbv

private def earlierStream :=
  executeField Tests.schema Tests.resolvers [] 4 "Query" (.object "Query" 0)
    { name := "values", outputType := .list (.named "String") }
    "before" [streamField] [] [] []

private def lastStream :=
  executeField Tests.schema Tests.resolvers [] 4 "Query" (.object "Query" 0)
    { name := "values", outputType := .list (.named "String") }
    "final" [streamField] [] [] []

private def eagerWithPrefix :=
  (executeActions List.cons [] [earlierStream, eagerParent, survivingStream]).run 17

private def cutWithPrefix :=
  (executeActions List.cons [] [earlierStream, cutParent, survivingStream]).run 17

-- A global shift would also rename the earlier live stream, which is incorrect.
example : streamAllocationRefs eagerWithPrefix.1.work = [17, 19] := by cbv
example : streamAllocationRefs cutWithPrefix.1.work = [17, 18] := by cbv

example
    : AlternativeWorkQueue.NativeRefinement.KeyRenaming.work (fun key => key + 1)
        cutWithPrefix.1.work
      ≠ eagerWithPrefix.1.work := by
  intro same
  have allocated := congrArg streamAllocationRefs same
  cbv at allocated
  contradiction

example
    : AlternativeWorkQueue.NativeRefinement.KeyRenaming.work
        (AlternativeWorkQueue.NativeRefinement.KeyRenaming.insertGap 18 1)
        cutWithPrefix.1.work
      = eagerWithPrefix.1.work := by cbv

private def eagerTwoCuts :=
  (executeActions List.cons []
    [earlierStream, eagerParent, survivingStream, eagerParent, lastStream]).run
    17

private def cutTwoCuts :=
  (executeActions List.cons []
    [earlierStream, cutParent, survivingStream, cutParent, lastStream]).run
    17

-- The second gap extends the same map; it does not disturb the first retained prefix.
example : streamAllocationRefs eagerTwoCuts.1.work = [17, 19, 21] := by cbv
example : streamAllocationRefs cutTwoCuts.1.work = [17, 18, 19] := by cbv

example
    : AlternativeWorkQueue.NativeRefinement.KeyRenaming.work
        (AlternativeWorkQueue.NativeRefinement.KeyRenaming.extendAtCut
          (AlternativeWorkQueue.NativeRefinement.KeyRenaming.insertGap 18 1) 19 1)
        cutTwoCuts.1.work
      = eagerTwoCuts.1.work := by cbv

-- The map boundary and gap are constructed from one actual public-action cut.
example
    : let actual := (observeUntilFatal fatalActions).run 18
      let eager := (observeActions fatalActions).run 18
      let keys :=
        AlternativeWorkQueue.NativeRefinement.KeyRenaming.insertGap
          actual.2 (eager.2 - actual.2)
      Function.Injective keys
      ∧ 18 ≤ actual.2
      ∧ actual.2 ≤ eager.2
      ∧ (∀ key, key < actual.2 → keys key = key)
      ∧ keys actual.2 = eager.2 := by
  exact cutSupplyExtension_holds _ fatalActions 18
    (fieldActions_monotone _ _ _ _ _ _ _ _ _ _ _ (by simp))

-- Literal Work/key equality is the wrong recursive refinement target after cancellation.
example : eagerOuter.1.work ≠ cutOuter.1.work := by
  intro same
  have keys := congrArg streamAllocationRefs same
  have eagerKeys : streamAllocationRefs eagerOuter.1.work = [18] := by cbv
  have cutKeys : streamAllocationRefs cutOuter.1.work = [17] := by cbv
  rw [eagerKeys, cutKeys] at keys
  contradiction

private def healthyFields : CollectedFieldsMap :=
  [
    ("nullable", [{ fieldName := "fail", arguments := [], selectionSet := [] }]),
    ("survivor", [streamField])
  ]

private def healthyActions :=
  fieldActions Tests.schema Tests.resolvers [] 4 "Query" (.object "Query" 0)
    healthyFields [] [] []

private def healthyCut := (observeUntilFatal healthyActions).run 17

-- Nullable errors do not cut a scope; all child work and final allocation agree exactly.
example
    : healthyCut.1.2 = []
      ∧ (executeActions List.append [] healthyActions).run 17
        = (foldCompletions List.append [] healthyCut.1.1, healthyCut.2) :=
  (observeUntilFatal_cut healthyActions 17).nonfatal_exact List.append [] (by cbv)

example : countedErrors (foldCompletions List.append [] healthyCut.1.1).result = 1 := by
  cbv

example : healthyCut.2 = 18 := by cbv

-- The original public result licenses exact agreement, including its streamed child work.
example
    : (cutActions List.append [] healthyActions).run 17
      = (executeCollectedFields Tests.schema Tests.resolvers [] 4 "Query"
          (.object "Query" 0) healthyFields [] [] []).run
          17 :=
  executeCollectedFields_cut_exact _ _ _ _ _ _ _ _ _ _ _ (by cbv)

private def pairFields : CollectedFieldsMap :=
  [
    ("first", [{ fieldName := "required", arguments := [], selectionSet := [] }]),
    ("second", [{ fieldName := "required", arguments := [], selectionSet := [] }])
  ]

private def pairActions :=
  fieldActions Tests.schema Tests.resolvers [] 4 "Query" (.object "Query" 0)
    pairFields [] [] []

private def pairCut := (observeUntilFatal pairActions).run 17
private def pairPlan := completionPlan ((observeActions pairActions).run 17).1 0

-- Here the scope history and exact ordered trace are constructed, not supplied as premises.
example
    : ∃ scope,
        History pairPlan scope
        ∧ scope.actions = [.start 0, .settle 0, .cancel 1]
        ∧ scope.observe pairPlan = some (.error 1)
        ∧ errorTotal scope.cancelled = 1 := by
  obtain ⟨scope, history, complete, settled, cancelled, actions, reported⟩ :=
    (observeUntilFatal_cut pairActions 17).scope_history 0
  have failed : scope.fatal = true := by
    rw [history.fatal, settled]
    cbv
  refine ⟨scope, history, ?_, ?_, ?_⟩
  · rw [actions]
    cbv
  · simp only [Scope.observe, complete, List.isEmpty_nil, ↓reduceIte, failed, reported]
    cbv
  · rw [cancelled]
    cbv

example : countedErrors (eager pairPlan) = 2 := by cbv

#print axioms observeUntilFatal_cut
#print axioms ActionCut.observed
#print axioms ActionCut.error_accounting
#print axioms ActionCut.sameData
#print axioms ActionCut.nonfatal_exact
#print axioms ActionCut.fatal_no_children
#print axioms ActionCut.scope_history
#print axioms cutActions_nonfatal_exact
#print axioms executeCollectedFields_cut_exact
#print axioms completeListValue_cut_exact
#print axioms cutSupplyExtension_holds
#print axioms fieldActions_monotone
#print axioms listActions_monotone
#print axioms executeCollectedFields_cut_supply
#print axioms completeListValue_cut_supply
#print axioms AlternativeWorkQueue.NativeRefinement.KeyRenaming.work_comp

end AlternativeSiblingCutChecks
