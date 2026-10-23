import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledPositivity
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.WorkKeyRenaming
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledErrors
import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamAllocations
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Generated root executions using recursively cancelled completion, not wrappers
around unchanged public actions. These are finite sequential policy regressions;
they do not claim to describe a native async execution or its error objects. -/

namespace AlternativeRecursiveCutChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open Semantics.GeneralScheduling

private def requiredPair : List Selection :=
  [
    Tests.field "required" [] [] (some "first"),
    Tests.field "required" [] [] (some "second")
  ]

private def eager (selections : List Selection) :=
  (executeRootSelectionSetCore Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) selections).run
    17

private def scheduled (selections : List Selection) :=
  (ScheduledExecution.executeRootSelectionSetCore Tests.schema Tests.resolvers [] 7
    "Query" (.object "Query" 0) selections).run
    17

private def caughtThenStream : List Selection :=
  [
    Tests.field "user" (requiredPair ++ [Tests.field "values" [] [.stream]]),
    Tests.field "values" [] [.stream]
  ]

-- An actual nested object cut changes both counted errors and the next live stream key.
example
    : (eager caughtThenStream).1.result
      = .ok ([("user", .null), ("values", .list [])], 2) := by cbv

example
    : (scheduled caughtThenStream).1.result
      = .ok ([("user", .null), ("values", .list [])], 1) := by cbv

example : streamAllocationRefs (eager caughtThenStream).1.work = [18] := by cbv
example : streamAllocationRefs (scheduled caughtThenStream).1.work = [17] := by cbv
example : (eager caughtThenStream).2 = 19 := by cbv
example : (scheduled caughtThenStream).2 = 18 := by cbv

private def deferredCaught : List Selection :=
  [Tests.defer [Tests.field "user" requiredPair]]

-- Initial errors alone do not reveal changed recursively computed task payloads.
example : (eager deferredCaught).1.result = .ok ([], 0) := by cbv
example : (scheduled deferredCaught).1.result = .ok ([], 0) := by cbv
example : (eager deferredCaught).2 = (scheduled deferredCaught).2 := by cbv

private def groupErrors : Work → List Nat
  | .empty | .stream _ _ => []
  | .declareGroups _ tasks => groupErrors tasks
  | .combine left right => groupErrors left ++ groupErrors right
  | .executionGroup _ _ result children =>
      ScheduledErrors.countedErrors result.result :: groupErrors children

private theorem groupErrors_renaming (keys : Nat → Nat) (original : Work)
    : groupErrors (KeyRenaming.work keys original) = groupErrors original := by
  cases original with
  | empty => simp only [KeyRenaming.work, groupErrors]
  | declareGroups groups tasks =>
      simp only [KeyRenaming.work, groupErrors, groupErrors_renaming keys tasks]
  | combine left right =>
      simp only [KeyRenaming.work, groupErrors, groupErrors_renaming keys left,
        groupErrors_renaming keys right]
  | executionGroup groups path result children =>
      simp only [KeyRenaming.work, groupErrors, groupErrors_renaming keys children]
  | stream node items => simp only [KeyRenaming.work, groupErrors]
termination_by sizeOf original

example : groupErrors (eager deferredCaught).1.work = [2] := by cbv
example : groupErrors (scheduled deferredCaught).1.work = [1] := by cbv

-- No key map, even noninjective, can fix a retained payload's changed error count.
example (keys : Nat → Nat)
    : KeyRenaming.work keys (scheduled deferredCaught).1.work
      ≠ (eager deferredCaught).1.work := by
  intro same
  have counts := congrArg groupErrors same
  rw [groupErrors_renaming] at counts
  cbv at counts
  contradiction

private def streamedCaught : List Selection :=
  [Tests.field "users" requiredPair [.stream]]

private def itemErrors : Work → List Nat
  | .empty | .executionGroup _ _ _ _ => []
  | .declareGroups _ tasks => itemErrors tasks
  | .combine left right => itemErrors left ++ itemErrors right
  | .stream _ items => items.map (fun item => ScheduledErrors.countedErrors item.1.result)

-- Both nullable object items complete; each recursively cuts its own field scope.
example : itemErrors (eager streamedCaught).1.work = [2, 2] := by cbv
example : itemErrors (scheduled streamedCaught).1.work = [1, 1] := by cbv

private def strictSchema : GraphQL.Schema :=
  {
    Tests.schema with
      types :=
        .object
          {
            name := "StrictQuery",
            fields :=
              [{ name := "users", outputType := .list (.nonNull (.named "User")) }]
          }
        :: Tests.schema.types
  }

private def strictRun (cancel : Bool) (stream : Bool) :=
  let selections := [Tests.field "users" requiredPair (if stream then [.stream] else [])]
  let execute :=
    if cancel then
      ScheduledExecution.executeRootSelectionSetCore
    else
      executeRootSelectionSetCore
  (execute strictSchema Tests.resolvers [] 7 "StrictQuery" (.object "StrictQuery" 0)
    selections).run
    17

-- Ordinary list items also cut: the first non-null object failure skips the second item.
example : (strictRun false false).1.result = .ok ([("users", .null)], 4) := by cbv
example : (strictRun true false).1.result = .ok ([("users", .null)], 1) := by cbv

-- Stream-tail stopping is shared, but inner field cancellation changes the fatal payload.
example : itemErrors (strictRun false true).1.work = [2] := by cbv
example : itemErrors (strictRun true true).1.work = [1] := by cbv

-- A nullable resolver failure precedes the fatal cut in this completed scope.
private def priorResolvers : Resolvers Nat :=
  {
    Tests.resolvers with
      resolve :=
        fun parent name arguments source =>
          if name == "name" then
            none
          else
            Tests.resolvers.resolve parent name arguments source
      resolve_argumentsEquivalent := by
        intro parent name first later source equivalent
        split
        · rfl
        · exact Tests.resolvers.resolve_argumentsEquivalent parent name first later
            source equivalent
  }

private def completedPrior : List Selection :=
  [Tests.defer
    [Tests.field "user"
      [
        Tests.field "name",
        Tests.field "required",
        Tests.field "required" [] [] (some "later")
      ]]]

private def priorRun (cancel : Bool) :=
  let execute :=
    if cancel then
      ScheduledExecution.executeRootSelectionSetCore
    else
      executeRootSelectionSetCore
  (execute Tests.schema priorResolvers [] 7 "Query" (.object "Query" 0)
    completedPrior).run
    17

example : groupErrors (priorRun false).1.work = [3] := by cbv
example : groupErrors (priorRun true).1.work = [2] := by cbv

private def healthy : List Selection :=
  [
    Tests.field "user" [Tests.field "name"],
    Tests.field "values" [] [.stream],
    Tests.defer [Tests.field "b"]
  ]

-- Sanity check for the entire generated completion and supply, including mixed work.
example : scheduled healthy = eager healthy := by cbv

-- Exact root statement and a consumer on the actual generated output, without an
-- assumed WorkPositive or a preselected scheduled/eager correspondence.
example : ScheduledExecution.RecursiveScheduledPositivity :=
  ScheduledExecution.recursiveScheduledPositivity_holds

example (schema : GraphQL.Schema) (resolvers : Resolvers Nat)
    (variables : VariableValues) (fuel : Nat) (parentType : GraphQL.Name)
    (source : ResolverValue Nat) (selections : List Selection) (supply : Nat)
    : ((ScheduledExecution.executeRootSelectionSetCore schema resolvers variables fuel
          parentType source selections).run
        supply).1.result
      ≠ .error 0 := by
  intro failed
  have positive :=
    (ScheduledExecution.recursiveScheduledPositivity_holds Nat schema resolvers variables
      fuel parentType source selections supply).1 0 failed
  omega

#print axioms ScheduledExecution.planPositivity_holds
#print axioms ScheduledExecution.recursiveScheduledPositivity_holds
#print axioms ScheduledExecution.root_task_failure_positive

end AlternativeRecursiveCutChecks
