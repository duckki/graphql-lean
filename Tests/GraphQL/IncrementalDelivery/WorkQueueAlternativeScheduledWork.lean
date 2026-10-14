import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledWorkCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledExecutor
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutKeySupply
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Constructed recursive Work witnesses for actual generated executions. The finite
examples cover changed retained payload counts, shifted surviving keys and nested stream
positions. They do not establish a general executor theorem or native error reporting. -/

namespace AlternativeScheduledWorkChecks

open GraphQL.IncrementalDelivery
open Execution WorkQueueSemantics AlternativeWorkQueue.NativeRefinement
open ScheduledErrors ScheduledWork

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

private def retainedDefer : List Selection :=
  [Tests.defer [Tests.field "user" requiredPair]]

private def retainedStream : List Selection :=
  [Tests.field "users" requiredPair [.stream]]

-- A retained defer payload changes 2→1, and its surviving child stream shifts 19→18.
-- One map preserves the original defer key 17 and maps the child stream 18→19.
private def changedCountAndKey : List Selection :=
  [Tests.defer
    [
      Tests.field "user" (requiredPair ++ [Tests.field "values" [] [.stream]]),
      Tests.field "values" [] [.stream]
    ]]

private def healthyNested : List Selection :=
  [Tests.field "users"
    [Tests.field "name", Tests.defer [Tests.field "values" [] [.stream]]]
    [.stream]]

private theorem retainedDefer_refines
    : CompletionRefines id (scheduled retainedDefer).1 (eager retainedDefer).1 := by
  cbv
  repeat first | constructor | trivial

private theorem retainedStream_refines
    : CompletionRefines id (scheduled retainedStream).1 (eager retainedStream).1 := by
  cbv
  repeat first | constructor | trivial

private theorem changedCountAndKey_refines
    : CompletionRefines (KeyRenaming.insertGap 18 1)
        (scheduled changedCountAndKey).1 (eager changedCountAndKey).1 := by
  cbv
  repeat first | constructor | trivial

private theorem healthyNested_refines
    : CompletionRefines id (scheduled healthyNested).1 (eager healthyNested).1 := by
  cbv
  repeat first | constructor | trivial

private def fatalDefer : List Selection := [Tests.defer requiredPair]

private theorem fatalDefer_refines
    : CompletionRefines id (scheduled fatalDefer).1 (eager fatalDefer).1 := by
  cbv
  repeat first | constructor | trivial

example : (scheduled changedCountAndKey).2 = 19 := by cbv
example : (eager changedCountAndKey).2 = 20 := by cbv

-- Applying the structural root uses these actual generated Work witnesses, not an
-- independent tree or a premise asserting the desired task/node correspondence.
example
    : ∀ occurrence owners producer payload,
        TaskAt (eager changedCountAndKey).1.work occurrence owners producer payload
        → ∃ before outcome,
            TaskAt (scheduled changedCountAndKey).1.work occurrence before producer
              outcome
            ∧ before.map (KeyRenaming.insertGap 18 1) = owners
            ∧ PayloadRefines (KeyRenaming.insertGap 18 1) outcome payload :=
  (recursiveWorkStructure_holds _ _ _ changedCountAndKey_refines.2).2.2.1

-- A count relation does not authorize inventing a different actual payload. The
-- soundness/coverage root intentionally pairs task witnesses from both trees.
example : PayloadRefines id (.object [] (.error 1)) (.object [] (.error 3)) := by
  apply PayloadRefines.object
  simp [ResultRefines, SameData, countedErrors]

example
    : ¬TaskAt (.executionGroup [] [] (.error 2) .empty)
        (.executionGroup []) [] none (.object [] (.error 3)) := by
  simp [TaskAt, Located, locateWork, locateWork.go, Work.executionGroup.injEq]

-- No extra/missing item, path change, fatal/success change or increased count is allowed.
example (node : DeliveryNode) (payload : Result ResponseValue)
    : ¬WorkRefines id (.stream node [(payload, .empty)]) (.stream node []) := by
  intro related
  cases related with
  | stream nested => cases nested

example : ¬WorkRefines id .empty (.combine .empty .empty) := by
  intro related
  cases related

example : ¬PayloadRefines id (.object [] (.error 1)) (.object [] (.ok ([], 1))) := by
  intro related
  cases related with
  | object payload => exact payload.1

example : ¬PayloadRefines id (.object [] (.error 2)) (.object [] (.error 1)) := by
  intro related
  cases related with
  | object payload =>
      have impossible := payload.2.1
      simp [countedErrors] at impossible

example : RecursiveWorkStructure := recursiveWorkStructure_holds

example : RecursiveWorkCausality := recursiveWorkCausality_holds

-- The same generated Work pair and one injective map cover every failure/publication
-- cut. This does not assume that an arbitrary such cut is source-admitted or native.
example (failed : List Occurrence) (published : Occurrence → Prop)
    : (∀ occurrence,
        Reachable (eager changedCountAndKey).1.work occurrence
        ↔ Reachable (scheduled changedCountAndKey).1.work occurrence)
      ∧ (∀ key,
          Causality.NodeFailed (eager changedCountAndKey).1.work failed published key
          ↔ ∃ before,
              KeyRenaming.insertGap 18 1 before = key
              ∧ Causality.NodeFailed (scheduled changedCountAndKey).1.work failed
                  published before)
      ∧ (∀ occurrence,
          Causality.TaskCancelled (eager changedCountAndKey).1.work failed published
            occurrence
          ↔ Causality.TaskCancelled (scheduled changedCountAndKey).1.work failed published
              occurrence) :=
  recursiveWorkCausality_holds _ (KeyRenaming.insertGap_injective 18 1) _ _
    changedCountAndKey_refines.2 failed published

private def fatalOccurrence : Occurrence := .executionGroup [1, 0]

private theorem scheduled_fatal_task
    : TaskAt (scheduled fatalDefer).1.work fatalOccurrence [17] none
        (.object [] (.error 1)) := by cbv; repeat first | constructor | trivial

private theorem scheduled_fatal_node
    : Causality.NodeFailed (scheduled fatalDefer).1.work [fatalOccurrence]
        (fun _ => False) 17 :=
  .task ⟨_, _, scheduled_fatal_task⟩ (by simp) (by simp)

-- This actual generated fatal task has payload 1 in the cut policy and 2 in eager Work.
-- Its node failure transports; changing the count does not change the cancellation cut.
example
    : Causality.NodeFailed (eager fatalDefer).1.work [fatalOccurrence] (fun _ => False)
        17 :=
  fatalDefer_refines.2.node_failed_forward (fun _ _ same => same) scheduled_fatal_node

example
    : Causality.TaskCancelled (eager fatalDefer).1.work [fatalOccurrence]
        (fun _ => False) fatalOccurrence := by
  apply fatalDefer_refines.2.task_cancelled_forward (fun _ _ same => same)
  exact .owners ⟨_, _, scheduled_fatal_task⟩ id (by simp)
    (by simpa using scheduled_fatal_node)

-- Publishing that same occurrence protects it in both policies, independently of counts.
example
    : ¬Causality.TaskCancelled (eager fatalDefer).1.work [fatalOccurrence]
        (fun occurrence => occurrence = fatalOccurrence) fatalOccurrence := by
  intro cancelled
  cases cancelled with
  | owners _ unpublished _ _ | producerFailed _ unpublished _
    | producerCancelled _ unpublished _ => exact unpublished rfl

#print axioms recursiveWorkStructure_holds
#print axioms recursiveWorkCausality_holds
#print axioms WorkRefines.renaming
#print axioms CompletionRefines.combine
#print axioms CompletionRefines.map
#print axioms CompletionRefines.catchNull
#print axioms CompletionRefines.nonNull
#print axioms PayloadRefines.failure_status
#print axioms retainedDefer_refines
#print axioms retainedStream_refines
#print axioms changedCountAndKey_refines
#print axioms healthyNested_refines

end AlternativeScheduledWorkChecks
