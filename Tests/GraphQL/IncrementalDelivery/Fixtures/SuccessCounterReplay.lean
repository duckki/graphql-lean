import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerExistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SelectedFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureAncestorReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SelectedGroupFailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InformativeFailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MixedFailureWitness
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Rejected dormant contributors retain counter tokens after overlapping failures. -/

namespace GraphQL.IncrementalDelivery.Tests.SuccessCounterReplay
open GraphQL.IncrementalDelivery.Execution
open ReferenceWorkQueue WorkQueueSemantics

private def selections : List Selection :=
  [
    defer
      [
        field "required" [] [] (some "second"),
        field "fail",
        field "required" [] [] (some "first")
      ]
      (some "A"),
    defer [field "fail", field "required" [] [] (some "first")] (some "B"),
    defer
      [
        field "a",
        defer
          [
            field "required" [] [] (some "second"),
            field "fail",
            field "required" [] [] (some "first")
          ]
          (some "C")
      ]
      (some "P")
  ]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def subsetTask : Occurrence := .executionGroup [1, 0]
private def supersetTask : Occurrence := .executionGroup [1, 1, 0]
private def supersetFailure : GraphEvent := .taskFailure supersetTask 1
private def subsetFailure : GraphEvent := .taskFailure subsetTask 1
private def inputs : List (List GraphEvent) := [[supersetFailure], [subsetFailure]]

private def current : State :=
  ((State.initialize (Work.fromExecution work)).runNormalized inputs).1

private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

private def a : DeliveryNode := { ref := 0, path := [], label := some (.string "A") }
private def b : DeliveryNode := { ref := 1, path := [], label := some (.string "B") }
private def parent : DeliveryNode := { ref := 2, path := [], label := some (.string "P") }
private def c : DeliveryNode := { ref := 3, path := [], label := some (.string "C") }

private theorem subset_known
    : TaskAt work subsetTask [0, 3] none (.object [] (.error 1)) := by
  refine ⟨[⟨a, []⟩, ⟨c, [parent]⟩], [], ⟨.error 1, some 1⟩, .empty, [], ?_, rfl, rfl⟩
  cbv

private theorem superset_known
    : TaskAt work supersetTask [0, 1, 3] none (.object [] (.error 1)) := by
  refine ⟨[⟨a, []⟩, ⟨b, []⟩, ⟨c, [parent]⟩], [], ⟨.error 2, some 1⟩, .empty, [], ?_, rfl, rfl⟩
  cbv

private theorem source_valid : ValidGraphEvents work inputs.flatten := by
  have first : ValidGraphEvents work [supersetFailure] :=
    .append .nil ⟨_, none, [], superset_known⟩ (by simp [GraphEvent.Fresh, GraphEvent.identities, supersetFailure])
      ⟨_, none, _, superset_known, by simp⟩
  exact .append first ⟨_, none, [], subset_known⟩
    (by
      simp [GraphEvent.Fresh, GraphEvent.identities, supersetFailure, subsetFailure, supersetTask, subsetTask])
    ⟨_, none, _, subset_known, by simp⟩

/-- Both computations remain started through the dormant shared owner. -/
theorem inputs_started : inputsStarted work inputs = true := by cbv

/-- The later source rejection is causally redundant, despite its retained task node.
Source start eligibility and licensed failure-cut accounting are distinct obligations.
-/
theorem later_task_already_cancelled
    : Causality.TaskCancelled work [supersetTask] (fun _ => False) subsetTask := by
  refine .owners ⟨none, _, subset_known⟩ (by simp) (by decide) ?_
  intro ref member
  exact .task ⟨none, _, superset_known⟩
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp)
    (by simp)

/-- The shared dormant group retains both rejected tasks' counter tokens. -/
theorem dormant_pending : (current.groupNode? 3).map GroupNode.pending = some 2 := by cbv

/-- Actual replay proves the lower bound against successful settlements alone. -/
theorem success_counter_bound : current.PendingBound (fun _ => True) [] := by
  have counted := generated.runNormalized_successLedger inputs source_valid inputs_started
  exact counted.pending

/-- Actual replay retains both rejections, including the causally redundant later one.
The certificate also excludes earlier failure contributors at unregistered group refs.
-/
theorem retained_failures : current.RetainedFailures work [subsetTask, supersetTask] := by
  have retained := generated.runNormalized_retainedFailures inputs source_valid inputs_started
  have inventory : (State.initialize (Work.fromExecution work)).objectFailureContributions
      inputs.flatten = [subsetTask, supersetTask] := by cbv
  rwa [inventory] at retained

/-- Even a causally redundant retained rejection keeps an actual live contributor. -/
theorem retained_task_owners : current.TaskOwnersPresent :=
  (generated.runNormalized_taskOwnerFrame inputs source_valid inputs_started).owners

/-- The second rejection adds no group cause, although the runtime retains its task. -/
theorem redundant_subset_cause : ¬InformativeFailure work [supersetTask] subsetTask := by
  intro informative
  obtain ⟨owners, ref, known, owner, healthy⟩ := informative
  obtain ⟨producer, payload, descriptor⟩ := known
  have same := (TaskAt.unique descriptor subset_known).1
  subst owners
  apply healthy
  exact .task ⟨none, _, superset_known⟩
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at owner
      rcases owner with rfl | rfl <;> simp)
    (by simp)

/-- Ancestor health survives actual replay, including the redundant retained rejection. -/
theorem root_ancestors_healthy
    : current.RootAncestorsHealthy work [subsetTask, supersetTask] := by
  have health := (generated.runNormalized_retiredHealth inputs source_valid inputs_started).2.1
  have inventory : (State.initialize (Work.fromExecution work)).objectFailureContributions
      inputs.flatten = [subsetTask, supersetTask] := by cbv
  rwa [inventory] at health

/-- Proof selection omits the redundant rejection and retains its original predecessor cut. -/
theorem selected_cuts
    : selectObjectFailureCuts work [] [(0, supersetTask), (2, subsetTask)]
      = [(0, supersetTask)] := by
  classical
  have informative : InformativeFailure work [] supersetTask := by
    refine ⟨[0, 1, 3], 0, ⟨none, _, superset_known⟩, by simp, ?_⟩
    intro failure
    exact failure.nonempty rfl
  simp [selectObjectFailureCuts, informative, redundant_subset_cause]

/-- The selected inventory preserves invalidation on both sides of the redundant cut. -/
theorem selected_boundary_causes (cut ref : Nat)
    : GroupInvalidated work (failedBefore [(0, supersetTask), (2, subsetTask)] cut) ref
      ↔ GroupInvalidated work (failedBefore [(0, supersetTask)] cut) ref := by
  have same := selectObjectFailureCuts_failedBefore_groupInvalidated work []
    [(0, supersetTask), (2, subsetTask)] cut ref (by simp)
  simpa only [List.nil_append, selected_cuts] using same

/-- Actual failed owner completions retain healthy ancestry at the source boundary. -/
theorem first_failure_ancestorHealth
    : GroupFailureAncestorsHealthy work [supersetTask]
        ((State.initialize (Work.fromExecution work)).handleGraphEvent
          supersetFailure).2 := by
  have first : ValidGraphEvents work ([] ++ [supersetFailure]) :=
    source_valid.prefix ⟨[subsetFailure], rfl⟩
  have health := generated.replayGraphEvents_next_failureAncestorsHealthy first (by cbv)
  have inventory : (State.initialize (Work.fromExecution work)).objectFailureContributions
      ([] ++ [supersetFailure]) = [supersetTask] := by cbv
  rw [inventory] at health
  exact health

private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]

private def parentResult : TaskResult :=
  { value := { deliveryGroups := [parent], path := [], data := [("a", .scalar "a")] } }

private def parentSuccess : GraphEvent := .taskSuccess parentTask parentResult
private def completedInputs : List (List GraphEvent) := inputs ++ [[parentSuccess]]

private theorem parent_known
    : TaskAt work parentTask [2] none (.object [] (.ok ([("a", .scalar "a")], 0))) := by
  refine ⟨[⟨parent, []⟩], [], ⟨.ok ([("a", .scalar "a")], 0), none⟩,
    .combine .empty .empty, [], ?_, rfl, rfl⟩
  cbv

private theorem completed_valid : ValidGraphEvents work completedInputs.flatten := by
  change ValidGraphEvents work (inputs.flatten ++ [parentSuccess])
  exact .append source_valid ⟨[2], none, parent_known, by cbv, by cbv⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, parentSuccess, parentTask, inputs,
      supersetFailure, subsetFailure, supersetTask, subsetTask])
    ⟨[2], none, _, parent_known, by simp⟩

private theorem completed_started : inputsStarted work completedInputs = true := by cbv

/-- Registration-order rejection replay reports the dormant child after parent completion. -/
theorem completed_child_failure
    : (((State.initialize (Work.fromExecution work)).runNormalized
          completedInputs).2.flatten.flatMap
        publicationAtoms)[4]?
      = some (.groupFailure c 1) := by cbv

/-- The earlier selected superset rejection explains the child's later replayed count.
The runtime keeps both rejections and selects its first registered failed task; the proof
inventory may omit that redundant task while preserving the same observable completion.
-/
theorem completed_child_selected_cause
    : NodeFailureCause work [supersetTask] c.ref 1 := by
  have cause := createWorkQueue_selectedObjectFailureCuts_nodeFailureCause generated
    completed_valid completed_started completed_child_failure
  have candidates : sourceObjectFailureCuts 0
      ((State.initialize (Work.fromExecution work)).eligibleFailureBlocks
        ((State.initialize (Work.fromExecution work)).sourceRunBlocks
          { active := (State.initialize (Work.fromExecution work)).initialGroups
              ++ (State.initialize (Work.fromExecution work)).initialStreams }
          completedInputs).2.2) = [(0, supersetTask), (2, subsetTask)] := by cbv
  dsimp only at cause
  rw [candidates, selected_cuts] at cause
  exact cause

/-- One informative cut accounts for all actual errors, including the child's later replay. -/
theorem completed_informative_inventory
    : CompleteFailureInventory work
        (((State.initialize (Work.fromExecution work)).runNormalized
            completedInputs).2.flatten.flatMap
          publicationAtoms) [(0, supersetTask)] := by
  have noStreams : StreamFailureCuts work
      (((State.initialize (Work.fromExecution work)).runNormalized completedInputs).2.flatten.flatMap
        publicationAtoms) [] := ⟨by cbv, by intro entry member; cases member⟩
  have inventory := createWorkQueue_completeInformativeFailureInventory generated
    completed_valid completed_started noStreams (by intro entry member; cases member)
  have candidates : sourceObjectFailureCuts 0
      ((State.initialize (Work.fromExecution work)).eligibleFailureBlocks
        ((State.initialize (Work.fromExecution work)).sourceRunBlocks
          { active := (State.initialize (Work.fromExecution work)).initialGroups
              ++ (State.initialize (Work.fromExecution work)).initialStreams }
          completedInputs).2.2) = [(0, supersetTask), (2, subsetTask)] := by cbv
  simpa only [informativeObjectFailureCuts, candidates, selected_cuts, mergeFailureCuts,
    List.merge]
    using inventory

/-- The actual completed replay has a licensed failure witness despite the redundant input. -/
theorem completed_failure_witness
    : ∃ matching failures,
        FailureWitness work (ConformancePlan.initialRefs work) matching
          ((ConformancePlan.initialQueue work).nonterminalAtoms completedInputs)
          failures := by
  obtain ⟨w, history, _, licensed⟩ := ConformancePlan.mixed_failureWitness_exists generated
    completed_valid completed_started
  rw [history] at licensed
  exact ⟨w.matching, w.failures, licensed⟩

end GraphQL.IncrementalDelivery.Tests.SuccessCounterReplay
