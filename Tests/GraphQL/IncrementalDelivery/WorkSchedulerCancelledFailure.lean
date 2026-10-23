import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Conformance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedTaskErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TerminalReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DescriptorMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootGroupCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingHealthy
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayCancellation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureOutput
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPublications
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Minimality
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles
import Tests.GraphQL.IncrementalDelivery.Execution
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! A late rejected task is retained even after its contributors are causally invalidated.
Dormant-owner release aggregates distinct cached task causes, independently of diagnostics. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerCancelledFailure
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated shared contributors with a failed defer ancestor
-----------------------------------------------------------------------------------------

private def root : DeliveryNode := { ref := 0, path := [], label := some (.string "R") }
private def parent : DeliveryNode := { ref := 1, path := [], label := some (.string "P") }
private def child : DeliveryNode := { ref := 2, path := [], label := some (.string "C") }
private def other : DeliveryNode := { ref := 3, path := [], label := some (.string "D") }
private def nested : DeliveryNode := { ref := 4, path := [], label := some (.string "E") }
private def firstTask : Occurrence := .executionGroup [1, 0]
private def secondTask : Occurrence := .executionGroup [1, 1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def data : List (Name × ResponseValue) := [("a", .scalar "a")]

private def work : Execution.Work :=
  .combine .empty
    (.declareGroups
      [
        ⟨root, []⟩,
        ⟨parent, []⟩,
        ⟨child, [parent]⟩,
        ⟨other, [parent]⟩,
        ⟨nested, [other, parent]⟩
      ]
      (.combine
        (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩, ⟨other, [parent]⟩] []
          ({ result := .error 1, cause := some 1 }) .empty)
        (.combine
          (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩, ⟨nested, [other, parent]⟩]
            [] ({ result := .error 2, cause := some 1 }) .empty)
          (.combine
            (.executionGroup [⟨parent, []⟩] [] ({ result := .ok (data, 0) })
              (.combine .empty .empty))
            .empty))))

private def first : GraphEvent := .taskFailure firstTask 1
private def second : GraphEvent := .taskFailure secondTask 1

private def finish : GraphEvent :=
  .taskSuccess parentTask
    {
      value := { deliveryGroups := [parent], path := [], data },
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def childNotice : GraphEvent := .groupFailure ⟨child, 2⟩
private def otherNotice : GraphEvent := .groupFailure ⟨other, 1⟩

private def inputs : List (List GraphEvent) :=
  [[first], [second], [finish, childNotice, otherNotice]]

/-- Execution generates two differently owned failing partitions sharing R and C.
Witness: the second task's other owner E is a child of the first task's owner D.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "first"), field "fail",
        field "required" [] [] (some "second")] (some "R"),
      defer [field "a",
        defer [field "required" [] [] (some "first"), field "fail",
          field "required" [] [] (some "second")] (some "C"),
        defer [field "required" [] [] (some "first"),
          defer [field "fail", field "required" [] [] (some "second")] (some "E")]
          (some "D")] (some "P")], ?_⟩
  cbv

/-- The host may still report the already-started task after its owners have failed.
Witness: the unchanged sequential start checker accepts the late settlement.
-/
theorem inputs_started : inputsStarted work inputs = true := by cbv

private theorem first_known
    : TaskAt work firstTask [root.ref, child.ref, other.ref] none
        (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 1, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

private theorem second_known
    : TaskAt work secondTask [root.ref, child.ref, nested.ref] none
        (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 2, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

private theorem parent_known
    : TaskAt work parentTask [parent.ref] none (.object [] (.ok (data, 0))) :=
  ⟨_, [], { result := .ok (data, 0) }, .combine .empty .empty, [], rfl, rfl, rfl⟩

/-- Both failures and the later parent success satisfy the unchanged source semantics.
Witness: fixed outcomes, fresh occurrences, and root structural producers.
-/
theorem source_valid : ValidGraphEvents work inputs.flatten := by
  have one : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, _, first_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first])
      ⟨_, _, _, first_known, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [first, second] :=
    .append one ⟨_, _, _, second_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first, second,
        firstTask, secondTask])
      ⟨_, _, _, second_known, by intro source impossible; cases impossible⟩
  have three : ValidGraphEvents work [first, second, finish] := .append two ⟨_, _, parent_known, rfl, rfl⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, first, second, finish,
      firstTask, secondTask, parentTask])
    ⟨_, _, _, parent_known, by intro source impossible; cases impossible⟩

  have four : ValidGraphEvents work [first, second, finish, childNotice] := .append three
    ⟨⟨[parent.ref], none, NodeAt.group (address := [1, 0])
      (group := ⟨child, [parent]⟩) (by rfl) (by simp)⟩, by decide⟩
    (by simp [childNotice, first, second, finish, GraphEvent.Fresh, GraphEvent.identities]) trivial
  exact .append four
    ⟨
      ⟨
        [parent.ref],
        none,
        NodeAt.group (address := [1, 0]) (group := ⟨other, [parent]⟩) (by rfl) (by simp)
      ⟩,
      by decide
    ⟩
    (by
      simp [otherNotice, childNotice, first, second, finish, child, other, GraphEvent.Fresh, GraphEvent.identities])
    trivial

private def initial : State := State.initialize (Work.fromExecution work)

private def correctedOutputs : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure root 1],
    [
      .groupValues parent [{ path := [], data, deliveryGroups := [parent] }],
      .groupSuccess parent [child, other] [],
      .groupFailure child 2,
      .groupFailure other 1,
      .workQueueTermination
    ]
  ]

/-- Normal parent release announces C and D before replaying their retained rejections. -/
theorem output : (initial.runNormalized inputs).2 = correctedOutputs := by cbv

/-- Sequential handlers preserve this result when all settlements share one host batch. -/
theorem batched_output
    : (initial.runNormalized [[first, second, finish, childNotice, otherNotice]]).2
      = [correctedOutputs.flatten] := by cbv

/-- Reversing the two rejections preserves C's two distinct cached reporting causes. -/
theorem reversed_output
    : inputsStarted work [[second], [first], [finish, childNotice, otherNotice]] = true
      ∧ (initial.runNormalized [[second], [first], [finish, childNotice, otherNotice]]).2
        = correctedOutputs := by
  cbv

/-- Presence accepts both rejections, including the causally redundant second one. -/
theorem contributing_failures
    : initial.objectFailureContributions inputs.flatten = [secondTask, firstTask] := by
  cbv

/-- Both rejected computations and C's full membership survive until ordinary activation. -/
theorem retained_rejections
    : let queue := (initial.runNormalized [[first], [second]]).1
      (queue.taskNode? firstTask).map TaskNode.rejection = some (some 1)
      ∧ (queue.taskNode? secondTask).map TaskNode.rejection = some (some 1)
      ∧ (queue.groupNode? child.ref).map (fun group => (group.tasks, group.pending))
        = some ([firstTask, secondTask], 2)
      ∧ (queue.groupNode? other.ref).map GroupNode.tasks = some [firstTask]
      ∧ (queue.groupNode? nested.ref).map GroupNode.tasks = some [secondTask] := by cbv

/-- The original source laws derive counter safety across every received outcome. -/
theorem complete_replay_pendingAccounting
    : (initial.runNormalized inputs).1.PendingAccounting work
        (GraphEvent.taskSettlements inputs.flatten) :=
  generated.runNormalized_pendingLedger inputs source_valid inputs_started

/-- Healthy counters use the success ledger, independently of retained rejected records. -/
theorem complete_replay_healthyCounters
    : (initial.runNormalized inputs).1.HealthyPendingTracks work
        (GraphEvent.groupSettlements inputs.flatten)
        (GraphEvent.failureSettlements inputs.flatten) :=
  (generated.runNormalized_healthyPendingAndLinks inputs source_valid inputs_started).1

/-- All healthy registered owners remain accounted for under the same accepted source. -/
theorem complete_replay_healthyOwners
    : (initial.runNormalized inputs).1.HealthyRegisteredTaskAccounting work
        (GraphEvent.groupSettlements inputs.flatten)
        (GraphEvent.failureSettlements inputs.flatten) :=
  (generated.runNormalized_healthyRegisteredOwners inputs source_valid inputs_started).2

/-- Rejection retention is derived from replay rather than assumed as source metadata. -/
theorem complete_replay_errorAccounting
    : (initial.runNormalized inputs).1.RetainedFailures work [secondTask, firstTask] := by
  have retained := generated.runNormalized_retainedFailures inputs source_valid inputs_started
  have inventory : GraphEvent.failureSettlements inputs.flatten = [secondTask, firstTask] := by cbv
  rwa [inventory] at retained

/-- Removing D traverses its still-unannounced child E after both rejections. -/
theorem retained_parent_removal_covers_child
    : let queue := (initial.runNormalized [[first], [second]]).1
      (queue.removeGroup other.ref).groupNode? nested.ref = none
      ∧ nested.ref ∉ (queue.removeGroup other.ref).rootGroups := by
  apply generated.runNormalized_removeGroup_covers [[first], [second]]
    (source_valid.prefix ⟨[finish, childNotice, otherNotice], rfl⟩)
  apply State.LiveDescendant.child (child := nested.ref)
  · cbv
  · simp [nested]
  · exact .self (by cbv)

/-- The full canonical proof admits and terminates this actual generated replay. -/
theorem output_admitted
    : AdmissibleRun work
        ((ConformancePlan.initialQueue work).normalizedHistory inputs) := by
  have nonempty : work.size ≠ 0 := by decide
  have initialized := generated.initializes nonempty
  obtain ⟨w, obligations⟩ := ConformancePlan.replayWitnessExists_holds work inputs
    ⟨nonempty, generated, initialized, source_valid, inputs_started⟩
  have explained := ConformancePlan.explains initialized obligations.announced
    obligations.uncancelled obligations.publications obligations.controls
  exact (ConformancePlan.run_iff_terminated explained obligations.batching
          (fun ended =>
            ConformancePlan.terminal (obligations.tasks ended)
              (obligations.nodes ended) (obligations.reported ended))).mpr
    (by cbv)

/-- The nested scope is covered by observable reports despite receiving no own ID. -/
theorem nested_reported : FailureReportedFor correctedOutputs.flatten nested.path := by
  exact ⟨
    other,
    1,
    by decide,
    by simp [other, nested],
    Or.inl (by simp [correctedOutputs])
  ⟩

private def aggregateOutputs : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure root 1],
    [
      .groupValues parent [{ path := [], data, deliveryGroups := [parent] }],
      .groupSuccess parent [child, other] [],
      .groupFailure child 3,
      .groupFailure other 1,
      .workQueueTermination
    ]
  ]

/-- Only the two failed object tasks can contribute to C's report. -/
private theorem child_reporting_bound {reported errors}
    (cause : NodeFailureCauses work reported child.ref errors)
    : errors ≤ 2 := by
  apply generated.nodeFailureCauses_count_le [firstTask, secondTask] ?_ cause
  intro occurrence owners producer payload known owner failed
  have token := known.observationToken
  simp [work, observationTokens] at token
  rcases token with rfl | rfl | rfl
  · simp [firstTask]
  · simp [secondTask]
  · have same := (known.unique parent_known).2.2
    rw [same] at failed
    cases failed

/-- Collected diagnostics cannot inflate two distinct unit causes into a count of three.
The bound holds for every matching, reporting inventory and batching. -/
theorem aggregate_not_valid
    : ¬ValidHistory work ⟨[root, parent], [], aggregateOutputs⟩ := by
  have excludes {events matching failures} (explained : Explains work [root, parent] []
      events matching failures) : .groupFailure child 3 ∉ events := by
    intro member
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨reported, _, _, allowed⟩ := explained.2.2
    have count := child_reporting_bound (allowed index _ selected).2.2.2
    omega
  rintro (⟨events, matching, failures, explained, batching⟩ |
    ⟨events, matching, failures, explained, _, batching⟩)
  · exact excludes explained ((batching.control_mem (by simp [IsValue])).mp
      (by simp [aggregateOutputs]))
  · have member := (batching.control_mem (event := .groupFailure child 3) (by simp [IsValue])).mp
      (by simp [aggregateOutputs])
    exact excludes explained (List.mem_append.mp member |>.resolve_right (by simp))

#print axioms output_admitted
#print axioms aggregate_not_valid

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerCancelledFailure
