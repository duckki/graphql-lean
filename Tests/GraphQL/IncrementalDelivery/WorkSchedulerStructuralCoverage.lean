import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupMembershipOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredContributorPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupAncestorProducer
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionBoundaries
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Structural coverage includes tasks absent when the queue is created. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerStructuralCoverage
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : DeliveryNode := { ref := 0, path := [], label := some (.string "P") }

private def child : DeliveryNode :=
  { ref := 1, path := [.field "user"], label := some (.string "C") }

private def parentTask : Occurrence := .executionGroup [1, 0]

private def children : Execution.Work :=
  .combine
    (.combine .empty
      (.combine
        (.executionGroup [⟨child, [parent]⟩] [.field "user"]
          (.ok ([("name", .scalar "name1")], 0)) (.combine .empty .empty))
        .empty))
    .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨parent, []⟩] [] (.ok ([("user", .object [])], 0)) children)
      .empty)

private def result : TaskResult :=
  {
    value := { deliveryGroups := [parent], path := [], data := [("user", .object [])] },
    work := Work.fromExecution children [1, 0, 0]
  }

private def queue : State := State.initialize (Work.fromExecution work)

private theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [defer [field "user" [defer [field "name"] (some "C")]] (some "P")], ?_⟩
  cbv

private def childTask : Occurrence := .executionGroup [1, 0, 0, 0, 1, 0]

private def childResult : TaskResult :=
  {
    value :=
      {
        deliveryGroups := [child], path := child.path, data := [("name", .scalar "name1")]
      }
  }

private def received : List GraphEvent :=
  [.taskSuccess parentTask result, .taskSuccess childTask childResult]

private theorem child_known
    : TaskAt work childTask [child.ref] (some parentTask)
        (.object child.path (.ok (childResult.value.data, 0))) := by
  refine ⟨[⟨child, [parent]⟩], child.path, _, .combine .empty .empty, [parent.ref],
    ?_, rfl, rfl⟩
  cbv

private theorem valid : ValidGraphEvents work received := by
  have parentKnown : TaskAt work parentTask [parent.ref] none
      (.object [] (.ok ([("user", .object [])], 0))) := by
    refine ⟨[⟨parent, []⟩], [], _, children, [], ?_, rfl, rfl⟩
    cbv
  have first : ValidGraphEvents work [.taskSuccess parentTask result] :=
    .append .nil ⟨_, _, parentKnown, by cbv, by cbv⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, parentKnown, by intro source impossible; cases impossible⟩
  refine .append first ⟨_, _, child_known, by cbv, by cbv⟩ ?_ ?_
  · simp [GraphEvent.Fresh, GraphEvent.identities, parentTask, childTask]
  · refine ⟨_, _, _, child_known, ?_⟩
    intro source same
    cases same
    simp [GraphEvent.successes]

/-- A previously activated child's ancestor data is strictly earlier on the shared witness.
Witness: actual two-handler replay supplies the active-root boundary. The general ancestor
publication theorem derives the parent's earlier occurrence without assuming its stored
value, a parent completion notice, or any new source-order requirement.
-/
theorem active_child_ancestor_published
    : ∃ w : ConformancePlan.Witness,
        w.events
          = queue.nonterminalAtoms
              [[.taskSuccess parentTask result], [.taskSuccess childTask childResult]]
        ∧ Published w.matching (w.events.take 2) parentTask := by
  let inputs := [[GraphEvent.taskSuccess parentTask result], [.taskSuccess childTask childResult]]
  have source : ValidGraphEvents work inputs.flatten := valid
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, _⟩ :=
    ConformancePlan.mixed_groupReleaseCertificates generated source (by cbv)
  let origin : GroupPublicationOrigin
      { active := queue.initialGroups ++ queue.initialStreams }
      (queue.rawEventReplay inputs.flatten).2 2 child
      [childResult.value] :=
    {
      before := [.groupValues parent [result.value], .groupSuccess parent [child] []],
      group := child, values := [childResult.value], groups := [], streams := [],
      after := [], offset := 0, value := childResult.value,
      rawEq := by cbv, found := rfl, position := by cbv,
      ownerEq := by cbv, payloadEq := rfl
    }
  let boundary : GroupPublicationHandlerBoundary queue inputs.flatten
      origin.group origin.values (origin.before.flatMap WorkQueueEvent.objectValues).length :=
    {
      before := [.taskSuccess parentTask result], event := .taskSuccess childTask childResult,
      after := [], position := 0, sourceEq := rfl, atHandler := by cbv, count := by cbv
    }
  have selected : w.events[2]? = some (.groupValues child [{ path := child.path, data := [("name", .scalar "name1")], errors := 0, deliveryGroups := [child] }]) := by rw [history]; cbv
  have childKnown : NodeAt work child .group [parent.ref] (some parentTask) :=
    ⟨[1, 0, 0, 0, 1, 0], [⟨child, [parent]⟩], child.path, _, .combine .empty .empty,
      [parent.ref], ⟨child, [parent]⟩, by cbv, List.mem_cons_self, rfl, rfl⟩
  have parentKnown : TaskAt work parentTask [parent.ref] none
      (.object [] (.ok ([("user", .object [])], 0))) :=
    ⟨[⟨parent, []⟩], [], _, children, [], by cbv, rfl, rfl⟩
  exact ⟨
    w,
    history,
    ConformancePlan.Witness.groupPublication_activeAncestorProducerPublished
      generated source
      (by cbv)
      history ledger selected origin boundary
      (by cbv; exact .head _)
      (groupRecordAt_of_nodeAt childKnown)
      List.mem_cons_self parentKnown List.mem_cons_self
  ⟩

/-- Produced tasks retain their parent-before-child registry order under actual replay.
Witness: the source-valid registration-order theorem and unconditional membership-order
preservation apply to this generated fixture, including its initially absent child task.
-/
theorem produced_task_registration_order
    : ObjectProducersRegisteredBefore work (queue.replayGraphEvents received).tasks
      ∧ (queue.replayGraphEvents received).GroupMembershipOrder :=
  ⟨
    createWorkQueue_replayGraphEvents_objectProducersRegisteredBefore valid,
    (createWorkQueue_groupMembershipOrder _).replayGraphEvents received
  ⟩

/-- A produced task absent initially publishes before its successful group's closure.
Witness: the general structural-coverage theorem derives its registration, source success,
and storage on the joint replay ledger. No fixture-specific registration or lookup is
supplied; the raw output prefix contains the parent and then the child's value.
-/
theorem produced_contributor_covered
    : childTask ∉ queue.tasks.map Task.occurrence
      ∧ ∃ published : List ObjectPublication,
          queue.ReplayClosuresCovered received published
          ∧ ∃ value, (childTask, value) ∈ published.take 2 := by
  refine ⟨by cbv; intro impossible; cases impossible; contradiction, ?_⟩
  obtain ⟨published, _, _, covered, _⟩ :=
    generated.rawEventReplay_bufferedCoverage received valid (by cbv)
  refine ⟨published, covered, ?_⟩
  have carrier : (((State.initialize (Work.fromExecution work)).replayGraphEvents
      [.taskSuccess parentTask result]).handleGraphEvent
        (.taskSuccess childTask childResult)).2[1]?
      = some (.groupSuccess child [] []) := by cbv
  obtain ⟨value, delivered⟩ := generated.successfulCarrier_structuralContributor_covered
    (before := [.taskSuccess parentTask result]) valid (by cbv) covered
      carrier child_known List.mem_cons_self
  have count : (((State.initialize (Work.fromExecution work)).rawEventReplay
      [.taskSuccess parentTask result]).2.flatMap WorkQueueEvent.objectValues).length
        + (((((State.initialize (Work.fromExecution work)).replayGraphEvents
            [.taskSuccess parentTask result]).handleGraphEvent
              (.taskSuccess childTask childResult)).2.take 1).flatMap
                WorkQueueEvent.objectValues).length = 2 := by cbv
  rw [count] at delivered
  exact ⟨value, delivered⟩

/-- Healthy retirement accounts for a produced task on the same replay ledger.
Witness: the generic retirement theorem needs no stored-task lookup or completion-event
premise. Actual replay supplies healthy retirement for this generated child fixture.
-/
theorem produced_retirement_covered
    : ∃ published : List ObjectPublication,
        queue.ReplayClosuresCovered received published
        ∧ ∃ value, (childTask, value) ∈ published.take 2 := by
  obtain ⟨published, _, _, covered, _⟩ :=
    generated.rawEventReplay_bufferedCoverage received valid (by cbv)
  have carrier : Execution.WorkQueueEvent.groupSuccess child [] []
      ∈ ((queue.replayGraphEvents [.taskSuccess parentTask result]).handleGraphEvent
          (.taskSuccess childTask childResult)).2 := by
    cbv; exact .tail _ (.head _)
  obtain ⟨_, _, retired, healthy, _⟩ :=
    generated.replayGraphEvents_successfulCarrier_retiredHealthy
      (before := [.taskSuccess parentTask result]) valid (by cbv) carrier
  obtain ⟨value, delivered⟩ := generated.retired_structuralContributor_published valid
    (by cbv) covered child_known List.mem_cons_self retired healthy
  have count : ((queue.rawEventReplay received).2.flatMap WorkQueueEvent.objectValues).length
      = 2 := by cbv
  change (childTask, value) ∈ published.take
    ((queue.rawEventReplay received).2.flatMap WorkQueueEvent.objectValues).length at delivered
  rw [count] at delivered
  exact ⟨published, covered, value, delivered⟩

/-- Separate input batches account for a produced child on one licensed atomic witness.
Witness: the general mixed construction supplies all successful-group accounting. Its
notice-free child closure satisfies full admission without concrete registry or buffer
facts, and the same matching publishes the child strictly before that closure.
-/
theorem produced_group_atomic_admission
    : ∃ w : ConformancePlan.Witness,
        w.events
          = (ConformancePlan.initialQueue work).nonterminalAtoms
              [[.taskSuccess parentTask result], [.taskSuccess childTask childResult]]
        ∧ FailureWitness work (ConformancePlan.initialRefs work) w.matching w.events
            w.failures
        ∧ ConformancePlan.GroupSuccessesAccounted work w
        ∧ EventAllowed work (ConformancePlan.initialRefs work) w.matching
            (w.events.take 3) w.failures (.groupSuccess child [] [])
        ∧ Published w.matching (w.events.take 3) childTask := by
  let inputs := [[GraphEvent.taskSuccess parentTask result], [.taskSuccess childTask childResult]]
  have source : ValidGraphEvents work inputs.flatten := valid
  obtain ⟨w, history, _, announced, uncancelled, _, _, _, healthy, accounted, ledger⟩ :=
    ConformancePlan.mixed_groupAccountingCertificates generated source (by cbv)
  have selected : w.events[3]? = some (.groupSuccess child [] []) := by rw [history]; cbv
  exact ⟨
    w,
    history,
    ConformancePlan.failureWitness announced uncancelled,
    accounted,
    ConformancePlan.groupSuccess_withoutNotices_allowed generated source (by cbv) history
      healthy ledger selected,
    ConformancePlan.groupSuccess_objectContributorsPublished generated source (by cbv)
      history ledger selected child_known List.mem_cons_self
  ⟩

/-- The same admitted publication stays absent across later child integration and execution.
Witness: the canonical ledger identifies the first matched occurrence, then its source-prefix
exclusion theorem applies both immediately and after the child's separate input batch.
Neither absence conclusion is obtained by evaluating the fixture's concrete queue.
-/
theorem published_memberships_stay_absent
    : ∃ w : ConformancePlan.Witness,
        w.events
          = queue.nonterminalAtoms
              [[.taskSuccess parentTask result], [.taskSuccess childTask childResult]]
        ∧ ConformancePlan.GroupPublicationAdmission work w
        ∧ (queue.replayGraphEvents [.taskSuccess parentTask result]).TaskMembershipAbsent
            (w.matching 0)
        ∧ (queue.replayGraphEvents received).TaskMembershipAbsent (w.matching 0) := by
  let inputs := [[GraphEvent.taskSuccess parentTask result], [.taskSuccess childTask childResult]]
  have source : ValidGraphEvents work inputs.flatten := valid
  have started : inputsStarted work inputs = true := by cbv
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated source started
  obtain ⟨published, matching, absent⟩ := ledger.membershipsAbsent source started
  have selected : w.events[0]? = some (.groupValues parent [result.value]) := by
    rw [history]; cbv
  have matched := matching.atObject 0 parent [result.value] selected
  cases labels : published with
  | nil => simp [labels] at matched
  | cons head tail =>
      have same : head.1 = w.matching 0 := by simpa [labels] using matched
      refine ⟨w, history, admitted, ?_, ?_⟩
      · rw [← same]
        apply absent [.taskSuccess parentTask result]
          ⟨[.taskSuccess childTask childResult], rfl⟩
        have count
            : (((ConformancePlan.initialQueue work).rawEventReplay
                  [.taskSuccess parentTask result]).2.flatMap
                WorkQueueEvent.objectValues).length
              = 1 := by
          cbv
        rw [count, labels]; simp
      · rw [← same]
        apply absent received ⟨[], rfl⟩
        have count : (((ConformancePlan.initialQueue work).rawEventReplay received).2.flatMap
            WorkQueueEvent.objectValues).length = 2 := by cbv
        rw [count, labels]; simp

private def childDrainStart : State :=
  let current := queue.replayGraphEvents [.taskSuccess parentTask result]
  let node : TaskNode := { task := ⟨childTask, [child]⟩ }
  let stored := current.putTaskNode { node with value := some childResult.value }
  let prepared := (stored.maybeIntegrateWork childResult.work (some childTask)).1
  let released := node.task.groups.foldl successGroupStep (prepared, [], {})
  released.1.startNewWork released.2.2

/-- One internal boundary clears both an earlier source publication and this handler's value.
Witness: the shared mixed ledger supplies the exact handler slice; the general drain-prefix
theorem combines it with earlier source labels before any drain iteration is performed.
-/
theorem prior_and_current_publications_absent_before_drain
    : ∃ w : ConformancePlan.Witness,
      ∃ published : List ObjectPublication,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ObjectLedgerMatching work
            [[.taskSuccess parentTask result], [.taskSuccess childTask childResult]]
            w.events w.matching published
        ∧ published.length = 2
        ∧ ∀ publication ∈ published.take 2,
            childDrainStart.TaskMembershipAbsent publication.1 := by
  let inputs := [[GraphEvent.taskSuccess parentTask result], [.taskSuccess childTask childResult]]
  have source : ValidGraphEvents work inputs.flatten := valid
  have started : inputsStarted work inputs = true := by cbv
  obtain ⟨w, _, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated source started
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rwa [← inputsStarted_eq_batchesStarted])
  have size : published.length = 2 := by
    have lengths := congrArg List.length matching.rawValues
    simpa only [List.length_map] using lengths.trans (by cbv)
  refine ⟨w, published, admitted, matching, size, ?_⟩
  intro publication member
  have cleared := createWorkQueue_taskSuccess_drainMemberships
    (before := [.taskSuccess parentTask result]) (after := [])
    (incoming := { task := ⟨childTask, [child]⟩ }) covered source
      (by cbv) (by cbv) 0 (Nat.zero_le _) publication
  apply cleared
  change publication ∈ published.take 2
  exact member

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerStructuralCoverage
