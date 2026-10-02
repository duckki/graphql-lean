import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedProducerSource
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducedGroupCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorCoverageReplay
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A generated nested object buffers behind a blocker while its child waits for announcement. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerBufferedProducer
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def nestedSchema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          {
            name := "Query",
            fields :=
              [
                { name := "b", outputType := .named "String" },
                { name := "user", outputType := .named "User" }
              ]
          },
        .object
          {
            name := "User",
            fields :=
              [
                { name := "friend", outputType := .named "User" },
                { name := "name", outputType := .named "String" }
              ]
          }
      ]
  }

private def nestedResolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ name _ _ =>
        match name with
        | "user" | "friend" => some (.object "User" 1)
        | _ => some (.scalar name),
    resolve_argumentsEquivalent := by intros; rfl
  }

private def parent : DeliveryNode := { key := 0, path := [], label := some (.string "P") }

private def child : DeliveryNode :=
  { key := 1, path := [.field "user", .field "friend"], label := some (.string "C") }

private def parentTask : Occurrence := .executionGroup [0, 0, 1, 0]
private def childTask : Occurrence := .executionGroup [0, 0, 1, 0, 0, 0, 1, 0]
private def blockerTask : Occurrence := .executionGroup [1, 0]

private def childValue : ExecutionGroupValue :=
  {
    path := child.path,
    data := [("name", .scalar "name")],
    errors := 0,
    deliveryGroups := [child]
  }

private def parentValue : ExecutionGroupValue :=
  {
    path := [.field "user"],
    data := [("friend", .object [])],
    errors := 0,
    deliveryGroups := [parent]
  }

private def blockerValue : ExecutionGroupValue :=
  { path := [], data := [("b", .scalar "b")], errors := 0, deliveryGroups := [parent] }

private def children : Execution.Work :=
  .combine
    (.combine .empty
      (.combine
        (.executionGroup [⟨child, [parent]⟩] child.path (.ok (childValue.data, 0))
          (.combine .empty .empty))
        .empty))
    .empty

private def work : Execution.Work :=
  .combine
    (.combine
      (.combine (.combine .empty .empty)
        (.combine
          (.executionGroup [⟨parent, []⟩] parentValue.path (.ok (parentValue.data, 0))
            children)
          .empty))
      .empty)
    (.combine
      (.executionGroup [⟨parent, []⟩] [] (.ok (blockerValue.data, 0))
        (.combine .empty .empty))
      .empty)

private def parentResult : TaskResult :=
  { value := parentValue, work := Work.fromExecution children [0, 0, 1, 0, 0] }

private def childResult : TaskResult := { value := childValue }
private def blockerResult : TaskResult := { value := blockerValue }

private def before : List GraphEvent :=
  [.taskSuccess parentTask parentResult]

private def finish : GraphEvent := .taskSuccess blockerTask blockerResult
private def initial : State := State.initialize (Work.fromExecution work)
private def waiting : State := initial.replayGraphEvents before

private theorem generated : ExecutedWork work := by
  refine ⟨Nat, nestedSchema, nestedResolvers, [], 50, "Query", .object "Query" 0,
    [field "user" [field "name"],
      defer [field "b", field "user" [field "friend" [defer [field "name"] (some "C")]]]
        (some "P")], ?_⟩
  cbv

private theorem parent_known
    : TaskAt work parentTask [parent.key] none
        (.object parentValue.path (.ok (parentValue.data, 0))) := by
  refine ⟨[⟨parent, []⟩], parentValue.path, _, children, [], ?_, rfl, rfl⟩
  cbv

private theorem child_known
    : TaskAt work childTask [child.key] (some parentTask)
        (.object childValue.path (.ok (childValue.data, 0))) := by
  refine ⟨[⟨child, [parent]⟩], childValue.path, _, .combine .empty .empty, [parent.key],
    ?_, rfl, rfl⟩
  cbv

private theorem valid : ValidGraphEvents work (before ++ [finish]) := by
  have first : ValidGraphEvents work [.taskSuccess parentTask parentResult] :=
    .append .nil ⟨_, _, parent_known, by cbv, by cbv⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, parent_known, by intro source impossible; cases impossible⟩
  have blockerKnown : TaskAt work blockerTask [parent.key] none
      (.object [] (.ok (blockerValue.data, 0))) := by
    refine ⟨[⟨parent, []⟩], [], _, .combine .empty .empty, [], ?_, rfl, rfl⟩
    cbv
  exact .append first ⟨_, _, blockerKnown, by cbv, by cbv⟩
    (by simp [before, finish, GraphEvent.Fresh, GraphEvent.identities,
      parentTask, blockerTask])
    ⟨_, _, _, blockerKnown, by intro source impossible; cases impossible⟩

private theorem child_valid
    : ValidGraphEvents work
        (before ++ [finish] ++ [.taskSuccess childTask childResult]) :=
  .append valid ⟨_, _, child_known, by cbv, by cbv⟩
    (by simp [before, finish, GraphEvent.Fresh, GraphEvent.identities,
      parentTask, blockerTask, childTask])
    ⟨
      _,
      _,
      _,
      child_known,
      by
        intro source same
        cases same
        simp [before, finish, GraphEvent.successes]
    ⟩

/-- A genuinely new nested group is already below an active root before producer closure.
Witness: the general producer-supported integration theorem on generated work. Its input
coverage concerns only P; C is absent before integration and is not assumed covered.
-/
theorem produced_child_inherits_root_coverage
    : let integrated := (initial.maybeIntegrateWork parentResult.work (some parentTask)).1
      initial.groupNode? child.key = none
      ∧ ∃ root ∈ integrated.rootGroups, integrated.LiveDescendant root child.key := by
  intro integrated
  refine ⟨by cbv, ?_⟩
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have keys := createWorkQueue_groupKeysUnique (Work.fromExecution work)
  have registered := createWorkQueue_registration work
  have linked := createWorkQueue_parentLinksComplete (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)
  have producerMember : (⟨parentTask, [parent]⟩ : Task) ∈ initial.tasks := by
    cbv
    exact List.mem_cons_self
  have matching : (GraphEvent.taskSuccess parentTask parentResult).MatchesWork work :=
    ⟨_, _, parent_known, by cbv, by cbv⟩
  have member : (⟨child, some parent.key⟩ : Group) ∈ parentResult.work.groups := by
    cbv
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have contributing : ∃ task ∈ parentResult.work.tasks,
      child.key ∈ task.groups.map DeliveryNode.key := by
    refine ⟨⟨childTask, [child]⟩, ?_, ?_⟩
    · cbv
      exact List.mem_cons_self
    · exact List.mem_cons_self
  apply (createWorkQueue_healthyRegisteredTaskAccounting
          work).childGroup_integrated_root_coverage
    (createWorkQueue_healthyPendingTracks work)
    (createWorkQueue_fromSpec_registeredTasksMatch work) generated
    (createWorkQueue_groupNodesMatchWork work)
    (createWorkQueue_healthyRetiredAncestors generated)
    (createWorkQueue_cancelledRecordsSupported _ work []) linked keys registered.1
    registered.2 (createWorkQueue_parentRegistryClosed canonical) canonical producerMember
    (by simp) matching member contributing (fun invalid => invalid.nonempty rfl)
  · intro node present contributes _
    have same : node.group.node.key = parent.key := List.mem_singleton.mp contributes
    refine ⟨parent.key, ?_, ?_⟩
    · cbv
      exact List.mem_cons_self
    · rw [same]
      exact .self (same ▸ keys.groupNode?_of_mem present)
  · refine ⟨{ group := ⟨child, some parent.key⟩, tasks := [childTask], pending := 1 }, ?_⟩
    cbv

/-- P's object buffers until its independent blocker settles; only then can C start.
Witness: actual generated handlers and start checks. A child settlement at the first
boundary would violate the existing source-start premise, not expose an ordering bug.
-/
theorem buffered_release_output
    : (initial.rawEventReplay before).2 = []
      ∧ child.key ∉ waiting.rootGroups
      ∧ waiting.acceptsGraphEvent (.taskSuccess childTask childResult) = false
      ∧ (waiting.handleGraphEvent finish).2
        = [
          .groupValues parent [parentValue, blockerValue],
          .groupSuccess parent [child] []
        ]
      ∧ (waiting.handleGraphEvent finish).1.acceptsGraphEvent
          (.taskSuccess childTask childResult)
        = true := by
  refine ⟨by cbv, ?_, by cbv, by cbv, by cbv⟩
  cbv; intro impossible; cases impossible; contradiction

private theorem waitingChildLive : ∃ node, waiting.groupNode? child.key = some node := by
  refine ⟨{ group := ⟨child, some parent.key⟩, tasks := [childTask], pending := 1 }, ?_⟩
  cbv

private theorem waitingChildRegistered
    : (⟨childTask, [child]⟩ : Task) ∈ waiting.tasks := by
  cbv
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- A healthy latent child remains reachable even while its producer's value is buffered.
Witness: the general generated replay-coverage theorem, not an assumed child notice or
output-admission certificate. C is live but is not itself an active root at this boundary.
-/
theorem buffered_child_has_active_ancestor
    : child.key ∉ waiting.rootGroups
      ∧ ∃ root ∈ waiting.rootGroups, waiting.LiveDescendant root child.key := by
  have prior := valid.prefix (List.prefix_append before [finish])
  have coverage := generated.replayGraphEvents_healthyContributorsCovered before prior (by cbv)
  have noFailures : initial.objectFailureContributions before = [] := by cbv
  refine ⟨buffered_release_output.2.1, ?_⟩
  apply coverage ⟨childTask, [child]⟩ waitingChildRegistered child.key List.mem_cons_self
    ?_ waitingChildLive
  change ¬GroupInvalidated work (initial.objectFailureContributions before) child.key
  rw [noFailures]
  exact fun invalid => invalid.nonempty rfl

/-- A retained child remains unaccounted while its successful object producer is buffered.
Witness: actual replay supplies task provenance and successful registration prerequisites;
the general retained-contents rule excludes cancellation without producer publication.
This is the pre-announcement contents obligation, not premature notice eligibility.
-/
theorem buffered_child_unaccounted
    : ¬Published (fun _ => parentTask) [] parentTask
      ∧ ¬NodeAccounted work (fun _ => parentTask) [] [] child.key := by
  have prior := valid.prefix (List.prefix_append before [finish])
  have contents : RetainedNoticeContents work (fun _ => parentTask) [] [] before child := by
    have known : NodeAt work child .group [parent.key] (some parentTask) :=
      .group (address := [0, 0, 1, 0, 0, 0, 1, 0])
        (groups := [⟨child, [parent]⟩]) (path := child.path)
        (result := .ok (childValue.data, 0)) (children := .combine .empty .empty)
        (owners := [parent.key]) (by cbv) List.mem_cons_self
    let node : GroupNode :=
      { group := ⟨child, some parent.key⟩, tasks := [childTask], pending := 1 }
    refine ⟨
      ⟨[parent.key], some parentTask, known⟩,
      waiting,
      node,
      by cbv,
      rfl,
      .inl (by simp [node]),
      ?_,
      ?_,
      ?_,
      ?_,
      ?_
    ⟩
    · exact (State.replay_noticeTaskProvenance (createWorkQueue_groupMembershipSound _)
        (createWorkQueue_fromSpec_registeredTasksMatch work) before
        (fun _ member => prior.eachMatches member)).1
    · exact (State.replay_noticeTaskProvenance (createWorkQueue_groupMembershipSound _)
        (createWorkQueue_fromSpec_registeredTasksMatch work) before
        (fun _ member => prior.eachMatches member)).2
    · have supported := generated.replayGraphEvents_cachedAcceptedFailures prior (by cbv)
      change waiting.CachedFailuresSupported work (initial.objectFailureContributions before)
        at supported
      simpa only [show initial.objectFailureContributions before = [] from by cbv]
        using supported
    · exact (createWorkQueue_replayGraphEvents_producerOrder prior).1
    · simp [Published]
  refine ⟨by simp [Published], ?_⟩
  exact (contents.recorded_or_unaccounted generated prior
          (by intro cut occurrence member; cases member)
          (by simp [TaskCancelled])
          (by simp [NodeFailed])).resolve_left
    (by simp [HasRecordedFailure, failedBefore])

/-- Source accounting derives the buffered producer rather than assuming its lookup.
Witness: the common replay ledger and healthy P contribution give the general
output-or-buffer alternative. Empty earlier output excludes publication, leaving the
exact stored value and live structural contributor before the blocker input.
-/
theorem buffered_parent_derived
    : ∃ w : ConformancePlan.Witness,
        w.events = initial.nonterminalAtoms [before ++ [finish]]
        ∧ ∃ result node,
            GraphEvent.taskSuccess parentTask result ∈ before
            ∧ waiting.taskNode? parentTask = some node
            ∧ node.value = some result.value
            ∧ TaskHasOwners work parentTask (node.task.groups.map DeliveryNode.key)
            ∧ parent.key ∈ node.task.groups.map DeliveryNode.key
            ∧ parent.key
              ∈ waiting.groupNodes.map (fun owner => owner.group.node.key) := by
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger⟩ :=
    ConformancePlan.mixed_groupAccountingCertificates (inputs := [before ++ [finish]])
      generated valid (by cbv)
  obtain ⟨published, batched, _, _, _⟩ := ledger
  have replay : initial.ReplayClosuresCovered (before ++ [finish]) published := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, initial,
      ConformancePlan.initialQueue]
      using batched.flatten (by cbv)
  have source : GraphEvent.taskSuccess parentTask parentResult ∈ before := List.mem_cons_self
  have healthy : ¬GroupRecordInvalidated work (initial.objectFailureContributions before)
      parent.key := by
    intro failed
    exact failed.nonempty (by cbv)
  have prior := generated.healthy_success_published_or_buffered
    (valid.prefix (List.prefix_append before [finish])) (by cbv)
    (replay.prefix before [finish]) parent_known List.mem_cons_self healthy source
  refine ⟨w, history, ?_⟩
  rcases prior with emitted | buffered
  · change (parentTask, parentResult.value) ∈ published.take
      ((initial.rawEventReplay before).2.flatMap WorkQueueEvent.objectValues).length at emitted
    simp only [buffered_release_output.1, List.flatMap_nil, List.length_nil,
      List.take_zero, List.not_mem_nil] at emitted
  · obtain ⟨node, facts⟩ := buffered
    exact ⟨parentResult, node, source, facts⟩

/-- The eventual C carrier derives an earlier producer input from source readiness.
Witness: after P's release the child input is accepted, and generic carrier accounting
identifies its object producer in the strict source prefix. No lookup premise is supplied.
-/
theorem child_carrier_producer_source
    : ∃ result, GraphEvent.taskSuccess parentTask result ∈ before ++ [finish] := by
  apply generated.successfulCarrier_objectProducer_before child_valid (by cbv)
    (group := child) (groups := []) (streams := []) ?_ child_known List.mem_cons_self
  change Execution.WorkQueueEvent.groupSuccess child [] []
    ∈ ((initial.replayGraphEvents (before ++ [finish])).handleGraphEvent
      (.taskSuccess childTask childResult)).2
  cbv
  exact .tail _ (.head _)

/-- The shared replay ledger places P's value strictly before C's object block.
Witness: the task-handler theorem derives either prior retirement or internal-drain
coverage without asking which activation path occurred. This generated fixture follows
the already-active branch after its blocker; the proof uses no stored-value premise.
-/
theorem child_value_has_prior_producer
    : ∃ published : List ObjectPublication,
        initial.ReplayClosuresCovered
          (before ++ [finish] ++ [.taskSuccess childTask childResult]) published
        ∧ ∃ value, (parentTask, value) ∈ published.take 2 := by
  let events := before ++ [finish] ++ [GraphEvent.taskSuccess childTask childResult]
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger⟩ :=
    ConformancePlan.mixed_groupAccountingCertificates (inputs := [events])
      generated child_valid (by cbv)
  obtain ⟨published, batched, _, _, _⟩ := ledger
  have replay : initial.ReplayClosuresCovered events published := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, initial,
      ConformancePlan.initialQueue]
      using batched.flatten (by cbv)
  have nodeKnown : NodeAt work child .group [parent.key] (some parentTask) :=
    ⟨[0, 0, 1, 0, 0, 0, 1, 0], [⟨child, [parent]⟩], child.path, _,
      .combine .empty .empty, [parent.key], ⟨child, [parent]⟩,
      by cbv, List.mem_cons_self, rfl, rfl⟩
  obtain ⟨value, delivered⟩ := generated.taskSuccess_ancestorProducer_beforeValue child_valid
    (by cbv) replay (position := 0) (group := child) (values := [childValue])
    (by cbv) child_known List.mem_cons_self (groupRecordAt_of_nodeAt nodeKnown)
    List.mem_cons_self parent_known List.mem_cons_self
  exact ⟨published, replay, value, delivered⟩

/-- The nested object's value satisfies full admission on the general mixed witness.
Witness: invoke the generic construction on the real parent/blocker/child sequence and
select its child atom. Producer readiness, freshness, noncancellation, and wire ownership
are all derived; the fixture supplies only generated work and valid started inputs.
-/
theorem child_value_admitted
    : ∃ w : ConformancePlan.Witness,
        w.events
          = initial.nonterminalAtoms
              [before ++ [finish] ++ [.taskSuccess childTask childResult]]
        ∧ EventAllowed work (ConformancePlan.initialKeys work) w.matching
            (w.events.take 3) w.failures
            (.groupValues child [childValue]) := by
  obtain ⟨w, history, _, _, _, _, _, _, _, _, _, _, _, _, publications⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates
      (inputs := [before ++ [finish] ++ [GraphEvent.taskSuccess childTask childResult]])
      generated (by simpa using child_valid) (by cbv)
  exact ⟨w, history, publications 3 child [childValue] (by rw [history]; cbv)⟩

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerBufferedProducer
