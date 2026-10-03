import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicItemNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeItemPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.LeadingNoticeAncestors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorSemantics
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshGroupPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPresenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalNoticeCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshGroupNoticeAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshRegionCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeSourceFreshness
import Tests.GraphQL.IncrementalDelivery.Execution

/-! An item-produced defer patch follows its exact item on the shared conformance witness. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerItemProducedObjects
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def stream : DeliveryNode := { ref := 0, path := [.field "users"] }

private def child (index : Nat) : DeliveryNode :=
  {
    ref := index + 1, path := [.field "users", .index index], label := some (.string "C")
  }

private def children (index : Nat) : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨child index, []⟩] (child index).path
        (.ok ([("name", .scalar ("name" ++ toString (index + 1)))], 0))
        (.combine .empty .empty))
      .empty)

private def entries : List (Result ResponseValue × Execution.Work) :=
  [(.ok (.object [], 0), children 0), (.ok (.object [], 0), children 1)]

private def work : Execution.Work :=
  .combine (.combine (.combine .empty (.stream stream entries)) .empty) .empty

private def producer : Occurrence := .item [0, 0, 1] 0
private def occurrence : Occurrence := .executionGroup [0, 0, 1, 0, 1, 0]

private def item : StreamItem :=
  ⟨producer, ⟨.object [], 0⟩, Work.fromExecution (children 0) [0, 0, 1, 0]⟩

private def result : TaskResult :=
  {
    value :=
      {
        deliveryGroups := [child 0],
        path := (child 0).path,
        data := [("name", .scalar "name1")]
      },
    work := Work.fromExecution (.combine .empty .empty) [0, 0, 1, 0, 1, 0, 0]
  }

private def received : List GraphEvent :=
  [.streamItems stream [item], .taskSuccess occurrence result]

private def initial : State := State.initialize (Work.fromExecution work)

private theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [field "users" [defer [field "name"] (some "C")] [.stream]], ?_⟩
  cbv

private theorem stream_located
    : Located work [0, 0, 1] (.stream stream entries) none [] := by cbv

private theorem known
    : TaskAt work occurrence [(child 0).ref] (some producer)
        (.object (child 0).path (.ok ([("name", .scalar "name1")], 0))) :=
  .executionGroup (groups := [⟨child 0, []⟩]) (children := .combine .empty .empty)
    (owners := []) (by cbv)

private theorem valid : ValidGraphEvents work received := by
  have first : ValidGraphEvents work [.streamItems stream [item]] := by
    refine .append .nil ?_ ?_ ?_
    · intro entry member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_, _, TaskAt.item stream_located rfl, by cbv⟩
    · simp [GraphEvent.Fresh, GraphEvent.identities, item]
    · exact ⟨_, _, _, _, stream_located, by simp, by simp,
        (by intro source impossible; cases impossible), rfl⟩
  refine .append first ⟨_, _, known, by cbv, by cbv⟩ ?_ ?_
  · simp [GraphEvent.Fresh, GraphEvent.identities, item, occurrence, producer]
  · refine ⟨_, _, _, known, ?_⟩
    intro source same
    cases same
    simp [GraphEvent.successes, item]

/-- Item-produced object admission uses the exact shared source occurrence, not its payload.
Witness: the mixed construction retains one matching and source ledger. Its object label
must name the only task-success input; the generic item-producer theorem places the first
stream item strictly before that object's publication, across separate response batches.
-/
theorem producer_published_before_child
    : ∃ w : ConformancePlan.Witness,
        w.events
          = initial.nonterminalAtoms
              [[.streamItems stream [item]], [.taskSuccess occurrence result]]
        ∧ ConformancePlan.BufferedClosureLedger work
            [[.streamItems stream [item]], [.taskSuccess occurrence result]] w
        ∧ w.matching 1 = occurrence
        ∧ Published w.matching (w.events.take 1) producer := by
  let inputs := [[GraphEvent.streamItems stream [item]], [.taskSuccess occurrence result]]
  have source : ValidGraphEvents work inputs.flatten := valid
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, releases⟩ :=
    ConformancePlan.mixed_groupReleaseCertificates generated source (by cbv)
  have selected : w.events[1]? = some (.groupValues (child 0) [result.value]) := by
    rw [history]; cbv
  have retained := ledger
  obtain ⟨_, _, exactLedger, _, _⟩ := retained
  have raw : ((initial.rawEventReplay inputs.flatten).2.flatMap
      WorkQueueEvent.objectValues)[((w.events.take 1).flatMap normalizedObjectValues).length]?
      = some result.value := by
    rw [history]
    cbv
  obtain ⟨supplied, member, _, _⟩ := exactLedger.source_at selected raw
  have identity : w.matching 1 = occurrence := by
    have same : w.matching 1 = occurrence ∧ supplied = result := by
      simpa [inputs] using member
    exact same.1
  have produced : TaskHasProducer work (w.matching 1) (some producer) := by
    rw [identity]
    exact ⟨_, _, known⟩
  have published := releases.itemProducerPublished generated source (by cbv) history ledger
    selected produced
  exact ⟨w, history, ledger, identity, published⟩

/-- An item-produced object's patch satisfies full admission across response batches.
Witness: the general mixed construction derives the exact object rule from generated,
valid started inputs; no fixture-specific producer, matching, or owner premise is added.
-/
theorem item_produced_value_admitted
    : ∃ w : ConformancePlan.Witness,
        w.events
          = initial.nonterminalAtoms
              [[.streamItems stream [item]], [.taskSuccess occurrence result]]
        ∧ EventAllowed work (ConformancePlan.initialRefs work) w.matching
            (w.events.take 1) w.failures
            (.groupValues (child 0) [result.value]) := by
  obtain ⟨w, history, _, _, _, _, _, _, _, _, _, _, _, _, publications⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates
      (inputs := [[.streamItems stream [item]], [.taskSuccess occurrence result]])
      generated valid (by cbv)
  exact ⟨w, history, publications 1 (child 0) [result.value] (by rw [history]; cbv)⟩

private def secondItem : StreamItem :=
  ⟨.item [0, 0, 1] 1, ⟨.object [], 0⟩, Work.fromExecution (children 1) [0, 0, 1, 1]⟩

private def wireValue : StreamItemValue := ⟨.object [], 0⟩

private theorem secondMatches
    : (GraphEvent.streamItems stream [secondItem]).MatchesWork work := by
  intro entry member
  obtain rfl := List.mem_singleton.mp member
  exact ⟨_, _, TaskAt.item stream_located rfl, by cbv⟩

private theorem valid_with_second
    : ValidGraphEvents work (received ++ [.streamItems stream [secondItem]]) := by
  apply ValidGraphEvents.append valid secondMatches
  · simp [GraphEvent.Fresh, GraphEvent.identities, received, item, secondItem,
      occurrence, producer]
  · refine ⟨_, _, _, _, stream_located, by simp, (by cbv; intro impossible; cases impossible),
      (by intro source impossible; cases impossible), ?_⟩
    cbv

/-- A later item cannot repeat a group notice from the first item and its child closure.
Witness: old registrations exclude the leading item frontier, while permanent ancestry
excludes every later drain notice, even though the earlier child has already closed.
-/
theorem second_item_does_not_reannounce {ref}
    (announced
      : ref
        ∈ initial.rootGroups
          ++ (initial.rawEventReplay received).2.flatMap rawGroupNoticeRefs)
    : ref
      ∉ ((initial.replayGraphEvents received).streamItems stream [secondItem]).2.flatMap
          rawGroupNoticeRefs :=
  generated.streamItems_noEarlierGroupNotice (before := received)
    (fun _ member => valid.eachMatches member) secondMatches announced

/-- The second item in one batch contributes its own concrete child-notice boundary.
Witness: recover the introducing input from the actual metadata fold; exact reduction
only selects the emitted notice, rather than supplying the boundary's contents.
-/
theorem second_item_notice_origin
    : ∃ earlier supplied later,
        [item, secondItem] = earlier ++ supplied :: later
        ∧ let boundary := initial.preparedStreamItems earlier
          child 1
          ∈ ((boundary.maybeIntegrateWork supplied.work).1.pruneEmptyGroups
              (boundary.maybeIntegrateWork supplied.work).2.newGroups).2 := by
  exact initial.streamItemFold_noticeOrigin [item, secondItem]
    (by cbv; exact .tail _ (.head _))

/-- A later item's noticed child excludes an earlier child's actual published occurrence.
Witness: the canonical mixed witness supplies its original ledger. The generic item-notice
theorem recovers the retained record and excludes the earlier patch without choosing a
new matching or assuming notice eligibility.
-/
theorem later_item_notice_excludes_prior_publication
    : ∃ w : ConformancePlan.Witness,
      ∃ published : List ObjectPublication,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ObjectLedgerMatching work [received ++ [.streamItems stream [secondItem]]]
            w.events w.matching published
        ∧ ∃ earlier supplied later,
            [secondItem] = earlier ++ supplied :: later
            ∧ let current := initial.replayGraphEvents received
              let boundary :=
                (current.preparedStreamItems earlier).integrateStreamItem supplied
              ∃ node,
                boundary.groupNode? (child 1).ref = some node
                ∧ node.group.node = child 1
                ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
                ∧ (∀ publication ∈ published.take 1, publication.1 ∉ node.tasks)
                ∧ ∀ task ∈ node.tasks, ¬Published w.matching (w.events.take 3) task := by
  have source := valid_with_second
  obtain ⟨w, history, _, _, _, _, _, streamReady, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [received ++ [GraphEvent.streamItems stream [secondItem]]])
      (by simpa using source) (by cbv)
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rw [← inputsStarted_eq_batchesStarted]; cbv)
  have carrier := (initial.replayGraphEvents received).streamItems_noticeGroups
    stream [secondItem] (index := 0) (emitted := stream) (values := [secondItem.value])
    (groups := [child 1]) (streams := []) (by cbv)
  have atomCount : ((w.events.take 3).flatMap normalizedObjectValues).length = 1 := by
    rw [history]
    cbv
  have sourceCount : ((initial.rawEventReplay received).2.flatMap
      WorkQueueEvent.objectValues).length = 1 := by cbv
  obtain ⟨earlier, supplied, later, splitItems, _, node, found, same,
      contents, excluded, unpublished⟩ :=
    generated.streamItems_leadingNotice_unpublished (before := received) (after := [])
      (child := child 1) (index := 3) covered source matching admitted streamReady
      (atomCount.trans sourceCount.symm) (carrier.2.2 ▸ List.mem_cons_self)
  refine ⟨w, published, admitted, matching, earlier, supplied, later, splitItems,
    node, found, same, contents, ?_, unpublished⟩
  simpa only [atomCount] using excluded

/-- The actual atomic notice obtains its retained node without a supplied boundary/count.
Witness: the end-to-end item-notice theorem recovers the source handler and integration
prefix on the original mixed matching; this fixture only selects the emitted carrier.
-/
theorem atomic_item_notice_unpublished
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[3]? = some (.streamValues stream [wireValue] [child 1] [])
        ∧ ∃ queue : State,
          ∃ node : GroupNode,
            queue.groupNode? (child 1).ref = some node
            ∧ node.group.node = child 1
            ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
            ∧ ∀ task ∈ node.tasks, ¬Published w.matching (w.events.take 3) task := by
  let inputs := [received ++ [GraphEvent.streamItems stream [secondItem]]]
  have source : ValidGraphEvents work inputs.flatten := by simpa [inputs] using valid_with_second
  obtain ⟨w, history, _, _, _, _, _, streamReady, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated source (by cbv)
  have selected : w.events[3]? = some (.streamValues stream [wireValue] [child 1] []) := by
    rw [history]
    cbv
  obtain ⟨before, sourceStream, items, after, earlier, supplied, later,
      _, _, _, _, node, found, same, contents, unpublished⟩ :=
    ConformancePlan.itemGroupNotice_unpublished generated source (by cbv) history ledger
      admitted streamReady selected List.mem_cons_self
  exact ⟨w, admitted, selected, _, node, found, same, contents, unpublished⟩

/-- A later item notice retains tasks and cut-supported caches on one canonical witness.
Witness: the joint contents theorem recovers the actual second item and its retained
record after the earlier item's child publication; no boundary or count is supplied.
-/
theorem atomic_item_notice_contents
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ RetainedNoticeContents work w.matching (w.events.take 3)
            (failedBefore w.failures 3)
            (received ++ [GraphEvent.streamItems stream [secondItem]]) (child 1) := by
  let inputs := [received ++ [GraphEvent.streamItems stream [secondItem]]]
  have source : ValidGraphEvents work inputs.flatten := by simpa [inputs] using valid_with_second
  obtain ⟨w, history, _, _, _, _, _, streamReady, _, _, ledger, _, _, _, admitted,
    streamCuts, _, exactCuts⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates_with_cuts generated source (by cbv)
  have selected : w.events[3]? = some (.streamValues stream [wireValue] [child 1] []) := by
    rw [history]
    cbv
  exact ⟨
    w,
    admitted,
    ConformancePlan.itemGroupNotice_contents generated source
      (by cbv)
      history ledger admitted streamReady
      (streamCuts := streamCuts)
      (by rw [exactCuts]; exact mergeFailureCuts_partition _ _)
      selected List.mem_cons_self
  ⟩

/-- Multiple item atoms retain all group notices only on their final carrier.
Witness: the generic joint-prefix theorem recovers one source position with zero prior
objects and both included items; there are no child-stream notices in this fixture.
-/
theorem group_only_carrier_joint_prefix
    : ∃ position values,
        [Execution.WorkQueueEvent.streamValues stream [wireValue, wireValue]
            [child 0, child 1] []][position]?
          = some (.streamValues stream values [child 0, child 1] [])
        ∧ position = 0
        ∧ values.length = 2 := by
  obtain ⟨position, values, selected, _, _⟩ := publicationAtoms_noticeCarrier_prefix
    [Execution.WorkQueueEvent.streamValues stream [wireValue, wireValue]
      [child 0, child 1] []]
    (index := 1) (owner := stream) (items := [wireValue])
    (groups := [child 0, child 1]) (streams := []) (child := child 1)
    (by rfl) (by simp)
  have zero : position = 0 := by
    have bounded := (List.getElem?_eq_some_iff.mp selected).1
    simp only [List.length_cons, List.length_nil] at bounded
    omega
  subst position
  have same := Execution.WorkQueueEvent.streamValues.inj (Option.some.inj selected)
  exact ⟨0, values, selected, rfl, by rw [← same.2.1]; rfl⟩

/-- A later item's child notice includes its own producer, not a later-source approximation.
Witness: the canonical witness's notice theorem recovers registration and the exact raw
item boundary. The fixture supplies only its descriptor and actual observed carrier.
-/
theorem atomic_notice_itemProducer_published
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[3]? = some (.streamValues stream [wireValue] [child 1] [])
        ∧ Published w.matching (w.events.take 4) secondItem.occurrence := by
  let inputs := [received ++ [GraphEvent.streamItems stream [secondItem]]]
  have source : ValidGraphEvents work inputs.flatten := by simpa [inputs] using valid_with_second
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated source (by cbv)
  have selected : w.events[3]? = some (.streamValues stream [wireValue] [child 1] []) := by
    rw [history]
    cbv
  have located : NodeAt work (child 1) .group [] (some secondItem.occurrence) :=
    NodeAt.group (address := [0, 0, 1, 1, 1, 0])
      (groups := [⟨child 1, []⟩]) (path := (child 1).path)
      (result := .ok ([("name", .scalar "name2")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  exact ⟨
    w,
    admitted,
    selected,
    w.groupNotice_itemProducerPublished generated source (by cbv) history ledger selected
      located (by simp [groupNoticeRefs])
  ⟩

private theorem valid_batched
    : ValidGraphEvents work [.streamItems stream [item, secondItem]] := by
  refine .append .nil ?_ ?_ ?_
  · intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, _, TaskAt.item stream_located rfl, by cbv⟩
    · exact secondMatches _ List.mem_cons_self
  · simp [GraphEvent.Fresh, GraphEvent.identities, item, secondItem, producer]
  · refine ⟨_, _, _, _, stream_located, by simp, by simp,
      (by intro source impossible; cases impossible), ?_⟩
    cbv

/-- A two-item carrier publishes both child producers before announcing their group notices.
Witness: the same general bridge handles the earlier atom and the carrier's own final
item. Neither whole-source publication nor equality of the repeated wire item values is
used to choose the producers.
-/
theorem batched_notice_itemProducers_published
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[1]? = some (.streamValues stream [wireValue] [child 0, child 1] [])
        ∧ Published w.matching (w.events.take 2) producer
        ∧ Published w.matching (w.events.take 2) secondItem.occurrence := by
  let inputs := [[GraphEvent.streamItems stream [item, secondItem]]]
  have source : ValidGraphEvents work inputs.flatten := valid_batched
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated source (by cbv)
  have selected : w.events[1]?
      = some (.streamValues stream [wireValue] [child 0, child 1] []) := by
    rw [history]
    cbv
  have first : NodeAt work (child 0) .group [] (some producer) :=
    NodeAt.group (address := [0, 0, 1, 0, 1, 0])
      (groups := [⟨child 0, []⟩]) (path := (child 0).path)
      (result := .ok ([("name", .scalar "name1")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  have second : NodeAt work (child 1) .group [] (some secondItem.occurrence) :=
    NodeAt.group (address := [0, 0, 1, 1, 1, 0])
      (groups := [⟨child 1, []⟩]) (path := (child 1).path)
      (result := .ok ([("name", .scalar "name2")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  exact ⟨
    w,
    admitted,
    selected,
    w.groupNotice_itemProducerPublished generated source (by cbv) history ledger selected
      first (by simp [groupNoticeRefs]),
    w.groupNotice_itemProducerPublished generated source (by cbv) history ledger selected
      second (by simp [groupNoticeRefs])
  ⟩

/-- A later item's notice is fully eligible on the canonical mixed witness.
Witness: the general eligibility bridge derives producer publication, retained-task
accounting, failure safety, and freshness. In particular, freshness follows from actual
replay separation after the earlier child's publication and closure, not fixture reduction.
-/
theorem atomic_item_notice_canAnnounce
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[3]? = some (.streamValues stream [wireValue] [child 1] [])
        ∧ ∃ birth,
            NodeAt work (child 1) .group [] birth
            ∧ CanAnnounce work (ConformancePlan.initialRefs work) w.matching
                (w.events.take 3 ++ [.streamValues stream [wireValue] [] []])
                (w.failures.filter (fun entry => entry.1 ≤ 3)) (child 1) .group []
                birth := by
  let inputs := [received ++ [GraphEvent.streamItems stream [secondItem]]]
  have source : ValidGraphEvents work inputs.flatten := by simpa [inputs] using valid_with_second
  obtain ⟨w, history, _, announced, _, failures, streams, streamReady, _, groups,
    ledger, _, support, _, admitted, safe, streamCuts, cuts, exactCuts⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates_with_noticeSafety
      generated source (by cbv)
  have selected : w.events[3]? = some (.streamValues stream [wireValue] [child 1] []) := by
    rw [history]
    cbv
  have partition := exactCuts ▸ mergeFailureCuts_partition _ _
  have contents := ConformancePlan.itemGroupNotice_contents generated source (by cbv)
    history ledger admitted streamReady (streamCuts := streamCuts) partition selected
    (child := child 1) List.mem_cons_self
  have located : NodeAt work (child 1) .group [] (some secondItem.occurrence) :=
    NodeAt.group (address := [0, 0, 1, 1, 1, 0])
      (groups := [⟨child 1, []⟩]) (path := (child 1).path)
      (result := .ok ([("name", .scalar "name2")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  refine ⟨w, admitted, selected, ?_⟩
  exact ConformancePlan.groupNotice_canAnnounce generated source
    (by cbv)
    history announced support safe groups streams failures streamReady ledger
    cuts partition contents selected
    (by simp [groupNoticeRefs])
    located

/-- One multi-item carrier retains the healthy ancestry of every introduced group.
Witness: the general handler theorem follows both actual item integrations and their
pruned frontiers; notice health is not assumed from the observed output.
-/
theorem batched_item_notice_ancestors_healthy
    : GroupNoticeAncestorsHealthy work
        (initial.objectFailureContributions [.streamItems stream [item, secondItem]])
        (initial.handleGraphEvent (.streamItems stream [item, secondItem])).2 :=
  generated.replayGraphEvents_next_noticeAncestorsHealthy (before := []) valid_batched
    (by cbv)

/-- Batched item integrations retain ancestry certificates for their combined carrier.
Witness: apply matched replay's notice-retirement theorem to the actual two-item handler,
without assuming the handler's output is admitted by the scheduler contract.
-/
theorem batched_item_notice_ancestors_retired
    : (initial.replayGraphEvents
        [.streamItems stream [item, secondItem]]).GroupNoticeAncestorsRetired
        work (initial.handleGraphEvent (.streamItems stream [item, secondItem])).2 :=
  generated.replayGraphEvents_next_noticeAncestorsRetired (before := []) (by simp)
    (valid_batched.eachMatches List.mem_cons_self)

-----------------------------------------------------------------------------------------
-- A batched carrier promotes children through distinct taskless defer ancestors
-----------------------------------------------------------------------------------------

namespace TasklessAncestors

private def shell (index : Nat) : DeliveryNode :=
  ⟨2 * index + 1, [.field "users", .index index], some (.string "P")⟩

private def nestedChild (index : Nat) : DeliveryNode :=
  ⟨2 * index + 2, [.field "users", .index index], some (.string "C")⟩

private def nestedWork (index : Nat) : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨nestedChild index, [shell index]⟩] (nestedChild index).path
        (.ok ([("name", .scalar ("name" ++ toString (index + 1)))], 0))
        (.combine .empty .empty))
      .empty)

private def nestedEntries : List (Result ResponseValue × Execution.Work) :=
  [(.ok (.object [], 0), nestedWork 0), (.ok (.object [], 0), nestedWork 1)]

private def nested : Execution.Work :=
  .combine (.combine (.combine .empty (.stream stream nestedEntries)) .empty) .empty

private def nestedItem (index : Nat) : StreamItem :=
  ⟨
    .item [0, 0, 1] index,
    ⟨.object [], 0⟩,
    Work.fromExecution (nestedWork index) [0, 0, 1, index]
  ⟩

private theorem generatedNested : ExecutedWork nested := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [field "users" [defer [defer [field "name"] (some "C")] (some "P")] [.stream]], ?_⟩
  cbv

private theorem nestedLocated
    : Located nested [0, 0, 1] (.stream stream nestedEntries) none [] := by cbv

private theorem validNested
    : ValidGraphEvents nested [.streamItems stream [nestedItem 0, nestedItem 1]] := by
  refine .append .nil ?_ ?_ ?_
  · intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, _, TaskAt.item nestedLocated rfl, by cbv⟩
    · exact ⟨_, _, TaskAt.item nestedLocated rfl, by cbv⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities, nestedItem]
  · refine ⟨_, _, _, _, nestedLocated, by simp, by simp,
      (by intro source impossible; cases impossible), ?_⟩
    cbv

private def nestedInitial : State := State.initialize (Work.fromExecution nested)

private def nestedNext : State := nestedInitial.integrateStreamItem (nestedItem 0)

private theorem nestedShellPruned : nestedNext.groupNode? (shell 0).ref = none := by cbv

private theorem nestedChildCandidate
    : (⟨nestedChild 0, some (shell 0).ref⟩ : Group) ∈ (nestedItem 0).work.groups := by
  cbv
  exact List.mem_cons_of_mem _ List.mem_cons_self

private theorem nestedChildSurvives
    : ∃ node, nestedNext.groupNode? (nestedChild 0).ref = some node := by
  refine ⟨{
    group := ⟨nestedChild 0, some (shell 0).ref⟩
    tasks := [.executionGroup [0, 0, 1, 0, 1, 0]]
    pending := 1 }, ?_⟩
  cbv

/-- A fresh item places C beneath an active root after pruning its taskless shell.
Witness: the general region-inventory coverage theorem, instantiated with generated item
work. No child coverage or announcement is assumed before integration.
-/
theorem taskless_item_child_root_covered
    : let initial := State.initialize (Work.fromExecution nested)
      let next := initial.integrateStreamItem (nestedItem 0)
      next.groupNode? (shell 0).ref = none
      ∧ ∃ root ∈ next.rootGroups, next.LiveDescendant root (nestedChild 0).ref := by
  change nestedNext.groupNode? (shell 0).ref = none
    ∧ ∃ root ∈ nestedNext.rootGroups, nestedNext.LiveDescendant root (nestedChild 0).ref
  refine ⟨nestedShellPruned, ?_⟩
  obtain ⟨parents, canonical⟩ := generatedNested.groupRecordsCanonical
  have initialCanonical : ∀ group ∈ (Work.fromExecution nested).groups,
      group.parent = (parents group.node.ref).head? :=
    fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member
  have registered := createWorkQueue_registration nested
  apply (createWorkQueue_regionInventory nested).streamItem_healthy_group_root_coverage
    generatedNested (createWorkQueue_parentLinksComplete _ parents initialCanonical)
    (createWorkQueue_groupRefsUnique _) registered.1
    (createWorkQueue_parentRegistryClosed canonical)
    (createWorkQueue_cancelledRecordsSupported _ nested [])
    (createWorkQueue_groupNodesMatchWork nested) (createWorkQueue_childGroupsUnique _)
    (createWorkQueue_childLinksCanonical _ parents initialCanonical) canonical
    (validNested.eachMatches List.mem_cons_self) List.mem_cons_self (by simp)
    nestedChildCandidate (fun invalid => invalid.nonempty rfl)
  exact nestedChildSurvives

/-- Both item-produced children are live at the carrier after their taskless shells prune.
Witness: fold the general registered-root preservation theorem over the matching batch.
This establishes preparation presence before any later drain can close a group.
-/
theorem batched_preparation_roots_present
    : ((State.initialize (Work.fromExecution nested)).preparedStreamItems
        [nestedItem 0, nestedItem 1]).RootGroupsPresent := by
  have registration := createWorkQueue_registration nested
  exact (createWorkQueue_rootGroupsPresent (Work.fromExecution nested)).preparedStreamItems
    (createWorkQueue_groupRefsUnique _) registration.1 registration.2
    (validNested.eachMatches List.mem_cons_self)

/-- Generated replay retains live roots after the same batched item carrier and its drain.
Witness: the general replay theorem needs only matching input, not scheduler admission.
-/
theorem batched_replay_roots_present
    : ((State.initialize (Work.fromExecution nested)).replayGraphEvents
        [.streamItems stream [nestedItem 0, nestedItem 1]]).RootGroupsPresent :=
  generatedNested.replayGraphEvents_rootsPresent _
    (fun _ member => validNested.eachMatches member)

private theorem childKnown (index : Nat) (bound : index < 2)
    : NodeAt nested (nestedChild index) .group [(shell index).ref]
        (some (.item [0, 0, 1] index)) := by
  have alternatives : index = 0 ∨ index = 1 := by omega
  rcases alternatives with rfl | rfl
  · exact .group (groups := [⟨nestedChild 0, [shell 0]⟩])
      (children := .combine .empty .empty) (address := [0, 0, 1, 0, 1, 0])
      (path := (nestedChild 0).path) (result := .ok ([("name", .scalar "name1")], 0))
      (owners := []) (by cbv) List.mem_cons_self
  · exact .group (groups := [⟨nestedChild 1, [shell 1]⟩])
      (children := .combine .empty .empty) (address := [0, 0, 1, 1, 1, 0])
      (path := (nestedChild 1).path) (result := .ok ([("name", .scalar "name2")], 0))
      (owners := []) (by cbv) List.mem_cons_self

/-- One item carrier accounts for both silently pruned ancestors on its canonical witness.
Witness: the general leading-notice theorem uses the original mixed ledger and actual
two-item carrier. Each child's nonempty ancestry refers to a different taskless shell;
neither shell is assumed announced, completed, or represented by a contributing task.
-/
theorem batched_notice_ancestors_accounted
    : ∃ w : ConformancePlan.Witness,
        w.events
          = (State.initialize (Work.fromExecution nested)).nonterminalAtoms
              [[.streamItems stream [nestedItem 0, nestedItem 1]]]
        ∧ w.events[1]?
          = some (.streamValues stream [wireValue] [nestedChild 0, nestedChild 1] [])
        ∧ ∀ ordinal < 2,
            ∀ failures,
              NodeAccounted nested w.matching (w.events.take 1) failures
                (shell ordinal).ref := by
  let inputs := [[GraphEvent.streamItems stream [nestedItem 0, nestedItem 1]]]
  have source : ValidGraphEvents nested inputs.flatten := validNested
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, _⟩ :=
    ConformancePlan.mixed_groupReleaseCertificates generatedNested source (by cbv)
  have selected : w.events[1]? = some (.streamValues stream [wireValue]
      [nestedChild 0, nestedChild 1] []) := by rw [history]; cbv
  refine ⟨w, history, selected, ?_⟩
  intro ordinal bound failures
  have noticed : nestedChild ordinal ∈ [nestedChild 0, nestedChild 1] := by
    have alternatives : ordinal = 0 ∨ ordinal = 1 := by omega
    rcases alternatives with rfl | rfl <;> simp
  exact ConformancePlan.itemGroupNoticeAncestor_nodeAccounted generatedNested source
    (by cbv) history ledger selected noticed
    (groupRecordAt_of_nodeAt (childKnown ordinal bound)) List.mem_cons_self failures

/-- Both taskless ancestors stay semantically healthy at the frozen two-item carrier.
Witness: the canonical publication-support theorem rules out every causal failure rule,
including producer propagation, then transports health across the actual final item atom.
-/
theorem batched_notice_ancestors_healthy_at_carrier
    : ∃ w : ConformancePlan.Witness,
        w.events[1]?
          = some (.streamValues stream [wireValue] [nestedChild 0, nestedChild 1] [])
        ∧ ∀ ordinal < 2,
            ¬NodeFailed nested w.matching
              (w.events.take 1 ++ [.streamValues stream [wireValue] [] []])
              (w.failures.filter (fun entry => entry.1 ≤ 1)) (shell ordinal).ref := by
  let inputs := [[GraphEvent.streamItems stream [nestedItem 0, nestedItem 1]]]
  have source : ValidGraphEvents nested inputs.flatten := validNested
  obtain ⟨w, history, _, announced, _, _, _, _, _, _, ledger, _, support, _⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generatedNested source (by cbv)
  have selected : w.events[1]? = some (.streamValues stream [wireValue]
      [nestedChild 0, nestedChild 1] []) := by rw [history]; cbv
  refine ⟨w, selected, ?_⟩
  intro ordinal bound
  have noticed : nestedChild ordinal ∈ [nestedChild 0, nestedChild 1] := by
    have alternatives : ordinal = 0 ∨ ordinal = 1 := by omega
    rcases alternatives with rfl | rfl <;> simp
  exact ConformancePlan.healthy_noticeCarrier selected
    (ConformancePlan.itemGroupNoticeAncestor_healthy generatedNested source (by cbv)
      history ledger support announced selected noticed
      (groupRecordAt_of_nodeAt (childKnown ordinal bound)) _ List.mem_cons_self)

/-- Both taskless ancestors are ready at the final atom of their shared item carrier.
Witness: the general canonical theorem derives every dependency component, preserving
the raw carrier despite the extra first item atom. No local notice-status premise is used.
-/
theorem batched_notice_ancestors_ready
    : ∃ w : ConformancePlan.Witness,
        w.events[1]?
          = some (.streamValues stream [wireValue] [nestedChild 0, nestedChild 1] [])
        ∧ ∀ ordinal < 2,
            DependencySatisfied nested (ConformancePlan.initialRefs nested) w.matching
              (w.events.take 1 ++ [.streamValues stream [wireValue] [] []])
              (w.failures.filter (fun entry => entry.1 ≤ 1)) (shell ordinal).ref := by
  let inputs := [[GraphEvent.streamItems stream [nestedItem 0, nestedItem 1]]]
  have source : ValidGraphEvents nested inputs.flatten := validNested
  obtain ⟨w, history, _, announced, _, _, _, _, _, _, ledger, _, support, _⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generatedNested source (by cbv)
  have selected : w.events[1]? = some (.streamValues stream [wireValue]
      [nestedChild 0, nestedChild 1] []) := by rw [history]; cbv
  refine ⟨w, selected, ?_⟩
  intro ordinal bound
  have noticed : nestedChild ordinal ∈ [nestedChild 0, nestedChild 1] := by
    have alternatives : ordinal = 0 ∨ ordinal = 1 := by omega
    rcases alternatives with rfl | rfl <;> simp
  exact ConformancePlan.itemGroupNoticeAncestor_dependencySatisfied generatedNested source
    (by cbv) history ledger support announced selected noticed
    (groupRecordAt_of_nodeAt (childKnown ordinal bound)) _ List.mem_cons_self

/-- Splitting a multi-item carrier preserves global uniqueness of its taskless-promoted groups.
Witness: the canonical shared construction retains the exact raw notice inventory, and
the generic global uniqueness theorem covers both children without fixture reduction.
-/
theorem batched_group_refs_unique
    : ∃ w : ConformancePlan.Witness,
        w.events
          = (ConformancePlan.initialQueue nested).nonterminalAtoms
              [[.streamItems stream [nestedItem 0, nestedItem 1]]]
        ∧ ((ConformancePlan.initialQueue nested).rootGroups
            ++ w.events.flatMap groupNoticeRefs).Nodup := by
  let inputs := [[GraphEvent.streamItems stream [nestedItem 0, nestedItem 1]]]
  have source : ValidGraphEvents nested inputs.flatten := validNested
  obtain ⟨w, history, _⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generatedNested source (by cbv)
  exact ⟨
    w,
    history,
    ConformancePlan.groupNoticeRefs_nodup generatedNested source (by cbv) history
  ⟩

end TasklessAncestors

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerItemProducedObjects
