import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupCarrierNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeFailureSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicHandlerBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyClosureAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeContributorSources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorDrainPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeAncestorPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeTracking
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPresenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCompletionHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawNoticeHistoryCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshGroupNoticeAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalGroupCompletion
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Cached failure removal precedes a successful drain; its queued notice waits for observed FIFO dispatch. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainNotices
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def root : DeliveryNode := ⟨0, [], some (.string "R")⟩
private def parent : DeliveryNode := ⟨1, [], some (.string "P")⟩
private def failed : DeliveryNode := ⟨2, [], some (.string "F")⟩
private def child : DeliveryNode := ⟨3, [], some (.string "C")⟩
private def grandchild : DeliveryNode := ⟨4, [], some (.string "D")⟩
private def failedTask : Occurrence := .executionGroup [1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]

private def sharedValue : ExecutionGroupValue :=
  {
    path := [], data := [("a", .scalar "a")], errors := 0, deliveryGroups := [root, child]
  }

private def parentValue : ExecutionGroupValue :=
  { path := [], data := [("b", .scalar "b")], errors := 0, deliveryGroups := [parent] }

private def selections : List Selection :=
  [
    defer [field "required", field "a"] (some "R"),
    defer
      [
        field "b",
        defer [field "required"] (some "F"),
        defer [field "a", defer [field "c"] (some "D")] (some "C")
      ]
      (some "P")
  ]

private def work : Execution.Work :=
  .combine .empty
    (.declareGroups
      [
        ⟨root, []⟩,
        ⟨parent, []⟩,
        ⟨failed, [parent]⟩,
        ⟨child, [parent]⟩,
        ⟨grandchild, [child, parent]⟩
      ]
      (.combine
        (.executionGroup [⟨root, []⟩, ⟨failed, [parent]⟩] []
          ({ result := .error 1, cause := some 1 }) .empty)
        (.combine
          (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] []
            ({ result := .ok (sharedValue.data, 0) }) (.combine .empty .empty))
          (.combine
            (.executionGroup [⟨parent, []⟩] [] ({ result := .ok (parentValue.data, 0) })
              (.combine .empty .empty))
            (.combine
              (.executionGroup [⟨grandchild, [child, parent]⟩] []
                ({ result := .ok ([("c", .scalar "c")], 0) }) (.combine .empty .empty))
              .empty)))))

private def failure : GraphEvent := .taskFailure failedTask 1
private def buffered : GraphEvent := .taskSuccess sharedTask ⟨sharedValue, {}⟩
private def finish : GraphEvent := .taskSuccess parentTask ⟨parentValue, {}⟩
private def received : List GraphEvent := [failure, buffered, finish]
private def notice : GraphEvent := .groupFailure ⟨failed, 1⟩
private def dispatched : List GraphEvent := received ++ [notice]
private def incoming : TaskNode := { task := ⟨parentTask, [parent]⟩ }
private def initial : State := State.initialize (Work.fromExecution work)

private def prepared : State :=
  let current := initial.replayGraphEvents [failure, buffered]
  let stored := current.putTaskNode { incoming with value := some parentValue }
  (stored.maybeIntegrateWork {} (some parentTask)).1

private def released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
private def ready : State := (released.1.startNewWork released.2.2).1

private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0, selections, by cbv⟩

private theorem valid : ValidGraphEvents work received := by
  have failureKnown : TaskAt work failedTask [root.ref, failed.ref] none (.object [] (.error 1)) :=
    .executionGroup (result := { result := .error 1, cause := some 1 }) (groups := [⟨root,
      []⟩, ⟨failed, [parent]⟩])
      (children := .empty) (owners := []) (by cbv)
  have sharedKnown : TaskAt work sharedTask [root.ref, child.ref] none
      (.object [] (.ok (sharedValue.data, 0))) :=
    .executionGroup (result := { result := .ok (sharedValue.data, 0) }) (groups := [⟨root,
      []⟩, ⟨child, [parent]⟩])
      (children := .combine .empty .empty) (owners := []) (by cbv)
  have parentKnown : TaskAt work parentTask [parent.ref] none
      (.object [] (.ok (parentValue.data, 0))) :=
    .executionGroup (result := { result := .ok (parentValue.data, 0) }) (groups := [⟨parent, []⟩])
      (children := .combine .empty .empty) (owners := []) (by cbv)
  have one : ValidGraphEvents work [failure] :=
    .append .nil ⟨_, _, _, failureKnown⟩
      (by simp [failure, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, failureKnown, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [failure, buffered] :=
    .append one ⟨_, _, sharedKnown, by cbv, by cbv⟩
      (by simp [failure, buffered, failedTask, sharedTask, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, sharedKnown, by intro source impossible; cases impossible⟩
  exact .append two ⟨_, _, parentKnown, by cbv, by cbv⟩
    (by simp [failure, buffered, finish, failedTask, sharedTask, parentTask,
      GraphEvent.Fresh, GraphEvent.identities])
    ⟨_, _, _, parentKnown, by intro source impossible; cases impossible⟩

/-- This fixture's two distinct payloads identify their exact supplying tasks. -/
private theorem received_publications_exact (published : List ObjectPublication)
    (values : published.map Prod.snd = [parentValue, sharedValue])
    (sources
      : ∀ publication ∈ published, ObjectValueFrom received publication.1 publication.2)
    : published = [(parentTask, parentValue), (sharedTask, sharedValue)] := by
  obtain ⟨first, rest, rfl, firstValue, restValues⟩ := List.map_eq_cons_iff.mp values
  obtain ⟨second, rfl, secondValue⟩ := List.map_eq_singleton_iff.mp restValues
  have firstSource := sources first List.mem_cons_self
  have secondSource := sources second (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨firstResult, firstMember, firstSame⟩ := firstSource
  obtain ⟨secondResult, secondMember, secondSame⟩ := secondSource
  simp only [received, failure, buffered, finish, List.mem_cons, List.not_mem_nil,
    or_false, GraphEvent.taskSuccess.injEq, reduceCtorEq, false_or] at firstMember secondMember
  have firstTask : first.1 = parentTask := by
    rcases firstMember with ⟨sameTask, rfl⟩ | ⟨sameTask, rfl⟩
    · have impossible := firstSame.trans firstValue
      simp [sharedValue, parentValue] at impossible
    · exact sameTask
  have secondTask : second.1 = sharedTask := by
    rcases secondMember with ⟨sameTask, rfl⟩ | ⟨sameTask, rfl⟩
    · exact sameTask
    · have impossible := secondSame.trans secondValue
      simp [sharedValue, parentValue] at impossible
  have firstExact : first = (parentTask, parentValue) := Prod.ext firstTask firstValue
  have secondExact : second = (sharedTask, sharedValue) := Prod.ext secondTask secondValue
  rw [firstExact, secondExact]

/-- The immediate replay has the same occurrence ledger in this concrete fixture.
Witness: derive a separate empty-snapshot certificate and identify both ledgers using
source provenance and the two distinct payloads. No host snapshot is erased.
-/
private theorem received_ledger_empty {events matching published}
    (ledger : ObjectLedgerMatching work [received] events matching published)
    : initial.ReplayClosuresCovered received published := by
  obtain ⟨raw, values, inventory, covered, _⟩ :=
    generated.rawEventReplay_bufferedCoverage received valid (by cbv)
  have rawExact := received_publications_exact raw (values.trans (by cbv))
    inventory.provenance
  have publishedExact := received_publications_exact published
    (ledger.rawValues.trans (by cbv)) (by
      intro publication member
      obtain ⟨result, source, same, _⟩ := ledger.source publication member
      exact ⟨result, by simpa using source, same⟩)
  rw [publishedExact]
  rwa [rawExact] at covered

/-- Startup removes the cached failure before draining the healthy child.
The failure notice is queued separately and forwarded after the supplied host batch.
-/
theorem failure_before_notice_carrier
    : (released.1.startNewWork released.2.2).2 = [⟨failed, 1⟩]
      ∧ ready.drainReadyGroups.2.1
        = [.groupValues child [sharedValue], .groupSuccess child [grandchild] []] := by
  cbv

private theorem grandchildKnown
    : NodeAt work grandchild .group [child.ref, parent.ref] none :=
  .group (work := work) (producer := none) (group := ⟨grandchild, [child, parent]⟩)
    (address := [1, 1, 1, 1, 0]) (groups := [⟨grandchild, [child, parent]⟩])
    (path := []) (result := { result := .ok ([("c", .scalar "c")], 0) })
    (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self

private theorem child_uncancelled
    : child.ref ∉ ready.drainReadyGroups.1.cancelledGroups := by
  cbv
  intro member
  cases member with
  | tail _ member =>
      cases member with
      | tail _ impossible => cases impossible

private theorem child_announced
    : .groupSuccess parent [failed, child] [] ∈ released.2.1 := by
  cbv
  exact .tail _ (.head _)

private theorem child_announced_before_carrier
    : child.ref
      ∈ initial.rootGroups
        ++ (((initial.rawEventReplay [failure, buffered]).2
              ++ released.2.1
              ++ ready.drainReadyGroups.2.1.take 2).flatMap
              rawGroupNoticeRefs) := by
  apply List.mem_append_right
  rw [List.flatMap_append, List.flatMap_append]
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨.groupSuccess parent [failed, child] [],
    child_announced, List.mem_cons_of_mem _ List.mem_cons_self⟩

private theorem child_carrier
    : ready.drainReadyGroups.2.1[1]? = some (.groupSuccess child [grandchild] []) := by
  rw [failure_before_notice_carrier.2]
  rfl

/-- C completes by D's carrier after startup removes an earlier cached failure.
Witness: source-prefix tracking includes P's earlier C notice and the intervening cached
failure. The general handler theorem derives completion by the exact D carrier.
-/
theorem ancestor_completed_after_cached_failure
    : child.ref
      ∈ (((initial.rawEventReplay [failure, buffered]).2
          ++ released.2.1
          ++ ready.drainReadyGroups.2.1.take 2).flatMap
          rawGroupClosureRefs) := by
  have prior : ∀ source ∈ [failure, buffered], source.MatchesWork work :=
    fun _ member => valid.eachMatches (List.mem_append_left [finish] member)
  have matched := valid.eachMatches
    (List.mem_append_right [failure, buffered] List.mem_cons_self)
  exact generated.taskDrainNoticeAncestor_completed (before := [failure, buffered])
    (occurrence := parentTask) (result := ⟨parentValue, {}⟩) (ref := child.ref) prior
    matched (by cbv) (groupRecordAt_of_nodeAt grandchildKnown) List.mem_cons_self
    (incoming := incoming) (index := 1) (group := child) (groups := [grandchild])
    (streams := []) child_carrier List.mem_cons_self child_uncancelled
    child_announced_before_carrier

/-- The complete raw replay closes C by D's exact carrier without a supplied health premise.
Witness: the general raw-history theorem derives noncancellation and recovers the actual
source handler and recursive-drain origin, including the earlier root-failure output.
-/
theorem raw_notice_ancestor_completed
    : child.ref
      ∈ ((initial.rawEventReplay received).2.take 5).flatMap rawGroupClosureRefs := by
  have selected : (initial.rawEventReplay received).2[4]?
      = some (.groupSuccess child [grandchild] []) := by cbv
  exact generated.rawEventReplay_groupNoticeAncestor_completed valid
    (by cbv)
    selected List.mem_cons_self
    (groupRecordAt_of_nodeAt grandchildKnown)
    List.mem_cons_self
    (by cbv; exact .tail _ (.tail _ (.tail _ (.head _))))

/-- The mixed replay retains status for initial, newly announced, and cancelled groups.
Witness: instantiate general handler/replay tracking, including cached failure release
and the later successful carrier. This does not assume abstract output admission.
-/
theorem mixed_replay_tracks_notices
    : GroupNoticeTracking initial.rootGroups (initial.rawEventReplay received) :=
  initial.rawEventReplay_groupNoticeTracking received

/-- C's disappearance after its notice requires an actual completion, not silent loss.
Witness: the general tracking theorem plus C's concrete notice and endpoint absence from
both active roots and cancellation history. The completion itself is not a premise.
-/
theorem announced_child_has_completion
    : child.ref ∈ (initial.rawEventReplay received).2.flatMap rawGroupClosureRefs := by
  apply mixed_replay_tracks_notices.completed_of_inactive_uncancelled
  · cbv
    exact .tail _ (.tail _ (.tail _ (.head _)))
  · cbv
    intro member
    cases member with
    | tail _ member => cases member
  · cbv
    intro member
    cases member with
    | tail _ member =>
        cases member with
        | tail _ member => cases member

/-- The retained F cache is supported by the accepted failure before P releases it.
Witness: derive support from full source accounting, then preserve it through P's owner
fold and every bounded drain prefix. This is not a supplied failure-admission premise.
-/
theorem cached_notice_has_accepted_contributor
    : ready.CachedFailuresSupported work [failedTask]
      ∧ (∀ fuel,
          (State.drainReadyGroups.go [] fuel ready).1.CachedFailuresSupported work
            [failedTask])
      ∧ ∃ owners, TaskHasOwners work failedTask owners ∧ failed.ref ∈ owners := by
  have prior : ValidGraphEvents work [failure, buffered] :=
    valid.prefix ⟨[finish], rfl⟩
  have supported := generated.taskSuccess_drain_cachedAcceptedFailures
    (occurrence := parentTask) (result := ⟨parentValue, {}⟩) prior (by cbv) incoming (by cbv)
  have inventory : initial.objectFailureContributions [failure, buffered] = [failedTask] := by
    cbv
  change ready.CachedFailuresSupported work
    (initial.objectFailureContributions [failure, buffered]) at supported
  rw [inventory] at supported
  refine ⟨supported, supported.drainReadyGroups_go, ?_⟩
  have known : TaskAt work failedTask [root.ref, failed.ref] none (.object [] (.error 1)) :=
    .executionGroup (result := { result := .error 1, cause := some 1 })
      (groups := [⟨root, []⟩, ⟨failed, [parent]⟩]) (children := .empty) (owners := []) (by cbv)
  exact ⟨[root.ref, failed.ref], ⟨none, _, known⟩, by simp⟩

/-- The same mixed witness retains D's contents and excludes both earlier publications.
Witness: the generated drain theorem recovers the actual carrier boundary after F's
failure. It supplies the live D record and its contents; the original conformance ledger
excludes P's owner-fold value and C's drain value from that same record.
-/
theorem retained_notice_after_failure_on_common_witness
    : ∃ w : ConformancePlan.Witness,
      ∃ published : List ObjectPublication,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ObjectLedgerMatching work [received] w.events w.matching published
        ∧ ∃ steps closing,
            steps < ready.groupNodes.length
            ∧ let segment := State.drainReadyGroups.go [] steps ready
              let closed := segment.1.finishGroupSuccess closing
              segment.1.rootGroups.findSome?
                  (fun ref => do
                    let candidate ← segment.1.groupNode? ref
                    if candidate.pending == 0 then some candidate else none)
                = some closing
              ∧ ready.drainReadyGroups.2.1.take 2 = segment.2.1 ++ closed.2.1
              ∧ ∃ node,
                  closed.1.groupNode? grandchild.ref = some node
                  ∧ node.group.node = grandchild
                  ∧ node.tasks ≠ []
                  ∧ ∀ publication ∈ published.take 2, publication.1 ∉ node.tasks := by
  have started : inputsStarted work [received] = true := by cbv
  obtain ⟨w, _, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [received]) valid started
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := received_ledger_empty matching
  obtain ⟨steps, closing, bounded, selected, exactPrefix, _, node, found, same, contents,
      excluded⟩ := generated.taskSuccess_drainNoticeContents (before := [failure,
        buffered]) (after := [])
      (incoming := incoming) (index := 1) (group := child) (groups := [grandchild]) (streams := [])
      covered valid (by cbv) (by cbv) List.mem_cons_self
  refine ⟨
    w,
    published,
    admitted,
    matching,
    steps,
    closing,
    bounded,
    selected,
    exactPrefix,
    node,
    found,
    same,
    contents,
    ?_
  ⟩
  intro publication member
  apply excluded publication
  have count : (((initial.rawEventReplay [failure, buffered]).2 ++ released.2.1
      ++ ready.drainReadyGroups.2.1.take 1).flatMap WorkQueueEvent.objectValues).length = 2 := by
    cbv
  change publication ∈ published.take
    (((initial.rawEventReplay [failure, buffered]).2 ++ released.2.1
      ++ ready.drainReadyGroups.2.1.take 1).flatMap WorkQueueEvent.objectValues).length
  rw [count]
  exact member

/-- The atomic carrier after cached failure cleanup retains semantically unpublished tasks.
Witness: apply the general canonical group-carrier theorem to the actual fifth output.
The test supplies neither a drain step nor a ledger count, and keeps object admission
on the same witness with the same failure cuts and publication matching.
-/
theorem atomic_notice_after_failure_unpublished
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[4]? = some (.groupSuccess child [grandchild] [])
        ∧ RetainedNoticeContents work w.matching (w.events.take 4)
            (failedBefore w.failures 4) received grandchild := by
  obtain ⟨w, history, _, _, _, _, _, streamReady, _, _, ledger, _, _, _, admitted,
    streamCuts, _, exactCuts⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates_with_cuts generated
      (inputs := [received]) valid (by cbv)
  have selected : w.events[4]? = some (.groupSuccess child [grandchild] []) := by
    rw [history]
    cbv
  exact ⟨
    w,
    admitted,
    selected,
    ConformancePlan.groupGroupNotice_unpublished
      (inputs := [received])
      generated valid
      (by cbv)
      history ledger admitted streamReady
      (streamCuts := streamCuts)
      (by rw [exactCuts]; exact mergeFailureCuts_partition _ _)
      selected List.mem_cons_self
  ⟩

/-- A newly announced failure-only child retains cut-supported contents on the common witness.
Witness: F has no pending task when P announces it. The strengthened canonical contents
theorem preserves its cached-failure support and task exclusion together, before draining F.
-/
theorem atomic_failure_only_notice_contents
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[2]? = some (.groupSuccess parent [failed, child] [])
        ∧ RetainedNoticeContents work w.matching (w.events.take 2)
            (failedBefore w.failures 2) received failed := by
  obtain ⟨w, history, _, _, _, _, _, streamReady, _, _, ledger, _, _, _, admitted,
    streamCuts, _, exactCuts⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates_with_cuts generated
      (inputs := [received]) valid (by cbv)
  have selected : w.events[2]? = some (.groupSuccess parent [failed, child] []) := by
    rw [history]
    cbv
  exact ⟨
    w,
    admitted,
    selected,
    ConformancePlan.groupGroupNotice_unpublished
      (inputs := [received])
      generated valid
      (by cbv)
      history ledger admitted streamReady
      (streamCuts := streamCuts)
      (by rw [exactCuts]; exact mergeFailureCuts_partition _ _)
      selected List.mem_cons_self
  ⟩

/-- P is accounted at its child-announcement boundary despite another owner's failure.
Witness: the common witness supplies successful-group accounting and failure admission;
the generic healthy-completion theorem transfers them to the inclusive carrier prefix.
No carried-notice admission is assumed for that prefix.
-/
theorem healthy_parent_accounted_at_notice
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ NodeAccounted work w.matching (w.events.take 3) w.failures parent.ref := by
  obtain ⟨w, history, _, _, _, failures, streams, _, healthy, accounted,
    _, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [received]) valid (by cbv)
  have selected : w.events[2]? = some (.groupSuccess parent [failed, child] []) := by
    rw [history]
    cbv
  have closed : parent.ref ∈ completedRefs (w.events.take 3) := by
    rw [history]
    cbv
    exact .tail _ (.head _)
  exact ⟨
    w,
    admitted,
    ConformancePlan.healthy_completed_accounted accounted streams failures
      closed (healthy.atPrefix selected 3)
  ⟩

/-- F's error-only notice has a source-ready contributor although its task was removed.
Witness: the actual carrier supplies the retained cache; the original mixed-cut partition
recovers an accepted input failure and its producer prerequisite on that same witness.
No live membership, source occurrence, or alternative cut list is supplied by the test.
-/
theorem error_only_notice_sourceReady
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ∃ address owners producer payload,
            TaskAt work (.executionGroup address) owners producer payload
            ∧ failed.ref ∈ owners
            ∧ ∀ source,
                producer = some source
                → source ∈ received.flatMap GraphEvent.successes := by
  obtain ⟨w, history, _, _, _, _, _, streamReady, _, _, ledger, _, _, _, admitted,
    streamCuts, cuts, exactCuts⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates_with_cuts generated
      (inputs := [received]) valid (by cbv)
  have selected : w.events[2]? = some (.groupSuccess parent [failed, child] []) := by
    rw [history]
    cbv
  have partition : w.failures.Perm
      (streamCuts ++ informativeObjectFailureCuts work
        (initial.sourceRunBlocks
          { active := initial.initialGroups ++ initial.initialStreams } [received]).2.2) := by
    rw [exactCuts]
    exact mergeFailureCuts_partition _ _
  have contents := ConformancePlan.groupGroupNotice_unpublished generated
    (inputs := [received]) valid (by cbv) history ledger admitted streamReady
    partition selected List.mem_cons_self
  exact ⟨
    w,
    admitted,
    ConformancePlan.retainedNotice_sourceReadyContributor
      generated (inputs := [received]) valid (by cbv) cuts partition contents
  ⟩

/-- P's carrier retains its actual handler and prior-cache support at the canonical cut.
Witness: the joint boundary theorem uses the same witness as full object admission, not
an independently selected history. Earlier failure and silent buffered settlement remain
in the recovered source prefix; the theorem supplies the publication count; source replay
  supplies rejection provenance.
-/
theorem atomic_handler_cache_supported
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ∃ before source after,
          ∃ publisher : IncrementalPublisher,
          ∃ localIndex,
            received = before ++ source :: after
            ∧ let current := initial.replayGraphEvents before
              ((publisher.normalizeBatch (current.handleGraphEvent source).2.1).2.flatMap
                  publicationAtoms)[localIndex]?
                = some (.groupSuccess parent [failed, child] [])
              ∧ ((w.events.take 2).flatMap normalizedObjectValues).length
                = ((initial.rawEventReplay before).2.flatMap
                    WorkQueueEvent.objectValues).length
                  + ((((publisher.normalizeBatch
                          (current.handleGraphEvent source).2.1).2.flatMap
                        publicationAtoms).take
                        localIndex).flatMap
                      normalizedObjectValues).length
              ∧ current.CachedFailuresSupported work
                  (initial.objectFailureContributions before) := by
  obtain ⟨w, history, _, _, _, _, _, _, _, _, _, _, _, _, admitted, _, _, _⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates_with_cuts generated
      (inputs := [received]) valid (by cbv)
  have selected : w.events[2]? = some (.groupSuccess parent [failed, child] []) := by
    rw [history]
    cbv
  have prior : ValidGraphEvents work [failure, buffered] := valid.prefix ⟨[finish], rfl⟩
  have supported := (createWorkQueue_cachedFailuresSupported (Work.fromExecution work) work
    []).replayGraphEvents_contributions (createWorkQueue_startedTasksRegistered _)
      (createWorkQueue_fromSpec_registeredTasksMatch _) [failure, buffered]
      (fun event member => prior.eachMatches member)
  refine ⟨w, admitted, [failure, buffered], finish, [], { active := [parent] }, 1,
    rfl, ?_, ?_, ?_⟩
  · cbv
  · rw [history]; cbv
  · simpa only [initial, List.append_nil] using supported

/-- An error-only child is eligible before its queued cached-error completion.
Witness: P's real successful carrier satisfies F's parent dependency. The general bridge
uses F's accepted failure cache and the same frozen mixed cuts, despite F having no live
task memberships. Freshness comes from raw replay separation, and F's later error
completion is not pulled into the carrier boundary.
-/
theorem error_only_notice_canAnnounce
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[2]? = some (.groupSuccess parent [failed, child] [])
        ∧ ∃ birth,
            NodeAt work failed .group [parent.ref] birth
            ∧ CanAnnounce work (ConformancePlan.initialRefs work) w.matching
                (w.events.take 2 ++ [.groupSuccess parent [] []])
                (w.failures.filter (fun entry => entry.1 ≤ 2))
                failed .group [parent.ref] birth := by
  obtain ⟨w, history, _, announced, _, failures, streams, streamReady, _, groups,
    ledger, _, support, _, admitted, safe, streamCuts, cuts, exactCuts⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates_with_noticeSafety
      generated (inputs := [received]) valid (by cbv)
  have selected : w.events[2]? = some (.groupSuccess parent [failed, child] []) := by
    rw [history]
    cbv
  have partition := exactCuts ▸ mergeFailureCuts_partition _ _
  have contents := ConformancePlan.groupGroupNotice_unpublished generated
    (inputs := [received]) valid (by cbv) history ledger admitted streamReady
    partition selected (child := failed) List.mem_cons_self
  have known : NodeAt work failed .group [parent.ref] none :=
    NodeAt.group (work := work) (producer := none) (group := ⟨failed, [parent]⟩)
      (address := [1, 0]) (groups := [⟨root, []⟩, ⟨failed, [parent]⟩])
      (path := []) (result := { result := .error 1, cause := some 1 })
      (children := .empty) (owners := [])
      (by cbv) (by simp)
  refine ⟨w, admitted, selected, ?_⟩
  exact ConformancePlan.groupNotice_canAnnounce generated
    (inputs := [received])
    valid
    (by cbv)
    history announced support safe groups streams
    failures streamReady ledger cuts partition contents selected
    (by simp [groupNoticeRefs])
    known

/-- Cached failure cleanup and later draining never duplicate any announced group ref.
Witness: global raw uniqueness combines local unique frontiers with cross-carrier
separation for this generated matching replay; it does not evaluate the final notice list.
-/
theorem cached_failure_group_refs_unique
    : (initial.rootGroups
        ++ (initial.rawEventReplay received).2.flatMap rawGroupNoticeRefs).Nodup :=
  generated.rawEventReplay_groupRefs_nodup received
    (fun _ member => valid.eachMatches member)

/-- Cached failure removal retains its notice until the internal event is dispatched.
Witness: exact prefix state preserves the stored descriptor and count without emitting
its closure merely because the callback batch ended.
-/
theorem cached_error_notice_pending
    : (initial.rawBatches [received]).1.groupFailureEvents = [⟨failed, 1⟩]
      ∧ failed.ref ∉ (initial.rawBatches [received]).2.flatMap rawGroupClosureRefs := by
  constructor
  · cbv
  · cbv
    intro member
    cases member with
    | tail _ member =>
        cases member with
        | tail _ member =>
            cases member with
            | tail _ member => cases member

/-- The cached error's announced group completes when its queued event is dispatched.
Witness: general FIFO notice tracking at the extended source boundary forces the closure
once neither a live group nor an undelivered internal notice supports F.
-/
theorem cached_error_notice_completed
    : failed.ref ∈ (initial.rawBatches [dispatched]).2.flatMap rawGroupClosureRefs := by
  have matched : notice.MatchesWork work :=
    ⟨⟨[parent.ref], none, NodeAt.group (address := [1, 0]) (group := ⟨failed, [parent]⟩)
      (result := { result := .error 1, cause := some 1 }) (children := .empty)
      (by cbv) (by simp [failed, parent])⟩, by decide⟩
  have tracked := generated.rawBatches_groupNoticeCompletion [dispatched] (by
    intro event member
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, dispatched,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with prior | rfl
    · exact valid.eachMatches prior
    · exact matched) failed.ref (by
      cbv
      change (2 : Nat) ∈ [0, 1, 2, 3, 4]
      decide)
  exact tracked.resolve_left
    (by
      cbv
      intro member
      cases member with
      | tail _ member => cases member)

/-- Announced groups in the callback prefix stay live, queued for closure, or completed.
Witness: the generated replay's FIFO certificate includes pending internal notices;
a cached failure is retained until its explicit dispatch.
-/
theorem cached_failure_group_notices_tracked
    : FifoGroupNoticeCompletion initial.rootGroups (initial.rawBatches [received]) :=
  generated.rawBatches_groupNoticeCompletion [received]
    (fun _ member => valid.eachMatches member)

/-- F's cached failure does not invalidate P, whose completion announces F and C.
Witness: the general actual-replay theorem certifies the entire handler's notice ancestry
under its accepted failures. The failed child itself is deliberately not claimed healthy.
-/
theorem cached_error_notice_ancestors_healthy
    : GroupNoticeAncestorsHealthy work (initial.objectFailureContributions received)
        ((initial.replayGraphEvents [failure, buffered]).handleGraphEvent finish).2.1 :=
  generated.replayGraphEvents_next_noticeAncestorsHealthy valid (by cbv)

/-- Later removal of the noticed F child does not erase its parent-retirement certificate.
Witness: the actual replay theorem retains ancestry for every notice in the handler,
including F's owner-fold notice and D's later drain notice after F's failed cleanup.
-/
theorem cached_error_notice_ancestors_retired
    : (initial.replayGraphEvents received).GroupNoticeAncestorsRetired work
        ((initial.replayGraphEvents [failure, buffered]).handleGraphEvent
          finish).2.1 := by
  apply generated.replayGraphEvents_next_noticeAncestorsRetired
    (before := [failure, buffered]) (event := finish)
  · intro event member
    exact valid.eachMatches (List.mem_append_left [finish] member)
  · exact valid.eachMatches (List.mem_append_right [failure, buffered] List.mem_cons_self)

/-- D's C-ancestor buffer publishes before its notice despite preceding cached-error cleanup.
Witness: the exact handler's common drain-prefix ledger and generated structural frame
force C's shared a contribution into the strict prefix of C's carrier announcing D.
-/
theorem drain_notice_ancestor_published_on_common_witness
    : ∃ w : ConformancePlan.Witness,
      ∃ published : List ObjectPublication,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ObjectLedgerMatching work [received] w.events w.matching published
        ∧ (sharedTask, sharedValue) ∈ published.take 2
        ∧ w.events[4]? = some (.groupSuccess child [grandchild] []) := by
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [received]) valid (by cbv)
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := received_ledger_empty matching
  have prefixes := covered.atPrefixDrainOwners [failure, buffered] finish []
  have childKnown : NodeAt work grandchild .group [child.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨grandchild, [child, parent]⟩)
      (address := [1, 1, 1, 1, 0]) (groups := [⟨grandchild, [child, parent]⟩])
      (path := []) (result := { result := .ok ([("c", .scalar "c")], 0) })
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  have taskKnown : TaskAt work sharedTask [root.ref, child.ref] none
      (.object [] (.ok (sharedValue.data, 0))) :=
    .executionGroup (result := { result := .ok (sharedValue.data, 0) }) (groups := [⟨root,
      []⟩, ⟨child, [parent]⟩])
      (children := .combine .empty .empty) (owners := []) (by cbv)
  let node : TaskNode := { task := ⟨sharedTask, [root, child]⟩, value := some sharedValue }
  have emitted :=
    generated.taskSuccess_drainNoticeAncestorValue_before
      (before := [failure, buffered])
      (fun _ member => valid.eachMatches (List.mem_append_left [finish] member))
      (valid.eachMatches (List.mem_append_right [failure, buffered] List.mem_cons_self))
      (groupRecordAt_of_nodeAt childKnown)
      (ref := child.ref)
      List.mem_cons_self
      (node := node)
      ⟨none, _, taskKnown⟩
      (by simp [node])
      rfl prefixes
      (incoming := incoming)
      (by cbv)
      (by cbv)
      (by cbv; exact .tail _ (.tail _ (.head _)))
      (index := 1)
      (group := child)
      (groups := [grandchild])
      (streams := [])
      (by cbv)
      List.mem_cons_self
      (by
        cbv; intro member; cases member with
        | tail _ member =>
            cases member with
            | tail _ member => cases member)
  refine ⟨w, published, admitted, matching, ?_, ?_⟩
  · have earlier : ((initial.rawEventReplay [failure, buffered]).2.flatMap
        WorkQueueEvent.objectValues).length = 0 := by cbv
    have total : (((initial.replayGraphEvents [failure, buffered]).handleGraphEvent
        finish).2.1.flatMap WorkQueueEvent.objectValues).length = 2 := by cbv
    have count : ((released.2.1 ++ ready.drainReadyGroups.2.1.take 1).flatMap
        WorkQueueEvent.objectValues).length = 2 := by cbv
    change (sharedTask, sharedValue) ∈ ((published.drop
      ((initial.rawEventReplay [failure, buffered]).2.flatMap
        WorkQueueEvent.objectValues).length).take
        (((initial.replayGraphEvents [failure, buffered]).handleGraphEvent finish).2.1.flatMap
          WorkQueueEvent.objectValues).length).take
        ((released.2.1 ++ ready.drainReadyGroups.2.1.take 1).flatMap
          WorkQueueEvent.objectValues).length at emitted
    simpa only [earlier, total, count, List.drop_zero, List.take_take, Nat.min_self]
      using emitted
  · rw [history]; cbv

/-- The later drain notice accounts for its structural C contributor without a supplied buffer.
Witness: the end-to-end source theorem derives arrival, preparation, health, and exact
internal publication from the original mixed replay witness after cached-error cleanup.
-/
theorem structural_ancestor_before_drain_notice
    : ∃ w : ConformancePlan.Witness,
      ∃ published : List ObjectPublication,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ObjectLedgerMatching work [received] w.events w.matching published
        ∧ ∃ value, (sharedTask, value) ∈ published.take 2 := by
  obtain ⟨w, _, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [received]) valid (by cbv)
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := received_ledger_empty matching
  have childKnown : NodeAt work grandchild .group [child.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨grandchild, [child, parent]⟩)
      (address := [1, 1, 1, 1, 0]) (groups := [⟨grandchild, [child, parent]⟩])
      (path := []) (result := { result := .ok ([("c", .scalar "c")], 0) })
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  have taskKnown : TaskAt work sharedTask [root.ref, child.ref] none
      (.object [] (.ok (sharedValue.data, 0))) :=
    .executionGroup (result := { result := .ok (sharedValue.data, 0) }) (groups := [⟨root,
      []⟩, ⟨child, [parent]⟩])
      (children := .combine .empty .empty) (owners := []) (by cbv)
  have output := generated.handleGraphEvent_groupNoticeAncestor_contributor_before
    (before := [failure, buffered]) (event := finish) valid (by cbv) covered
    (position := 3) (group := child) (groups := [grandchild]) (streams := []) (by cbv)
    List.mem_cons_self (groupRecordAt_of_nodeAt childKnown)
    (ref := child.ref) List.mem_cons_self taskKnown (by simp)
  have count : ((initial.rawEventReplay [failure, buffered]).2.flatMap
      WorkQueueEvent.objectValues).length
      + ((((initial.replayGraphEvents [failure, buffered]).handleGraphEvent finish).2.1.take
          3).flatMap WorkQueueEvent.objectValues).length = 2 := by cbv
  dsimp only [initial] at count
  refine ⟨w, published, admitted, matching, ?_⟩
  simpa only [count, sharedTask] using output

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainNotices
