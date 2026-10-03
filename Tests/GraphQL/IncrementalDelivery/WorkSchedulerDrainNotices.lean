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

/-! A cached failure precedes a successful drain carrier that announces another defer. -/

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
    (.combine
      (.executionGroup [⟨root, []⟩, ⟨failed, [parent]⟩] [] (.error 1) .empty)
      (.combine
        (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] [] (.ok (sharedValue.data, 0))
          (.combine .empty .empty))
        (.combine
          (.executionGroup [⟨parent, []⟩] [] (.ok (parentValue.data, 0))
            (.combine .empty .empty))
          (.combine
            (.executionGroup [⟨grandchild, [child, parent]⟩] []
              (.ok ([("c", .scalar "c")], 0)) (.combine .empty .empty)) .empty))))

private def failure : GraphEvent := .taskFailure failedTask 1
private def buffered : GraphEvent := .taskSuccess sharedTask ⟨sharedValue, {}⟩
private def finish : GraphEvent := .taskSuccess parentTask ⟨parentValue, {}⟩
private def received : List GraphEvent := [failure, buffered, finish]
private def incoming : TaskNode := { task := ⟨parentTask, [parent]⟩ }
private def initial : State := State.initialize (Work.fromExecution work)

private def prepared : State :=
  let current := initial.replayGraphEvents [failure, buffered]
  let stored := current.putTaskNode { incoming with value := some parentValue }
  (stored.maybeIntegrateWork {} (some parentTask)).1

private def released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
private def ready : State := released.1.startNewWork released.2.2

private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0, selections, by cbv⟩

private theorem valid : ValidGraphEvents work received := by
  have failureKnown : TaskAt work failedTask [root.ref, failed.ref] none (.object [] (.error 1)) :=
    .executionGroup (groups := [⟨root, []⟩, ⟨failed, [parent]⟩])
      (children := .empty) (owners := []) (by cbv)
  have sharedKnown : TaskAt work sharedTask [root.ref, child.ref] none
      (.object [] (.ok (sharedValue.data, 0))) :=
    .executionGroup (groups := [⟨root, []⟩, ⟨child, [parent]⟩])
      (children := .combine .empty .empty) (owners := []) (by cbv)
  have parentKnown : TaskAt work parentTask [parent.ref] none
      (.object [] (.ok (parentValue.data, 0))) :=
    .executionGroup (groups := [⟨parent, []⟩])
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

/-- The generated drain emits a cached failure before the child-success notice carrier.
Witness: exact executable reduction; D is announced only by the second real iteration.
-/
theorem failure_before_notice_carrier
    : ready.drainReadyGroups.2
      = [
        .groupFailure failed 1,
        .groupValues child [sharedValue],
        .groupSuccess child [grandchild] []
      ] := by
  cbv

private theorem grandchildKnown
    : NodeAt work grandchild .group [child.ref, parent.ref] none :=
  .group (work := work) (producer := none) (group := ⟨grandchild, [child, parent]⟩)
    (address := [1, 1, 1, 1, 0]) (groups := [⟨grandchild, [child, parent]⟩])
    (path := []) (result := .ok ([("c", .scalar "c")], 0))
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
              ++ ready.drainReadyGroups.2.take 3).flatMap
              rawGroupNoticeRefs) := by
  apply List.mem_append_right
  rw [List.flatMap_append, List.flatMap_append]
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨.groupSuccess parent [failed, child] [],
    child_announced, List.mem_cons_of_mem _ List.mem_cons_self⟩

private theorem child_carrier
    : ready.drainReadyGroups.2[2]? = some (.groupSuccess child [grandchild] []) := by
  rw [failure_before_notice_carrier]
  rfl

/-- C completes by D's carrier even after an earlier cached failure in the same drain.
Witness: source-prefix tracking includes P's earlier C notice and the intervening cached
failure. The general handler theorem derives completion by the exact D carrier.
-/
theorem ancestor_completed_after_cached_failure
    : child.ref
      ∈ (((initial.rawEventReplay [failure, buffered]).2
          ++ released.2.1
          ++ ready.drainReadyGroups.2.take 3).flatMap
          rawGroupClosureRefs) := by
  have prior : ∀ source ∈ [failure, buffered], source.MatchesWork work :=
    fun _ member => valid.eachMatches (List.mem_append_left [finish] member)
  have matched := valid.eachMatches
    (List.mem_append_right [failure, buffered] List.mem_cons_self)
  exact generated.taskDrainNoticeAncestor_completed
    (before := [failure, buffered]) (occurrence := parentTask) (result := ⟨parentValue, {}⟩)
    (ref := child.ref) prior matched
    (groupRecordAt_of_nodeAt grandchildKnown)
    List.mem_cons_self
    (incoming := incoming)
    (index := 2)
    (group := child)
    (groups := [grandchild])
    (streams := [])
    child_carrier
    List.mem_cons_self
    child_uncancelled
    child_announced_before_carrier

/-- The complete raw replay closes C by D's exact carrier without a supplied health premise.
Witness: the general raw-history theorem derives noncancellation and recovers the actual
source handler and recursive-drain origin, including all earlier cached-failure output.
-/
theorem raw_notice_ancestor_completed
    : child.ref
      ∈ ((initial.rawEventReplay received).2.take 6).flatMap rawGroupClosureRefs := by
  have selected : (initial.rawEventReplay received).2[5]?
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
          (State.drainReadyGroups.go fuel ready).1.CachedFailuresSupported work
            [failedTask])
      ∧ ∃ owners, TaskHasOwners work failedTask owners ∧ failed.ref ∈ owners := by
  have prior : ValidGraphEvents work [failure, buffered] :=
    valid.prefix ⟨[finish], rfl⟩
  have supported := generated.taskSuccess_drain_cachedAcceptedFailures
    (occurrence := parentTask) (result := ⟨parentValue, {}⟩) prior (by cbv) incoming
  have inventory : initial.objectFailureContributions [failure, buffered] = [failedTask] := by
    cbv
  change ready.CachedFailuresSupported work
    (initial.objectFailureContributions [failure, buffered]) at supported
  rw [inventory] at supported
  refine ⟨supported, supported.drainReadyGroups_go, ?_⟩
  have cache : ∃ node ∈ ready.groupNodes,
      node.group.node = failed ∧ node.failure.isSome = true := by
    refine ⟨{ group := ⟨failed, some parent.ref⟩, failure := some 1 }, ?_, rfl, rfl⟩
    cbv
    exact .head _
  obtain ⟨node, member, same, cached⟩ := cache
  obtain ⟨occurrence, accepted, owners, known, owner⟩ := supported node member cached
  obtain rfl := List.mem_singleton.mp accepted
  exact ⟨owners, known, same ▸ owner⟩

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
        ∧ ∃ steps,
            steps < ready.groupNodes.length
            ∧ ready.drainReadyGroups.2.take 3
              = (State.drainReadyGroups.go (steps + 1) ready).2
            ∧ ∃ node,
                (State.drainReadyGroups.go (steps + 1) ready).1.groupNode? grandchild.ref
                  = some node
                ∧ node.group.node = grandchild
                ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
                ∧ ∀ publication ∈ published.take 2, publication.1 ∉ node.tasks := by
  have started : inputsStarted work [received] = true := by cbv
  obtain ⟨w, _, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [received]) valid started
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rwa [← inputsStarted_eq_batchesStarted])
  obtain ⟨steps, bounded, exactPrefix, _, node, found, same, contents, excluded⟩ :=
    generated.taskSuccess_drainNoticeContents (before := [failure, buffered]) (after := [])
      (incoming := incoming) (index := 2) (group := child) (groups := [grandchild]) (streams := [])
      covered valid (by cbv) (by cbv) (by cbv) List.mem_cons_self
  refine ⟨w, published, admitted, matching, steps, bounded, exactPrefix,
    node, found, same, contents, ?_⟩
  intro publication member
  apply excluded publication
  have count : ((initial.rawEventReplay [failure, buffered]).2.flatMap
      WorkQueueEvent.objectValues).length
      + ((released.2.1 ++ ready.drainReadyGroups.2.take 2).flatMap
        WorkQueueEvent.objectValues).length = 2 := by cbv
  change publication ∈ published.take
    (((initial.rawEventReplay [failure, buffered]).2.flatMap WorkQueueEvent.objectValues).length
      + ((released.2.1 ++ ready.drainReadyGroups.2.take 2).flatMap
        WorkQueueEvent.objectValues).length)
  rw [count]
  exact member

/-- The atomic carrier after cached failure cleanup retains semantically unpublished tasks.
Witness: apply the general canonical group-carrier theorem to the actual sixth output.
The test supplies neither a drain step nor a ledger count, and keeps object admission
on the same witness with the same failure cuts and publication matching.
-/
theorem atomic_notice_after_failure_unpublished
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[5]? = some (.groupSuccess child [grandchild] [])
        ∧ RetainedNoticeContents work w.matching (w.events.take 5)
            (failedBefore w.failures 5) received grandchild := by
  obtain ⟨w, history, _, _, _, _, _, streamReady, _, _, ledger, _, _, _, admitted,
    streamCuts, _, exactCuts⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates_with_cuts generated
      (inputs := [received]) valid (by cbv)
  have selected : w.events[5]? = some (.groupSuccess child [grandchild] []) := by
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
      (streamCuts ++ sourceObjectFailureCuts 0
        (initial.eligibleFailureBlocks
          (initial.sourceRunBlocks
            { active := initial.initialGroups ++ initial.initialStreams } [received]).2.2)) := by
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
in the recovered source prefix; the theorem supplies the publication count and cache law.
-/
theorem atomic_handler_cache_supported
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ∃ before source after,
          ∃ publisher : IncrementalPublisher,
          ∃ localIndex,
            received = before ++ source :: after
            ∧ let current := initial.replayGraphEvents before
              ((publisher.normalizeBatch (current.handleGraphEvent source).2).2.flatMap
                  publicationAtoms)[localIndex]?
                = some (.groupSuccess parent [failed, child] [])
              ∧ ((w.events.take 2).flatMap normalizedObjectValues).length
                = ((initial.rawEventReplay before).2.flatMap
                    WorkQueueEvent.objectValues).length
                  + ((((publisher.normalizeBatch
                          (current.handleGraphEvent source).2).2.flatMap
                        publicationAtoms).take
                        localIndex).flatMap
                      normalizedObjectValues).length
              ∧ current.CachedFailuresSupported work (failedBefore w.failures 2) := by
  obtain ⟨w, history, _, _, _, _, _, _, _, _, _, _, _, _, admitted,
    streams, _, exactCuts⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates_with_cuts generated
      (inputs := [received]) valid (by cbv)
  have selected : w.events[2]? = some (.groupSuccess parent [failed, child] []) := by
    rw [history]
    cbv
  refine ⟨w, admitted, ?_⟩
  apply ConformancePlan.Witness.handlerBoundary_cachedFailures
    (inputs := [received]) generated valid (by cbv) history (streams := streams)
    (selected := selected)
  rw [exactCuts]
  exact mergeFailureCuts_partition _ _

/-- An error-only child is eligible before its immediate cached-error completion.
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
      (path := []) (result := .error 1) (children := .empty) (owners := [])
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

/-- A cached error's newly announced group actually completes in the same handler.
Witness: general exact notice tracking, not mere membership in cancelledGroups, forces
the closure once the concrete end state no longer contains F as an active root.
-/
theorem cached_error_notice_completed
    : failed.ref ∈ (initial.rawEventReplay received).2.flatMap rawGroupClosureRefs := by
  have tracked := generated.rawEventReplay_groupNoticeCompletion received
    (fun _ member => valid.eachMatches member) failed.ref (by
      cbv
      change (2 : Nat) ∈ [0, 1, 2, 3, 4]
      decide)
  exact tracked.resolve_left
    (by
      cbv
      change (2 : Nat) ∉ [4]
      decide)

/-- Every announced group in this mixed success/failure prefix remains active or closes.
Witness: general generated matching replay; transient failures do not weaken the endpoint
to an unexplained cancellation marker, even when later group work remains outstanding.
-/
theorem cached_failure_group_notices_tracked
    : GroupNoticeCompletion initial.rootGroups (initial.rawEventReplay received) :=
  generated.rawEventReplay_groupNoticeCompletion received
    (fun _ member => valid.eachMatches member)

/-- F's cached failure does not invalidate P, whose completion announces F and C.
Witness: the general actual-replay theorem certifies the entire handler's notice ancestry
under its accepted failures. The failed child itself is deliberately not claimed healthy.
-/
theorem cached_error_notice_ancestors_healthy
    : GroupNoticeAncestorsHealthy work (initial.objectFailureContributions received)
        ((initial.replayGraphEvents [failure, buffered]).handleGraphEvent finish).2 :=
  generated.replayGraphEvents_next_noticeAncestorsHealthy valid (by cbv)

/-- Later removal of the noticed F child does not erase its parent-retirement certificate.
Witness: the actual replay theorem retains ancestry for every notice in the handler,
including F's owner-fold notice and D's later drain notice after F's failed cleanup.
-/
theorem cached_error_notice_ancestors_retired
    : (initial.replayGraphEvents received).GroupNoticeAncestorsRetired work
        ((initial.replayGraphEvents [failure, buffered]).handleGraphEvent finish).2 := by
  apply generated.replayGraphEvents_next_noticeAncestorsRetired
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
        ∧ w.events[5]? = some (.groupSuccess child [grandchild] []) := by
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [received]) valid (by cbv)
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rw [← inputsStarted_eq_batchesStarted]; cbv)
  have prefixes := covered.atPrefixDrainOwners [failure, buffered] finish []
  have childKnown : NodeAt work grandchild .group [child.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨grandchild, [child, parent]⟩)
      (address := [1, 1, 1, 1, 0]) (groups := [⟨grandchild, [child, parent]⟩])
      (path := []) (result := .ok ([("c", .scalar "c")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  have taskKnown : TaskAt work sharedTask [root.ref, child.ref] none
      (.object [] (.ok (sharedValue.data, 0))) :=
    .executionGroup (groups := [⟨root, []⟩, ⟨child, [parent]⟩])
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
      (by cbv)
      (by cbv; exact .tail _ (.tail _ (.head _)))
      (index := 2)
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
        finish).2.flatMap WorkQueueEvent.objectValues).length = 2 := by cbv
    have count : ((released.2.1 ++ ready.drainReadyGroups.2.take 2).flatMap
        WorkQueueEvent.objectValues).length = 2 := by cbv
    change (sharedTask, sharedValue) ∈ ((published.drop
      ((initial.rawEventReplay [failure, buffered]).2.flatMap
        WorkQueueEvent.objectValues).length).take
        (((initial.replayGraphEvents [failure, buffered]).handleGraphEvent finish).2.flatMap
          WorkQueueEvent.objectValues).length).take
        ((released.2.1 ++ ready.drainReadyGroups.2.take 2).flatMap
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
  have covered := batches.flatten (by rw [← inputsStarted_eq_batchesStarted]; cbv)
  have childKnown : NodeAt work grandchild .group [child.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨grandchild, [child, parent]⟩)
      (address := [1, 1, 1, 1, 0]) (groups := [⟨grandchild, [child, parent]⟩])
      (path := []) (result := .ok ([("c", .scalar "c")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  have taskKnown : TaskAt work sharedTask [root.ref, child.ref] none
      (.object [] (.ok (sharedValue.data, 0))) :=
    .executionGroup (groups := [⟨root, []⟩, ⟨child, [parent]⟩])
      (children := .combine .empty .empty) (owners := []) (by cbv)
  have output := generated.handleGraphEvent_groupNoticeAncestor_contributor_before
    (before := [failure, buffered]) (event := finish) valid (by cbv) covered
    (position := 4) (group := child) (groups := [grandchild]) (streams := []) (by cbv)
    List.mem_cons_self (groupRecordAt_of_nodeAt childKnown)
    (ref := child.ref) List.mem_cons_self taskKnown (by simp)
  have count : ((initial.rawEventReplay [failure, buffered]).2.flatMap
      WorkQueueEvent.objectValues).length
      + ((((initial.replayGraphEvents [failure, buffered]).handleGraphEvent finish).2.take
          4).flatMap WorkQueueEvent.objectValues).length = 2 := by cbv
  dsimp only [initial] at count
  refine ⟨w, published, admitted, matching, ?_⟩
  simpa only [count, sharedTask] using output

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainNotices
