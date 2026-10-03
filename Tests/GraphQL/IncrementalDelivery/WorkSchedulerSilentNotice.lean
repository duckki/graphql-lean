import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorContributors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeAncestorPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeAncestorAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorSemantics
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPresenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalNoticeCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeSourceFreshness
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A real notice crosses an unannounced task-bearing ancestor removed in the owner fold. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerSilentNotice
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def root : DeliveryNode := ⟨0, [], some (.string "R")⟩
private def parent : DeliveryNode := ⟨1, [], some (.string "P")⟩
private def silent : DeliveryNode := ⟨2, [], some (.string "S")⟩
private def child : DeliveryNode := ⟨3, [], some (.string "C")⟩
private def occurrence : Occurrence := .executionGroup [1, 0]

private def value : ExecutionGroupValue :=
  {
    path := [],
    data := [("a", .scalar "a")],
    errors := 0,
    deliveryGroups := [root, silent]
  }

private def first : GraphEvent := .taskSuccess occurrence ⟨value, {}⟩
private def lastOccurrence : Occurrence := .executionGroup [1, 1, 0]

private def lastValue : ExecutionGroupValue :=
  {
    path := [],
    data := [("b", .scalar "b")],
    errors := 0,
    deliveryGroups := [root, parent]
  }

private def incoming : TaskNode := { task := ⟨lastOccurrence, [root, parent]⟩ }

private def buffered : TaskNode :=
  { task := ⟨occurrence, [root, silent]⟩, value := some value }

private def result : TaskResult := ⟨lastValue, {}⟩
private def event : GraphEvent := .taskSuccess lastOccurrence result

private def selections : List Selection :=
  [
    defer [field "a", field "b"] (some "R"),
    defer [field "b", defer [field "a", defer [field "c"] (some "C")] (some "S")]
      (some "P")
  ]

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨root, []⟩, ⟨silent, [parent]⟩] [] (.ok (value.data, 0))
        (.combine .empty .empty))
      (.combine
        (.executionGroup [⟨root, []⟩, ⟨parent, []⟩] [] (.ok (lastValue.data, 0))
          (.combine .empty .empty))
        (.combine
          (.executionGroup [⟨child, [silent, parent]⟩] [] (.ok ([("c", .scalar "c")], 0))
            (.combine .empty .empty)) .empty)))

private def initial : State := State.initialize (Work.fromExecution work)

private def prepared : State :=
  (((initial.replayGraphEvents [first]).putTaskNode
      { incoming with value := some lastValue }).maybeIntegrateWork
    {} (some lastOccurrence)).1

private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0, selections, by cbv⟩

private theorem known
    : TaskAt work occurrence [root.ref, silent.ref] none
        (.object [] (.ok (value.data, 0))) :=
  .executionGroup (groups := [⟨root, []⟩, ⟨silent, [parent]⟩])
    (children := .combine .empty .empty) (owners := []) (by cbv)

private theorem lastKnown
    : TaskAt work lastOccurrence [root.ref, parent.ref] none
        (.object [] (.ok (lastValue.data, 0))) :=
  .executionGroup (groups := [⟨root, []⟩, ⟨parent, []⟩])
    (children := .combine .empty .empty) (owners := []) (by cbv)

private theorem matched : event.MatchesWork work := ⟨_, _, lastKnown, by cbv, by cbv⟩

private theorem valid : ValidGraphEvents work [first, event] := by
  have one : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, known, by cbv, by cbv⟩
      (by simp [GraphEvent.Fresh, first, GraphEvent.identities])
      ⟨_, _, _, known, by intro source impossible; cases impossible⟩
  exact .append one matched
    (by
      simp [GraphEvent.Fresh, first, event, GraphEvent.identities, occurrence, lastOccurrence])
    ⟨_, _, _, lastKnown, by intro source impossible; cases impossible⟩

/-- The later shared settlement cannot repeat either initial root or an earlier notice.
Witness: the general cross-input exclusion theorem follows the actual silent-ancestor
owner pass and its drain, requiring matching inputs but no abstract output admission.
-/
theorem shared_handler_does_not_reannounce {ref}
    (announced
      : ref
        ∈ initial.rootGroups
          ++ (initial.rawEventReplay [first]).2.flatMap rawGroupNoticeRefs)
    : ref
      ∉ ((initial.replayGraphEvents [first]).handleGraphEvent event).2.flatMap
          rawGroupNoticeRefs := by
  apply generated.handleGraphEvent_noEarlierGroupNotice (event := event)
    (before := [first]) _ matched announced
  intro source member
  obtain rfl := List.mem_singleton.mp member
  exact valid.eachMatches List.mem_cons_self

/-- Closing R preserves the live P root needed by the next single-pass contributor step.
Witness: generated ancestry protects P from R's flush and recursive taskless pruning.
The proof uses the prepared source boundary, not the final handler state or admission.
-/
theorem closing_root_preserves_other_root
    : ∃ closing,
        prepared.groupNode? root.ref = some closing
        ∧ parent.ref
          ∈ (prepared.finishGroupSuccess closing).1.groupNodes.map
              (fun node => node.group.node.ref) := by
  obtain ⟨parents, canonical, records, links, live, tasks, roots, _⟩ :=
    generated.replayGraphEvents_preparedRetirement [first]
      (by intro source member; obtain rfl := List.mem_singleton.mp member;
          exact ⟨_, _, known, by cbv, by cbv⟩) matched incoming
  have existsClosing : ∃ closing, prepared.groupNode? root.ref = some closing := by
    exact ⟨_, rfl⟩
  obtain ⟨closing, found⟩ := existsClosing
  have same := State.groupNode?_ref found
  refine ⟨closing, found, ?_⟩
  have rootProtected := roots parent.ref (by cbv; exact .tail _ (.head _))
  exact rootProtected.supported_finishGroupSuccess_present generated records links
    canonical
    (by cbv; exact .tail _ (.head _))
    (same.symm ▸ found)
    ⟨none, _, known⟩
    (same.symm ▸ List.mem_cons_self)
    (by rw [same]; decide)

/-- P's announcement is discharged by its actual completion when it carries C's notice.
Witness: source-prefix notice tracking and the generic exact-owner-boundary theorem.
It does not borrow the final drain's output or assume notice admission or root presence.
-/
theorem parent_completed_by_child_carrier
    : parent.ref
      ∈ ((([root, parent].foldl successGroupStep (prepared, [], {})).2.1.take 3).flatMap
          rawGroupClosureRefs) := by
  have firstMatches : ∀ source ∈ [first], source.MatchesWork work := by
    intro source member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, _, known, by cbv, by cbv⟩
  have childKnown : NodeAt work child .group [silent.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨child, [silent, parent]⟩)
      (address := [1, 1, 1, 0]) (groups := [⟨child, [silent, parent]⟩])
      (path := []) (result := .ok ([("c", .scalar "c")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  have closed := generated.ownerNoticeAncestor_completed firstMatches matched
    (groupRecordAt_of_nodeAt childKnown)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (incoming := incoming) (index := 2) (group := parent) (groups := [child]) (streams := [])
    (by cbv) List.mem_cons_self (by cbv; intro impossible; cases impossible)
    (List.mem_append_left _ (by cbv; exact .tail _ (.head _)))
  have emptyOutput : (initial.rawEventReplay [first]).2 = [] := by cbv
  change parent.ref ∈ (((initial.rawEventReplay [first]).2 ++
    (([root, parent].foldl successGroupStep (prepared, [], {})).2.1.take 3)).flatMap
      rawGroupClosureRefs) at closed
  rw [emptyOutput, List.nil_append] at closed
  exact closed

/-- P announces C after R's shared value silently exhausts the intervening S record.
Witness: exact reduction of the generated work and single-pass handler. S is a real
contributing owner, yet is never announced or completed; C is retained for future work.
-/
theorem silent_ancestor_carrier
    : ((initial.replayGraphEvents [first]).handleGraphEvent event).2
        = [
          .groupValues root [value, lastValue],
          .groupSuccess root [] [],
          .groupSuccess parent [child] []
        ]
      ∧ (([root, parent].foldl successGroupStep (prepared, [], {})).1).RetiredGroup
          silent.ref
      ∧ silent.ref ∉ initial.initialGroups.map DeliveryNode.ref := by
  refine ⟨by cbv, ⟨?_, ?_⟩, ?_⟩
  · cbv; exact .tail _ (.tail _ (.head _))
  · cbv; intro impossible; cases impossible; contradiction
  · cbv; intro member; cases member with
    | tail _ member =>
        cases member with
        | tail _ member => cases member

/-- The canonical witness accounts for S's buffered contributor before C's notice.
Witness: recover the stronger owner-prefix certificate from the existing replay ledger.
The general ancestor theorem uses concrete retirement at P's exact carrier boundary,
not an S completion, a second matching or the handler's final state.
-/
theorem silent_ancestor_published_before_notice
    : ∃ w : ConformancePlan.Witness,
      ∃ published : List ObjectPublication,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ObjectLedgerMatching work [[first, event]] w.events w.matching published
        ∧ (occurrence, value) ∈ published.take 2
        ∧ w.events[3]? = some (.groupSuccess parent [child] []) := by
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [[first, event]]) valid (by cbv)
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rw [← inputsStarted_eq_batchesStarted]; cbv)
  have ownerPrefixes := covered.atPrefixDrainOwners [first] event []
  have certificates := ownerPrefixes incoming (by cbv) (by cbv)
  obtain ⟨parents, canonical, records, links, live, tasks, roots, _⟩ :=
    generated.replayGraphEvents_preparedRetirement [first]
      (by intro source member; obtain rfl := List.mem_singleton.mp member;
          exact ⟨_, _, known, by cbv, by cbv⟩) matched incoming
  have childKnown : NodeAt work child .group [silent.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨child, [silent, parent]⟩)
      (address := [1, 1, 1, 0]) (groups := [⟨child, [silent, parent]⟩])
      (path := []) (result := .ok ([("c", .scalar "c")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  have emitted := certificates.ownerCarrier_ancestorValue generated records links canonical
    live tasks roots (index := 2) (group := parent) (groups := [child]) (streams := [])
    (by cbv) List.mem_cons_self (groupRecordAt_of_nodeAt childKnown)
    (ref := silent.ref) List.mem_cons_self (occurrence := occurrence)
    (node := buffered) (value := value)
    (by cbv) rfl ⟨none, _, known⟩ (by simp [buffered])
    (by cbv; exact .tail _ (.tail _ (.head _)))
    (by cbv; intro impossible; cases impossible)
  refine ⟨w, published, admitted, matching, ?_, ?_⟩
  · have earlier : ((initial.rawEventReplay [first]).2.flatMap
        WorkQueueEvent.objectValues).length = 0 := by cbv
    have total : (((initial.replayGraphEvents [first]).handleGraphEvent event).2.flatMap
        WorkQueueEvent.objectValues).length = 2 := by cbv
    have localCount : ((([root, parent].foldl successGroupStep (prepared, [], {})).2.1.take
        2).flatMap WorkQueueEvent.objectValues).length = 2 := by cbv
    change (occurrence, value) ∈ ((published.drop
      ((initial.rawEventReplay [first]).2.flatMap WorkQueueEvent.objectValues).length).take
        (((initial.replayGraphEvents [first]).handleGraphEvent event).2.flatMap
          WorkQueueEvent.objectValues).length).take
        ((([root, parent].foldl successGroupStep (prepared, [], {})).2.1.take 2).flatMap
          WorkQueueEvent.objectValues).length at emitted
    simpa only [earlier, total, localCount, List.drop_zero, List.take_take, Nat.min_self]
      using emitted
  · rw [history]; cbv

/-- The silent S ancestor remains healthy when C is announced by P's own carrier.
Witness: apply general source-boundary notice health to the actual emitted event and
the generated C record. Concrete cancellation is excluded without a separate guard or
notice-admission assumption; S's own completion remains absent.
-/
theorem silent_ancestor_healthy
    : ¬GroupRecordInvalidated work (initial.objectFailureContributions [first, event])
        silent.ref
      ∧ silent.ref ∉ (initial.replayGraphEvents [first, event]).cancelledGroups := by
  have childKnown : NodeAt work child .group [silent.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨child, [silent, parent]⟩)
      (address := [1, 1, 1, 0]) (groups := [⟨child, [silent, parent]⟩])
      (path := []) (result := .ok ([("c", .scalar "c")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  apply generated.noticeAncestor_healthy_uncancelled
    (before := [first])
    (event := event)
    valid
    (by cbv)
    (output := .groupSuccess parent [child] [])
    (by
      change _ ∈ ((initial.replayGraphEvents [first]).handleGraphEvent event).2
      rw [silent_ancestor_carrier.1]
      simp)
    (by simp [rawGroupNoticeRefs])
    (groupRecordAt_of_nodeAt childKnown)
    List.mem_cons_self

/-- Silent S's structural a contributor has actually succeeded before C is announced.
Witness: the general notice-ancestor theorem recovers its source event from structural
ownership, even though S has no wire completion and its live record has been pruned.
-/
theorem silent_ancestor_contributor_succeeded
    : ∃ result, GraphEvent.taskSuccess occurrence result ∈ [first, event] := by
  have childKnown : NodeAt work child .group [silent.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨child, [silent, parent]⟩)
      (address := [1, 1, 1, 0]) (groups := [⟨child, [silent, parent]⟩])
      (path := []) (result := .ok ([("c", .scalar "c")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  exact generated.noticeAncestor_structuralContributor_succeeded
    (before := [first])
    (event := event)
    valid
    (by cbv)
    (output := .groupSuccess parent [child] [])
    (by
      change _ ∈ ((initial.replayGraphEvents [first]).handleGraphEvent event).2
      rw [silent_ancestor_carrier.1]
      simp)
    (by simp [rawGroupNoticeRefs])
    (groupRecordAt_of_nodeAt childKnown)
    List.mem_cons_self known
    (by simp)

/-- Both earlier S data and the current P input precede C's notice without storage premises.
Witness: apply the general source-to-notice theorem twice on one canonical replay ledger.
It derives the buffered and newly installed branches itself; the test supplies only the
actual notice, generated ancestry, and the two original structural contributors.
-/
theorem all_ancestor_contributors_before_notice
    : ∃ w : ConformancePlan.Witness,
      ∃ published : List ObjectPublication,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ ObjectLedgerMatching work [[first, event]] w.events w.matching published
        ∧ (∃ value, (occurrence, value) ∈ published.take 2)
        ∧ (∃ value, (lastOccurrence, value) ∈ published.take 2) := by
  obtain ⟨w, _, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [[first, event]]) valid (by cbv)
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rw [← inputsStarted_eq_batchesStarted]; cbv)
  have childKnown : NodeAt work child .group [silent.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨child, [silent, parent]⟩)
      (address := [1, 1, 1, 0]) (groups := [⟨child, [silent, parent]⟩])
      (path := []) (result := .ok ([("c", .scalar "c")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  have selected : ((initial.replayGraphEvents [first]).handleGraphEvent event).2[2]?
      = some (.groupSuccess parent [child] []) := by rw [silent_ancestor_carrier.1]; rfl
  have firstOutput := generated.handleGraphEvent_groupNoticeAncestor_contributor_before
    (before := [first]) (event := event) valid (by cbv) covered selected List.mem_cons_self
    (groupRecordAt_of_nodeAt childKnown) (ref := silent.ref) List.mem_cons_self known
    (by simp)
  have lastOutput := generated.handleGraphEvent_groupNoticeAncestor_contributor_before
    (before := [first]) (event := event) valid (by cbv) covered selected List.mem_cons_self
    (groupRecordAt_of_nodeAt childKnown) (ref := parent.ref) (by simp) lastKnown (by simp)
  have count : ((initial.rawEventReplay [first]).2.flatMap WorkQueueEvent.objectValues).length
      + ((((initial.replayGraphEvents [first]).handleGraphEvent event).2.take 2).flatMap
          WorkQueueEvent.objectValues).length = 2 := by cbv
  dsimp only [initial] at count
  refine ⟨w, published, admitted, matching, ?_, ?_⟩
  · simpa only [count, occurrence] using firstOutput
  · simpa only [count, lastOccurrence] using lastOutput

/-- Both silently retired S and closing P are semantically accounted before C's notice.
Witness: the canonical ancestor-accounting theorem interprets every structural contributor
on the existing matching. The proof uses the event-start frozen failure cuts and requires
neither an S completion nor assumed notice admission.
-/
theorem notice_ancestors_accounted_on_common_witness
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[3]? = some (.groupSuccess parent [child] [])
        ∧ ∀ ref ∈ [silent.ref, parent.ref],
            NodeAccounted work w.matching (w.events.take 3)
              (w.failures.filter (fun entry => entry.1 ≤ 3)) ref := by
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [[first, event]]) valid (by cbv)
  have childKnown : NodeAt work child .group [silent.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨child, [silent, parent]⟩)
      (address := [1, 1, 1, 0]) (groups := [⟨child, [silent, parent]⟩])
      (path := []) (result := .ok ([("c", .scalar "c")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  have selected : w.events[3]? = some (.groupSuccess parent [child] []) := by rw [history]; cbv
  refine ⟨w, admitted, selected, ?_⟩
  intro ref member
  exact ConformancePlan.groupNoticeAncestor_nodeAccounted generated
    (inputs := [[first, event]]) valid (by cbv) history ledger selected List.mem_cons_self
    (groupRecordAt_of_nodeAt childKnown) member _

/-- A silently retired ancestor and a closing ancestor are both ready at the carrier cut.
Witness: the generic canonical dependency theorem derives health, task accounting, and
announcement/completion status together. No fixture-specific status alternative is used.
-/
theorem notice_ancestors_ready_at_carrier
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ w.events[3]? = some (.groupSuccess parent [child] [])
        ∧ ∀ ref ∈ [silent.ref, parent.ref],
            DependencySatisfied work (ConformancePlan.initialRefs work) w.matching
              (w.events.take 3 ++ [.groupSuccess parent [] []])
              (w.failures.filter (fun entry => entry.1 ≤ 3)) ref := by
  obtain ⟨w, history, _, announced, _, _, _, _, _, _, ledger, _, support, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated
      (inputs := [[first, event]]) valid (by cbv)
  have childKnown : NodeAt work child .group [silent.ref, parent.ref] none :=
    .group (work := work) (producer := none) (group := ⟨child, [silent, parent]⟩)
      (address := [1, 1, 1, 0]) (groups := [⟨child, [silent, parent]⟩])
      (path := []) (result := .ok ([("c", .scalar "c")], 0))
      (children := .combine .empty .empty) (owners := []) (by cbv) List.mem_cons_self
  have selected : w.events[3]? = some (.groupSuccess parent [child] []) := by rw [history]; cbv
  exact ⟨
    w,
    admitted,
    selected,
    ConformancePlan.groupNoticeAncestor_dependencySatisfied (inputs := [[first, event]])
      generated valid (by cbv) history ledger support announced selected
      List.mem_cons_self (groupRecordAt_of_nodeAt childKnown)
  ⟩

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerSilentNotice
