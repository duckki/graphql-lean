import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeContents

/-! Concrete retained memberships are unpublished under the same atomic matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The exact object ledger also recovers labels from already observed publications
-----------------------------------------------------------------------------------------

/-- A nonempty object event contributes its exact matched label to every later prefix.
Witness: its object rank is strictly below the later prefix's object count; the shared
ledger's indexed label is therefore in that prefix. No payload equality selects a task.
-/
theorem ObjectLedgerMatching.objectPublication_before
    {work inputs events matching published position index group values}
    (ledger : ObjectLedgerMatching work inputs events matching published)
    (selected : events[position]? = some (.groupValues group values))
    (nonempty : values ≠ []) (earlier : position < index)
    : ∃ value,
        (matching position, value)
        ∈ published.take ((events.take index).flatMap normalizedObjectValues).length := by
  have rank := ledger.atObject position group values selected
  have counts : ((events.take position).flatMap normalizedObjectValues).length
      < ((events.take index).flatMap normalizedObjectValues).length := by
    have splitIndex : index = (position + 1) + (index - (position + 1)) := by omega
    rw [splitIndex, List.take_add, List.flatMap_append, List.length_append,
      List.take_add_one, selected, Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, normalizedObjectValues, WorkQueueEvent.objectValues,
      List.length_append]
    have positive : 0 < values.length := List.length_pos_iff.mpr nonempty
    omega
  rw [List.getElem?_map] at rank
  cases found
        : published[((events.take position).flatMap normalizedObjectValues).length]? with
  | none => simp only [found, Option.map_none, reduceCtorEq] at rank
  | some entry =>
      have same : entry.1 = matching position := by
        simpa only [found, Option.map_some, Option.some.injEq] using rank
      refine ⟨entry.2, ?_⟩
      have inPrefix : entry ∈ published.take
          ((events.take index).flatMap normalizedObjectValues).length :=
        List.mem_of_getElem? ((List.getElem?_take_of_lt counts).trans found)
      simpa only [← same] using inPrefix

namespace ConformancePlan

/-- Every published object occurrence belongs to the same ledger's observed prefix.
Witness: object admission rules out empty value events and supplies the indexed label;
stream provenance prevents an item event from impersonating an object occurrence.
This is the reverse of the common ledger's existing publication interpretation, without
assuming admission of carried notices or of the whole history.
-/
theorem objectOccurrence_published_mem
    {work inputs w published index address}
    (ledger : ObjectLedgerMatching work inputs w.events w.matching published)
    (objects : GroupPublicationAdmission work w)
    (streams : StreamPublicationReady work w)
    (observed : Published w.matching (w.events.take index) (.executionGroup address))
    : ∃ value,
        (.executionGroup address, value)
        ∈ published.take
            ((w.events.take index).flatMap normalizedObjectValues).length := by
  obtain ⟨position, event, atPrefix, isValue, same⟩ := observed
  have inside : position < index := by
    have bounded := (List.getElem?_eq_some_iff.mp atPrefix).1
    simp only [List.length_take] at bounded
    omega
  have selected := (List.getElem?_take_of_lt inside).symm.trans atPrefix
  cases event with
  | groupValues group values =>
      obtain ⟨_, _, _, singleton, _⟩ := objects position group values selected
      have nonempty : values ≠ [] := by simp [singleton]
      simpa only [same] using ledger.objectPublication_before selected nonempty inside
  | streamValues stream values groups children =>
      obtain ⟨_, _, _, known, _⟩ := streams position stream values groups children selected
      rw [same] at known
      simp [TaskAt] at known
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases isValue

/-- Excluding observed object labels from a retained record excludes semantic publication.
Witness: membership soundness identifies each retained occurrence as an object task;
the reverse ledger theorem places any purported publication in the excluded prefix.
Stream publications cannot provide a second route around the object-label exclusion.
-/
theorem retainedGroupMembers_unpublished
    {work inputs w published index} {queue : State} {node : GroupNode}
    (ledger : ObjectLedgerMatching work inputs w.events w.matching published)
    (objects : GroupPublicationAdmission work w)
    (streams : StreamPublicationReady work w)
    (sound : queue.GroupMembershipSound) (registered : queue.RegisteredTasksMatch work)
    (member : node ∈ queue.groupNodes)
    (excluded
      : ∀ publication ∈
          published.take ((w.events.take index).flatMap normalizedObjectValues).length,
          publication.1 ∉ node.tasks)
    : ∀ occurrence ∈ node.tasks,
        ¬Published w.matching (w.events.take index) occurrence := by
  intro occurrence listed observed
  obtain ⟨task, taskMember, same, _⟩ := sound node member occurrence listed
  obtain ⟨address, _, _, kind, _⟩ := (registered task taskMember).1
  have object : occurrence = .executionGroup address := same.symm.trans kind
  obtain ⟨value, inLedger⟩ := objectOccurrence_published_mem ledger objects streams
    (object ▸ observed)
  exact excluded (.executionGroup address, value) inLedger (object ▸ listed)

end ConformancePlan

-----------------------------------------------------------------------------------------
-- Actual item boundaries derive their task metadata instead of assuming it
-----------------------------------------------------------------------------------------

/-- Matching sequential replay retains sound memberships and exact registered tasks.
Witness: pair the two existing handler-preservation facts in the actual source fold.
-/
theorem State.replay_noticeTaskProvenance {queue : State} {work}
    (sound : queue.GroupMembershipSound) (registered : queue.RegisteredTasksMatch work)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.replayGraphEvents events).GroupMembershipSound
      ∧ (queue.replayGraphEvents events).RegisteredTasksMatch work := by
  induction events generalizing queue with
  | nil => exact ⟨sound, registered⟩
  | cons event rest ih =>
      exact ih (sound.handleGraphEvent event)
        (registered.handleGraphEvent event (matching event List.mem_cons_self))
        (fun next member => matching next (List.mem_cons_of_mem _ member))

/-- A matched item's integration preserves the metadata of every retained membership.
Witness: exact child-task descriptors justify registration, while pruning and activation
preserve both independent state invariants.
-/
theorem State.integrateStreamItem_noticeTaskProvenance {queue : State}
    {work stream items item}
    (sound : queue.GroupMembershipSound) (registered : queue.RegisteredTasksMatch work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items)
    : (queue.integrateStreamItem item).GroupMembershipSound
      ∧ (queue.integrateStreamItem item).RegisteredTasksMatch work := by
  have integrated := registered.maybeIntegrateWork item.work (by
    intro task candidate
    obtain ⟨address, payload, same, known⟩ :=
      matching.streamItem_childTask_producer member candidate
    exact ⟨⟨address, payload, some item.occurrence, same, known⟩,
      matching.streamItem_childTask_groupsExact member candidate⟩)
  exact ⟨((sound.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
    (integrated.pruneEmptyGroups _).startNewWork _⟩

/-- An actual item-prefix boundary retains the metadata needed for publication exclusion.
Witness: project the invariant through the concrete metadata-carrying fold, using the
original event's matching evidence for every included input item.
-/
theorem State.preparedStreamItems_noticeTaskProvenance {queue : State} {work stream items}
    (sound : queue.GroupMembershipSound) (registered : queue.RegisteredTasksMatch work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (earlier : List StreamItem) (included : earlier.Subset items)
    : (queue.preparedStreamItems earlier).GroupMembershipSound
      ∧ (queue.preparedStreamItems earlier).RegisteredTasksMatch work := by
  apply State.preparedStreamItems_preserves
    (fun current => current.GroupMembershipSound ∧ current.RegisteredTasksMatch work)
    ⟨sound, registered⟩ earlier
  intro current item member prior
  exact State.integrateStreamItem_noticeTaskProvenance prior.1 prior.2 matching
    (included member)

/-- A leading group notice retains only unpublished tasks on the common atomic matching.
Witness: its concrete integration boundary supplies contents and earlier-label exclusion;
derive that boundary's task metadata from replay and interpret exclusion semantically.
The count equation is the remaining raw-to-atomic boundary bridge, not a scheduler law.
-/
theorem ExecutedWork.streamItems_leadingNotice_unpublished
    {work before stream items after published child inputs w index}
    (generated : ExecutedWork work)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ .streamItems stream items :: after) published)
    (valid : ValidGraphEvents work (before ++ .streamItems stream items :: after))
    (ledger : ObjectLedgerMatching work inputs w.events w.matching published)
    (objects : ConformancePlan.GroupPublicationAdmission work w)
    (streams : ConformancePlan.StreamPublicationReady work w)
    (count
      : ((w.events.take index).flatMap normalizedObjectValues).length
        = (((State.initialize (Work.fromExecution work)).rawEventReplay before).2.flatMap
            WorkQueueEvent.objectValues).length)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      child ∈ (items.foldl streamItemStep (current, [], [], [])).2.1
      → ∃ earlier item later,
          items = earlier ++ item :: later
          ∧ let boundary := (current.preparedStreamItems earlier).integrateStreamItem item
            (∃ dependencies producer, NodeAt work child .group dependencies producer)
            ∧ ∃ node,
                boundary.groupNode? child.key = some node
                ∧ node.group.node = child
                ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
                ∧ (∀ publication ∈
                    published.take
                      ((w.events.take index).flatMap normalizedObjectValues).length,
                    publication.1 ∉ node.tasks)
                ∧ ∀ occurrence ∈ node.tasks,
                    ¬Published w.matching (w.events.take index) occurrence := by
  intro current noticed
  obtain ⟨earlier, item, later, splitItems, located, node, found, same, contents, excluded⟩ :=
    generated.streamItems_leadingNoticeContents covered valid noticed
  have prior := valid.prefix (List.prefix_append before (.streamItems stream items :: after))
  obtain ⟨matching, _, _⟩ := valid.atPrefix (show
    (before ++ [GraphEvent.streamItems stream items]).IsPrefix
      (before ++ GraphEvent.streamItems stream items :: after) from ⟨after, by simp⟩)
  obtain ⟨sound, registered⟩ := State.replay_noticeTaskProvenance
    (createWorkQueue_groupMembershipSound _) (createWorkQueue_fromSpec_registeredTasksMatch work)
    before (fun _ member => prior.eachMatches member)
  have included : earlier.Subset items := by
    rw [splitItems]
    exact List.subset_append_left _ _
  obtain ⟨preparedSound, preparedRegistered⟩ :=
    State.preparedStreamItems_noticeTaskProvenance sound registered matching earlier included
  obtain ⟨boundarySound, boundaryRegistered⟩ :=
    State.integrateStreamItem_noticeTaskProvenance (item := item)
      preparedSound preparedRegistered matching
      (by simp [splitItems])
  have excludedAtAtom : ∀ publication ∈ published.take
      ((w.events.take index).flatMap normalizedObjectValues).length,
      publication.1 ∉ node.tasks := by simpa only [count] using excluded
  refine ⟨earlier, item, later, splitItems, located, node, found, same, contents,
    excludedAtAtom, ?_⟩
  apply ConformancePlan.retainedGroupMembers_unpublished ledger objects streams
    boundarySound boundaryRegistered (List.mem_of_find?_eq_some found)
  exact excludedAtAtom

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
