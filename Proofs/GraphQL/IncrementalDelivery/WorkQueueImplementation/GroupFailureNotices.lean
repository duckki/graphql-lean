import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReferences
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyPending
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OutputShape

/-! Failed group closures have strictly prior notices, including release-time drains. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Notice accounting composes without assuming output admission
-----------------------------------------------------------------------------------------

/-- Group keys announced by a raw carrier; stream notices are deliberately excluded. -/
def rawGroupNoticeKeys : WorkQueueEvent → Keys
  | .groupSuccess _ groups _ | .streamValues _ _ groups _ =>
      groups.map Execution.DeliveryNode.key
  | _ => []

/-- A failed group closure references its own key, not any newly released child. -/
def rawGroupFailureKeys : WorkQueueEvent → Keys
  | .groupFailure group _ => [group.key]
  | _ => []

/-- Output justifies the result's active groups and every failed closure's prior notice.
The initial keys describe already announced groups; openness and freshness are separate.
-/
def GroupFailureNoticeAccounting (initial : Keys) (result : State × List WorkQueueEvent)
    : Prop :=
  result.1.rootGroups.Subset (initial ++ result.2.flatMap rawGroupNoticeKeys)
  ∧ ReferencesAnnounced rawGroupNoticeKeys rawGroupFailureKeys initial result.2

/-- Enlarging the initial notice set preserves both accounting clauses.
Witness: subset transport for roots and monotonicity of strict-prefix references.
-/
theorem GroupFailureNoticeAccounting.mono {initial more result}
    (accounted : GroupFailureNoticeAccounting initial result)
    (included : initial.Subset more)
    : GroupFailureNoticeAccounting more result := by
  refine ⟨?_, accounted.2.mono included⟩
  intro key member
  exact (List.mem_append.mp (accounted.1 member)).elim
    (fun old => List.mem_append_left _ (included old))
    (fun added => List.mem_append_right _ added)

/-- Sequential output segments preserve the notice-before-failure boundary.
Witness: the first segment supplies all roots used by the next segment, and actual
notice lists concatenate in output order. No lifecycle premise is used.
-/
theorem GroupFailureNoticeAccounting.append {initial first second}
    (before : GroupFailureNoticeAccounting initial first)
    (after : GroupFailureNoticeAccounting first.1.rootGroups second)
    : GroupFailureNoticeAccounting initial (second.1, first.2 ++ second.2) := by
  have later := after.mono before.1
  refine ⟨?_, before.2.append later.2⟩
  simpa only [List.flatMap_append, List.append_assoc] using later.1

-----------------------------------------------------------------------------------------
-- Each ready-group drain announces retained failures before closing them
-----------------------------------------------------------------------------------------

/-- A successful flush announces exactly the group roots returned for activation.
Witness: its optional values carry no notices; its final success carries the release list.
-/
theorem State.finishGroupSuccess_groupNotices (queue : State) (node : GroupNode)
    : (queue.finishGroupSuccess node).2.2.newGroups.map Execution.DeliveryNode.key
      = (queue.finishGroupSuccess node).2.1.flatMap rawGroupNoticeKeys := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output, List.flatMap_append]
  split <;> simp [rawGroupNoticeKeys]

/-- The owner fold's pending frontier contains exactly its emitted group-notice keys.
Witness: each successful step appends the same pruned frontier to output and new work;
missing/counter-only steps change neither list. No freshness premise is needed.
-/
theorem successGroupFold_groupNotices (queue : State)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl successGroupStep (queue, [], {})).2.2.newGroups.map
        Execution.DeliveryNode.key
      = (groups.foldl successGroupStep (queue, [], {})).2.1.flatMap
          rawGroupNoticeKeys := by
  have loop (more : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (same : acc.2.2.newGroups.map Execution.DeliveryNode.key
        = acc.2.1.flatMap rawGroupNoticeKeys)
      : (more.foldl successGroupStep acc).2.2.newGroups.map Execution.DeliveryNode.key
        = (more.foldl successGroupStep acc).2.1.flatMap rawGroupNoticeKeys := by
    induction more generalizing acc with
    | nil => exact same
    | cons group rest ih =>
        apply ih
        dsimp only [successGroupStep]
        split
        · exact same
        · split
          · simp only [List.map_append, List.flatMap_append, same,
              State.finishGroupSuccess_groupNotices]
          · exact same
  exact loop groups (queue, [], {}) rfl

/-- Successful closure followed by activation justifies every newly active group.
Witness: closure removes a root; activation adds precisely its emitted child notices.
-/
theorem State.finishGroupSuccess_groupFailureNotices (queue : State) (node : GroupNode)
    : GroupFailureNoticeAccounting queue.rootGroups
        (
          (queue.finishGroupSuccess node).1.startNewWork
            (queue.finishGroupSuccess node).2.2,
          (queue.finishGroupSuccess node).2.1
        ) := by
  refine ⟨?_, ReferencesAnnounced.of_references ?_⟩
  · rw [((queue.finishGroupSuccess node).1.startNewWork_groupCore _).2.2,
      queue.finishGroupSuccess_groupNotices]
    intro key member
    exact (List.mem_append.mp member).elim
      (fun old => List.mem_append_left _ (queue.finishGroupSuccess_rootsSubset node old))
      (fun added => List.mem_append_right _ added)
  · obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
    rw [output]
    split <;> simp [rawGroupFailureKeys, List.Subset]

/-- An active failed group closes using an already known root key.
Witness: the failure event introduces no notice, and removal only shrinks active roots.
-/
theorem State.finishGroupFailure_groupFailureNotices (queue : State) (node : GroupNode)
    (errors : Nat) (active : node.group.node.key ∈ queue.rootGroups)
    : GroupFailureNoticeAccounting queue.rootGroups
        (
          (queue.finishGroupFailure node errors).1,
          [(queue.finishGroupFailure node errors).2]
        ) := by
  refine ⟨?_, ?_⟩
  · simpa only [State.finishGroupFailure, List.flatMap_singleton, rawGroupNoticeKeys,
      List.append_nil] using queue.removeGroup_rootsSubset node.group.node.key
  · exact ⟨by simpa [State.finishGroupFailure, rawGroupFailureKeys, List.Subset] using active,
      trivial⟩

/-- Recursive draining closes failed groups only after their notices are available.
Witness: each selected node is active; successful carriers add the roots used by later
drain iterations. Retained failures released and closed within one batch are included.
-/
theorem State.drainReadyGroups_groupFailureNotices (queue : State)
    : GroupFailureNoticeAccounting queue.rootGroups queue.drainReadyGroups := by
  have loop (fuel : Nat) (current : State)
      : GroupFailureNoticeAccounting current.rootGroups
          (State.drainReadyGroups.go fuel current) := by
    induction fuel generalizing current with
    | zero => exact ⟨by simp [State.drainReadyGroups.go, List.Subset], trivial⟩
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact ⟨by simp [List.Subset], trivial⟩
        · rename_i node selected
          obtain ⟨key, active, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : current.groupNode? key with
          | none => simp [found] at choice
          | some candidate =>
              simp only [found] at choice
              change (if candidate.failure.isSome || candidate.pending == 0 then
                some candidate else none) = some node at choice
              split at choice
              · have same := Option.some.inj choice
                subst candidate
                have root := current.groupNode?_key found ▸ active
                cases cached : node.failure with
                | none =>
                    exact (current.finishGroupSuccess_groupFailureNotices node).append (ih _)
                | some errors =>
                    exact (current.finishGroupFailure_groupFailureNotices node errors root).append
                      (ih _)
              · contradiction
  exact loop _ queue

-----------------------------------------------------------------------------------------
-- Complete handlers preserve the same boundary, including silent settlements
-----------------------------------------------------------------------------------------

/-- Task failure closes only active owners and never activates a latent one.
Witness: each owner step either emits an active failure or stores a silent cache;
ignored settlements change memberships only. This needs no source or health premise.
-/
theorem State.taskFailure_groupFailureNotices (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : GroupFailureNoticeAccounting queue.rootGroups
        (queue.taskFailure occurrence errors) := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : GroupFailureNoticeAccounting queue.rootGroups acc)
      : GroupFailureNoticeAccounting queue.rootGroups
          (groups.foldl (failureGroupStep errors) acc) := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        obtain ⟨current, events⟩ := acc
        dsimp only [failureGroupStep]
        split
        · exact prior
        · rename_i node found
          split
          · rename_i active
            exact prior.append (current.finishGroupFailure_groupFailureNotices node errors
              (current.groupNode?_key found ▸ (by simpa using active)))
          · exact prior
  cases found : queue.taskNode? occurrence with
  | none =>
      simp [State.taskFailure, found, GroupFailureNoticeAccounting, ReferencesAnnounced,
        List.Subset]
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      split
      · exact ⟨by simp [State.removeTask, List.Subset], trivial⟩
      · exact loop _ (_, []) ⟨by simp [State.removeTask, List.Subset], trivial⟩

/-- Successful task processing announces every root before its final failure drain.
Witness: contributor flushes accumulate the exact released notices without activating
new roots; activation follows those carriers and precedes recursive cached closure.
-/
theorem State.taskSuccess_groupFailureNotices (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : GroupFailureNoticeAccounting queue.rootGroups
        (queue.taskSuccess occurrence result) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp [State.taskSuccess, found, GroupFailureNoticeAccounting, ReferencesAnnounced,
        List.Subset]
  | some node =>
      let stored := queue.putTaskNode { node with value := some result.value }
      let integrated := stored.maybeIntegrateWork result.work (some occurrence)
      have loop (groups : List Execution.DeliveryNode)
          (acc : State × List WorkQueueEvent × NewWork)
          (roots : acc.1.rootGroups.Subset queue.rootGroups)
          (notices : acc.2.2.newGroups.map Execution.DeliveryNode.key
            = acc.2.1.flatMap rawGroupNoticeKeys)
          (noFailures : acc.2.1.flatMap rawGroupFailureKeys = [])
          : (groups.foldl successGroupStep acc).1.rootGroups.Subset queue.rootGroups
            ∧ (groups.foldl successGroupStep acc).2.2.newGroups.map Execution.DeliveryNode.key
              = (groups.foldl successGroupStep acc).2.1.flatMap rawGroupNoticeKeys
            ∧ (groups.foldl successGroupStep acc).2.1.flatMap rawGroupFailureKeys = [] := by
        induction groups generalizing acc with
        | nil => exact ⟨roots, notices, noFailures⟩
        | cons group rest ih =>
            apply ih
            · dsimp only [successGroupStep]
              split
              · exact roots
              · split
                · exact (State.finishGroupSuccess_rootsSubset _ _).trans roots
                · exact roots
            · dsimp only [successGroupStep]
              split
              · exact notices
              · split
                · simp only [List.map_append, List.flatMap_append, notices,
                    State.finishGroupSuccess_groupNotices]
                · exact notices
            · dsimp only [successGroupStep]
              split
              · exact noFailures
              · split
                · rename_i current descriptor selected ready
                  rw [List.flatMap_append, noFailures, List.nil_append]
                  obtain ⟨values, _, _, output, _, _⟩ :=
                    State.finishGroupSuccess_publications _ _
                  rw [output]
                  split <;> simp [rawGroupFailureKeys]
                · exact noFailures
      have initial : integrated.1.rootGroups = queue.rootGroups :=
        State.maybeIntegrateWork_rootGroups _ _ _
      obtain ⟨roots, notices, noFailures⟩ := loop node.task.groups (integrated.1, [], {})
        (by rw [initial]; exact List.Subset.refl _) rfl rfl
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact ⟨by simp [State.removeTask, List.Subset], trivial⟩
      · let folded := node.task.groups.foldl successGroupStep (integrated.1, [], {})
        have first : GroupFailureNoticeAccounting queue.rootGroups
            (folded.1.startNewWork folded.2.2, folded.2.1) := by
          refine ⟨?_, ReferencesAnnounced.of_references (by rw [noFailures]; simp [List.Subset])⟩
          rw [(folded.1.startNewWork_groupCore _).2.2, notices]
          intro key member
          exact (List.mem_append.mp member).elim
            (fun old => List.mem_append_left _ (roots old))
            (fun fresh => List.mem_append_right _ fresh)
        exact first.append (State.drainReadyGroups_groupFailureNotices _)

/-- Item processing emits its group notices before draining newly released failures.
Witness: each item adds only its accumulated group roots; the single stream carrier
announces that entire list before the ready-group drain emits any failed completion.
-/
theorem State.streamItems_groupFailureNotices (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : GroupFailureNoticeAccounting queue.rootGroups (queue.streamItems stream items) := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 },
      acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams,
      acc.2.2.2 ++ [item.value])
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (prior : acc.1.rootGroups
        = queue.rootGroups ++ acc.2.1.map Execution.DeliveryNode.key)
      : (more.foldl step acc).1.rootGroups
        = queue.rootGroups ++ (more.foldl step acc).2.1.map Execution.DeliveryNode.key := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih
        dsimp only [step]
        rw [(State.startNewWork_groupCore _ _).2.2,
          State.pruneEmptyGroups_rootGroups, State.maybeIntegrateWork_rootGroups, prior,
          List.map_append, List.append_assoc]
  unfold State.streamItems
  split
  · exact ⟨by simp [List.Subset], trivial⟩
  · let folded := items.foldl step (queue, [], [], [])
    have roots := loop items (queue, [], [], []) (by simp)
    have first : GroupFailureNoticeAccounting queue.rootGroups
        (folded.1, [.streamValues stream folded.2.2.2 folded.2.1 folded.2.2.1]) := by
      refine ⟨?_, ⟨by simp [rawGroupFailureKeys, List.Subset], trivial⟩⟩
      rw [roots, List.flatMap_singleton, rawGroupNoticeKeys]
      exact List.Subset.refl _
    exact first.append (folded.1.drainReadyGroups_groupFailureNotices)

/-- Every graph-event handler preserves prior group notices for failed closures.
Witness: task/item handlers include their actual drains; stream closure changes no
group roots and emits no group failure. No admitted-output premise is required.
-/
theorem State.handleGraphEvent_groupFailureNotices (queue : State) (event : GraphEvent)
    : GroupFailureNoticeAccounting queue.rootGroups (queue.handleGraphEvent event) := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_groupFailureNotices occurrence result
  | taskFailure occurrence errors =>
      exact queue.taskFailure_groupFailureNotices occurrence errors
  | streamItems stream items => exact queue.streamItems_groupFailureNotices stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact ⟨by simp [rawGroupNoticeKeys, List.Subset],
        by simp [ReferencesAnnounced, rawGroupFailureKeys, List.Subset]⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact ⟨by simp [rawGroupNoticeKeys, List.Subset],
        by simp [ReferencesAnnounced, rawGroupFailureKeys, List.Subset]⟩

-----------------------------------------------------------------------------------------
-- Actual batching and publisher normalization preserve prior group notices
-----------------------------------------------------------------------------------------

/-- Raw replay composes notice accounting across all received settlements.
Witness: each handler's final roots justify the next handler's initial keys.
-/
theorem State.rawEventReplay_groupFailureNotices (queue : State)
    (events : List GraphEvent)
    : GroupFailureNoticeAccounting queue.rootGroups (queue.rawEventReplay events) := by
  induction events generalizing queue with
  | nil => exact ⟨by simp [State.rawEventReplay, List.Subset], trivial⟩
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      exact (queue.handleGraphEvent_groupFailureNotices event).append (ih _)

/-- The batch wrapper preserves notice accounting, including its terminal marker.
Witness: ignored input emits nothing; termination changes neither group roots nor notices.
-/
theorem State.handleGraphEvents_groupFailureNotices (queue : State)
    (events : List GraphEvent)
    : GroupFailureNoticeAccounting queue.rootGroups (queue.handleGraphEvents events) := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact ⟨by simp [List.Subset], trivial⟩
  · have prior := queue.rawEventReplay_groupFailureNotices events
    dsimp only
    split
    · refine ⟨?_, prior.2.append ?_⟩
      · simpa only [List.flatMap_append, List.flatMap_singleton, rawGroupNoticeKeys,
          List.append_nil] using prior.1
      · exact ⟨by simp [rawGroupFailureKeys, List.Subset], trivial⟩
    · exact prior

/-- Group keys announced by a normalized output carrier, before wire ID allocation. -/
def groupNoticeKeys : Execution.WorkQueueEvent → Keys
  | .groupSuccess _ groups _ | .streamValues _ _ groups _ =>
      groups.map Execution.DeliveryNode.key
  | _ => []

/-- Group keys referenced by normalized failed closures. -/
def groupFailureKeys : Execution.WorkQueueEvent → Keys
  | .groupFailure group _ => [group.key]
  | _ => []

/-- Normalizing one raw event retains exactly its group notices.
Witness: owner remapping changes only value events; carriers retain their notice lists.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_groupNotices
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap groupNoticeKeys
      = rawGroupNoticeKeys event := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, rawGroupNoticeKeys,
    groupNoticeKeys, List.flatMap_map]

/-- Publisher processing retains exactly the raw failed-group references.
Witness: failed closures are unchanged and no other constructor produces one.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_groupFailureKeys
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap groupFailureKeys
      = rawGroupFailureKeys event := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, rawGroupFailureKeys,
    groupFailureKeys, List.flatMap_map]

/-- Stateful normalization retains the ordered group-notice projection of a batch.
Witness: each raw head preserves notices and its normalized output precedes the tail.
-/
theorem IncrementalPublisher.normalizeBatch_groupNotices
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.flatMap groupNoticeKeys
      = events.flatMap rawGroupNoticeKeys := by
  induction events generalizing publisher with
  | nil => rfl
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      simp only [List.flatMap_append, IncrementalPublisher.handleWorkQueueEvent_groupNotices,
        ih, List.flatMap_cons]

/-- Publisher normalization preserves strict notice-before-failure ordering.
Witness: each normalized head uses its old keys and passes its exact notices to the tail.
-/
theorem ReferencesAnnounced.normalizeGroupFailures {initial events}
    (announced
      : ReferencesAnnounced rawGroupNoticeKeys rawGroupFailureKeys initial events)
    (publisher : IncrementalPublisher)
    : ReferencesAnnounced groupNoticeKeys groupFailureKeys initial
        (publisher.normalizeBatch events).2 := by
  induction events generalizing initial publisher with
  | nil => trivial
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      apply ReferencesAnnounced.append
      · apply ReferencesAnnounced.of_references
        rw [IncrementalPublisher.handleWorkQueueEvent_groupFailureKeys]
        exact announced.1
      · rw [IncrementalPublisher.handleWorkQueueEvent_groupNotices]
        exact ih announced.2 _

/-- Actual normalized failures use initially announced or strictly earlier group notices.
Witness: joint replay of active-root support and each batch's notice-before-failure law.
This holds for arbitrary work and inputs; notice freshness and openness are not asserted.
-/
theorem createWorkQueue_runNormalized_groupFailureNotices (work : Work)
    (batches : List (List GraphEvent))
    : ReferencesAnnounced groupNoticeKeys groupFailureKeys
        ((State.initialize work).initialGroups.map Execution.DeliveryNode.key)
        ((State.initialize work).runNormalized batches).2.flatten := by
  let initial := (State.initialize work).initialGroups.map Execution.DeliveryNode.key
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (roots : acc.1.rootGroups.Subset (initial ++ acc.2.2.flatten.flatMap groupNoticeKeys))
      (announced : ReferencesAnnounced groupNoticeKeys groupFailureKeys initial
        acc.2.2.flatten)
      : ReferencesAnnounced groupNoticeKeys groupFailureKeys initial
          (more.foldl normalizedStep acc).2.2.flatten := by
    induction more generalizing acc with
    | nil => exact announced
    | cons batch rest ih =>
        have localFacts := acc.1.handleGraphEvents_groupFailureNotices batch
        apply ih
        · rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupNotices]
          intro key member
          rcases List.mem_append.mp (localFacts.1 member) with old | added
          · exact (List.mem_append.mp (roots old)).elim
              (fun root => List.mem_append_left _ root)
              (fun prior => List.mem_append_right _ (List.mem_append_left _ prior))
          · exact List.mem_append_right _ (List.mem_append_right _ added)
        · rw [normalizedStep_flatten]
          exact announced.append ((localFacts.2.normalizeGroupFailures acc.2.1).mono roots)
  let queue := State.initialize work
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  exact loop batches (queue, publisher, [])
    (by rw [createWorkQueue_rootGroups]; simp [initial, List.Subset]) trivial

-----------------------------------------------------------------------------------------
-- Atomic output positions retain the carrier before any failed closure
-----------------------------------------------------------------------------------------

/-- Splitting a nonempty stream value batch keeps all group notices on its last item.
Witness: the singleton item carries notices; every preceding item carries none.
-/
theorem streamPublicationAtoms_groupNotices (stream groups streams values)
    (nonempty : values ≠ [])
    : (streamPublicationAtoms stream groups streams values).flatMap groupNoticeKeys
      = groups.map Execution.DeliveryNode.key := by
  induction values using streamPublicationAtoms.induct with
  | case1 => contradiction
  | case2 => simp [streamPublicationAtoms, groupNoticeKeys]
  | case3 value next rest ih =>
      simpa [streamPublicationAtoms, groupNoticeKeys] using ih (by simp)

/-- Atomic expansion preserves group notices when its value payload is nonempty.
Witness: stream notices stay on the final item, while group/control events are immediate.
-/
theorem publicationAtoms_groupNotices (event : Execution.WorkQueueEvent)
    (nonempty : NonemptyValues event)
    : (publicationAtoms event).flatMap groupNoticeKeys = groupNoticeKeys event := by
  cases event with
  | streamValues stream values groups streams =>
      exact streamPublicationAtoms_groupNotices _ _ _ _ nonempty
  | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
    | workQueueTermination => simp [publicationAtoms, groupNoticeKeys, List.flatMap_map]

/-- Atomic expansion leaves failed-group references unchanged.
Witness: value atoms produce no failed closure and each control event stays a singleton.
-/
theorem publicationAtoms_groupFailureKeys (event : Execution.WorkQueueEvent)
    : (publicationAtoms event).flatMap groupFailureKeys = groupFailureKeys event := by
  cases event with
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => rfl
      | case2 => rfl
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, groupFailureKeys] using ih
  | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
    | workQueueTermination => simp [publicationAtoms, groupFailureKeys, List.flatMap_map]

/-- Expanding actual value batches keeps each failed closure after its earlier notices.
Witness: exact notice and failure projections compose through the atomic list traversal.
-/
theorem ReferencesAnnounced.groupFailureAtoms {initial events}
    (announced : ReferencesAnnounced groupNoticeKeys groupFailureKeys initial events)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    : ReferencesAnnounced groupNoticeKeys groupFailureKeys initial
        (events.flatMap publicationAtoms) := by
  induction events generalizing initial with
  | nil => trivial
  | cons event rest ih =>
      rw [List.flatMap_cons]
      apply ReferencesAnnounced.append
      · apply ReferencesAnnounced.of_references
        rw [publicationAtoms_groupFailureKeys]
        exact announced.1
      · rw [publicationAtoms_groupNotices event (nonempty event List.mem_cons_self)]
        exact ih announced.2 (fun event member => nonempty event (List.mem_cons_of_mem _ member))

/-- Every actual atomic failed-group closure has a strictly prior pending notice.
Witness: raw active-root accounting, exact publisher projections, and nonempty atomic
expansion. Source validity only excludes empty item carriers; no matching, failure-cut,
generated-work, accepted-start, or admitted-output premise is assumed.
This proves the announcement half of Open, not continued openness or full licensing.
-/
theorem createWorkQueue_runNormalized_groupFailureAnnouncedAt {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index group errors}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      group.key
      ∈ announcedKeys
          ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.key)
          (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take
            index) := by
  have announced := (createWorkQueue_runNormalized_groupFailureNotices (Work.fromExecution work)
    batches).groupFailureAtoms (createWorkQueue_runNormalized_nonemptyValues valid).2
  have known := announced.atEvent atEvent List.mem_cons_self
  rcases List.mem_append.mp known with initial | prior
  · apply List.mem_append_left
    rw [List.map_append]
    exact List.mem_append_left _ initial
  · apply List.mem_append_right
    obtain ⟨carrier, member, noticed⟩ := List.mem_flatMap.mp prior
    apply List.mem_flatMap.mpr ⟨carrier, member, ?_⟩
    cases carrier <;> simp_all [groupNoticeKeys, eventPending, List.map_append]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
