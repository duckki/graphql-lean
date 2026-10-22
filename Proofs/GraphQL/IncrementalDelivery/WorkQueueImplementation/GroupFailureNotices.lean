import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingFailureFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureOutput
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupActivationSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyPending
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OutputShape

/-! Failed group closures have strictly prior notices, including release-time drains. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Notice accounting composes without assuming output admission
-----------------------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
-- Startup notices retain announcement evidence across successful drains
-----------------------------------------------------------------------------------------

/-- Successful closure followed by activation justifies every newly active group.
Witness: closure removes a root; activation adds precisely its emitted child notices.
-/
theorem State.finishGroupSuccess_groupFailureNotices (queue : State) (node : GroupNode)
    (available : List (Occurrence × Nat) := [])
    : StartupFailureNoticeAccounting queue.rootGroups
        (
          (queue.finishGroupSuccess node).1.startNewWork
            (queue.finishGroupSuccess node).2.2 available
          |>.1,
          (queue.finishGroupSuccess node).2.1,
          ((queue.finishGroupSuccess node).1.startNewWork
            (queue.finishGroupSuccess node).2.2 available).2
        ) := by
  refine ⟨⟨?_, ReferencesAnnounced.of_references ?_⟩, ?_⟩
  · have roots := ((queue.finishGroupSuccess node).1.startNewWork_groupCore
      (queue.finishGroupSuccess node).2.2 available).2.2.subset
    rw [← queue.finishGroupSuccess_groupNotices node]
    intro ref member
    exact (List.mem_append.mp (roots member)).elim
      (fun old => List.mem_append_left _ (queue.finishGroupSuccess_rootsSubset node old))
      (fun added => List.mem_append_right _ added)
  · obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
    rw [output]
    split <;> simp [rawGroupFailureRefs, List.Subset]
  · intro failure member
    rw [← queue.finishGroupSuccess_groupNotices]
    exact List.mem_append_right _
      (State.startNewWork_failure_refs _ _ available failure member)

/-- An active failed group closes using an already known root ref.
Witness: the failure event introduces no notice, and removal only shrinks active roots.
-/
theorem State.finishGroupFailure_groupFailureNotices (queue : State) (node : GroupNode)
    (errors : Nat) (active : node.group.node.ref ∈ queue.rootGroups)
    : GroupFailureNoticeAccounting queue.rootGroups
        (
          (queue.finishGroupFailure node errors).1,
          [.groupFailure (queue.finishGroupFailure node errors).2.group
            (queue.finishGroupFailure node errors).2.errors]
        ) := by
  refine ⟨?_, ?_⟩
  · simpa only [State.finishGroupFailure, List.flatMap_singleton, rawGroupNoticeRefs,
      List.append_nil] using queue.removeGroup_rootsSubset node.group.node.ref
  · exact ⟨by simpa [State.finishGroupFailure, rawGroupFailureRefs, List.Subset] using active,
      trivial⟩

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
              (current.groupNode?_ref found ▸ (by simpa using active)))
          · exact prior
  cases found : queue.taskNode? occurrence with
  | none =>
      simp [State.taskFailure, found, GroupFailureNoticeAccounting, ReferencesAnnounced,
        List.Subset]
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact loop _ (_, []) ⟨by simp [State.putTaskNode, List.Subset], trivial⟩

/-- Recursive draining closes failed groups only after their notices are available.
Witness: each selected node is active; successful carriers add the roots used by later
drain iterations. Retained failures released and closed within one batch are included.
-/
theorem State.drainReadyGroups_groupFailureNotices (queue : State)
    (available : List (Occurrence × Nat) := [])
    : StartupFailureNoticeAccounting queue.rootGroups
        (queue.drainReadyGroups available) := by
  have loop (fuel : Nat) (current : State)
      : StartupFailureNoticeAccounting current.rootGroups
          (State.drainReadyGroups.go available fuel current) := by
    induction fuel generalizing current with
    | zero =>
        exact ⟨
          ⟨by simp [State.drainReadyGroups.go, List.Subset], trivial⟩,
          by simp [State.drainReadyGroups.go]
        ⟩
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact ⟨⟨by simp [List.Subset], trivial⟩, by simp⟩
        · exact (current.finishGroupSuccess_groupFailureNotices _ available).append (ih _)
  exact loop _ queue

-----------------------------------------------------------------------------------------
-- Complete handlers preserve the same boundary, including silent settlements
-----------------------------------------------------------------------------------------

/-- Successful task processing announces every root before its final failure drain.
Witness: contributor flushes accumulate the exact released notices without activating
new roots; activation follows those carriers and precedes recursive cached closure.
-/
theorem State.taskSuccess_groupFailureNotices (queue : State) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    : StartupFailureNoticeAccounting queue.rootGroups
        (queue.taskSuccess occurrence result available) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp [State.taskSuccess, found, StartupFailureNoticeAccounting, GroupFailureNoticeAccounting,
        ReferencesAnnounced,
        List.Subset]
  | some node =>
      let stored := queue.putTaskNode { node with value := some result.value }
      let integrated := stored.maybeIntegrateWork result.work (some occurrence)
      have loop (groups : List Execution.DeliveryNode)
          (acc : State × List WorkQueueEvent × NewWork)
          (roots : acc.1.rootGroups.Subset queue.rootGroups)
          (notices : acc.2.2.newGroups.map Execution.DeliveryNode.ref
            = acc.2.1.flatMap rawGroupNoticeRefs)
          (noFailures : acc.2.1.flatMap rawGroupFailureRefs = [])
          : (groups.foldl successGroupStep acc).1.rootGroups.Subset queue.rootGroups
            ∧ (groups.foldl successGroupStep acc).2.2.newGroups.map Execution.DeliveryNode.ref
              = (groups.foldl successGroupStep acc).2.1.flatMap rawGroupNoticeRefs
            ∧ (groups.foldl successGroupStep acc).2.1.flatMap rawGroupFailureRefs = [] := by
        induction groups generalizing acc with
        | nil => exact ⟨roots, notices, noFailures⟩
        | cons group rest ih =>
            obtain ⟨current, events, released⟩ := acc
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
                ·
                  rw [List.flatMap_append, noFailures, List.nil_append]
                  obtain ⟨values, _, _, output, _, _⟩ :=
                    State.finishGroupSuccess_publications _ _
                  rw [output]
                  split <;> simp [rawGroupFailureRefs]
                · exact noFailures
      have initial : integrated.1.rootGroups = queue.rootGroups :=
        State.maybeIntegrateWork_rootGroups _ _ _
      obtain ⟨roots, notices, noFailures⟩ := loop node.task.groups (integrated.1, [], {})
        (by rw [initial]; exact List.Subset.refl _) rfl rfl
      rw [queue.taskSuccess_eq occurrence result node found available]
      let folded := node.task.groups.foldl successGroupStep (integrated.1, [], {})
      have first : StartupFailureNoticeAccounting queue.rootGroups
          ((folded.1.startNewWork folded.2.2 available).1, folded.2.1,
            (folded.1.startNewWork folded.2.2 available).2) := by
        refine ⟨⟨?_, ReferencesAnnounced.of_references
          (by rw [noFailures]; simp [List.Subset])⟩, ?_⟩
        · have subset := (folded.1.startNewWork_groupCore folded.2.2 available).2.2.subset
          intro ref member
          rw [← notices]
          exact (List.mem_append.mp (subset member)).elim
            (fun old => List.mem_append_left _ (roots old))
            (fun fresh => List.mem_append_right _ fresh)
        · intro failure member
          rw [← notices]
          exact List.mem_append_right _
            (State.startNewWork_failure_refs _ _ available failure member)
      exact first.append (State.drainReadyGroups_groupFailureNotices _ available)

/-- Item processing emits its group notices before draining newly released failures.
Witness: each item adds only its accumulated group roots; the single stream carrier
announces that entire list before the ready-group drain emits any failed completion.
-/
theorem State.streamItems_groupFailureNotices (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    : StartupFailureNoticeAccounting queue.rootGroups
        (queue.streamItems stream items available) := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue × List GroupFailureEvent) (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    let (started, queued) :=
      pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 } available
    (started, acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams,
      acc.2.2.2.1 ++ [item.value], acc.2.2.2.2 ++ queued)
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (roots : acc.1.rootGroups.Subset
        (queue.rootGroups ++ acc.2.1.map Execution.DeliveryNode.ref))
      (failures : ∀ failure ∈ acc.2.2.2.2,
        failure.group.ref ∈ acc.2.1.map Execution.DeliveryNode.ref)
      : (more.foldl step acc).1.rootGroups.Subset
          (queue.rootGroups ++ (more.foldl step acc).2.1.map Execution.DeliveryNode.ref)
        ∧ ∀ failure ∈ (more.foldl step acc).2.2.2.2,
          failure.group.ref ∈ (more.foldl step acc).2.1.map Execution.DeliveryNode.ref := by
    induction more generalizing acc with
    | nil => exact ⟨roots, failures⟩
    | cons item rest ih =>
        apply ih
        · intro ref member
          dsimp only [step] at member ⊢
          have added := (State.startNewWork_groupCore _ _ available).2.2.subset member
          rw [State.pruneEmptyGroups_rootGroups, State.maybeIntegrateWork_rootGroups] at added
          simp only [List.map_append, List.mem_append]
          rcases List.mem_append.mp added with old | fresh
          · exact (List.mem_append.mp (roots old)).elim Or.inl (fun prior => Or.inr (.inl prior))
          · exact .inr (.inr fresh)
        · intro failure member
          rw [List.map_append]
          rcases List.mem_append.mp member with old | fresh
          · exact List.mem_append_left _ (failures failure old)
          · exact List.mem_append_right _
              (State.startNewWork_failure_refs _ _ available failure fresh)
  unfold State.streamItems
  split
  · exact ⟨⟨by simp [List.Subset], trivial⟩, by simp⟩
  · let folded := items.foldl step (queue, [], [], [], [])
    obtain ⟨roots, failures⟩ := loop items (queue, [], [], [], [])
      (by simp [List.Subset]) (by simp)
    have first : StartupFailureNoticeAccounting queue.rootGroups
        (folded.1, [.streamValues stream folded.2.2.2.1 folded.2.1 folded.2.2.1],
          folded.2.2.2.2) := by
      refine ⟨⟨?_, ⟨by simp [rawGroupFailureRefs, List.Subset], trivial⟩⟩, ?_⟩
      · simpa only [List.flatMap_singleton, rawGroupNoticeRefs] using roots
      · intro failure member
        simpa only [List.flatMap_singleton, rawGroupNoticeRefs]
          using List.mem_append_right queue.rootGroups (failures failure member)
    exact first.append (folded.1.drainReadyGroups_groupFailureNotices available)

/-- Every graph-event handler preserves prior group notices for failed closures.
Witness: task/item handlers include their actual drains; stream closure changes no
group roots and emits no group failure. No admitted-output premise is required.
-/
private theorem State.handleGraphEvent_rootFailureNotices (queue : State)
    (event : GraphEvent) (available : List (Occurrence × Nat) := [])
    (ordinary : ∀ failure, event ≠ .groupFailure failure)
    : StartupFailureNoticeAccounting queue.rootGroups
        (queue.handleGraphEvent event available) := by
  have roots := queue.cacheTaskFailures_rootGroups available
  cases event with
  | taskSuccess occurrence result =>
      simpa only [State.handleGraphEvent, roots]
        using (queue.cacheTaskFailures available).taskSuccess_groupFailureNotices
          occurrence result available
  | taskFailure occurrence errors =>
      have known := (queue.cacheTaskFailures available).taskFailure_groupFailureNotices
        occurrence errors
      cases reduced
            : (queue.cacheTaskFailures available).taskFailure occurrence errors with
      | mk next output =>
          exact ⟨
            by simpa only [State.handleGraphEvent, reduced, roots] using known,
            by simp [State.handleGraphEvent, reduced]
          ⟩
  | streamItems stream items =>
      simpa only [State.handleGraphEvent, roots]
        using (queue.cacheTaskFailures available).streamItems_groupFailureNotices stream
          items available
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact ⟨⟨by simp [roots, rawGroupNoticeRefs, List.Subset],
        by simp [ReferencesAnnounced, rawGroupFailureRefs, List.Subset]⟩, by simp⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact ⟨⟨by simp [roots, rawGroupNoticeRefs, List.Subset],
        by simp [ReferencesAnnounced, rawGroupFailureRefs, List.Subset]⟩, by simp⟩

  -----------------------------------------------------------------------------------------
  -- Actual batching and publisher normalization preserve prior group notices
  -----------------------------------------------------------------------------------------

  | groupFailure failure => exact (ordinary failure rfl).elim

/-- Forwarding an internal control leaves live group roots unchanged. -/
theorem State.groupFailure_rootGroups (queue : State) (failure : GroupFailureEvent)
    : (queue.groupFailure failure).1.rootGroups = queue.rootGroups := by
  unfold State.groupFailure
  split
  · rfl
  · split <;> rfl

/-- Every forwarded failure head retains the announcement represented by its FIFO entry. -/
theorem State.groupFailure_noticeAccounting (queue : State) (failure : GroupFailureEvent)
    : GroupFailureNoticeAccounting queue.groupNoticeSupport
        (queue.groupFailure failure) := by
  constructor
  · intro ref member
    rw [State.groupFailure_rootGroups] at member
    exact List.mem_append_left _ (List.mem_append_left _ member)
  · apply ReferencesAnnounced.of_references
    intro ref member
    obtain ⟨output, emitted, referenced⟩ := List.mem_flatMap.mp member
    cases output <;> simp only [rawGroupFailureRefs, List.not_mem_nil] at referenced
    obtain rfl := List.mem_singleton.mp referenced
    obtain ⟨rest, head⟩ := queue.groupFailure_origin failure emitted
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_, by rw [head]; exact List.mem_cons_self, rfl⟩

/-- Every handler accounts for failure references using live or pending announcements. -/
theorem State.handleGraphEvent_groupFailureNotices (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : StartupFailureNoticeAccounting queue.groupNoticeSupport
        (queue.handleGraphEvent event available) := by
  by_cases control : ∃ failure, event = .groupFailure failure
  · obtain ⟨failure, rfl⟩ := control
    refine ⟨?_, by simp [State.handleGraphEvent]⟩
    have prior := (queue.cacheTaskFailures available).groupFailure_noticeAccounting failure
    simpa only [State.handleGraphEvent, State.groupNoticeSupport, State.pendingGroupFailureRefs,
      State.cacheTaskFailures_rootGroups, State.cacheTaskFailures_groupFailureEvents] using prior
  · exact (queue.handleGraphEvent_rootFailureNotices event available
      (by intro failure same; exact control ⟨failure, same⟩)).mono
        (List.subset_append_left _ _)

/-- Root activation uses only earlier live roots or this handler's fresh notices.
Pending controls contribute no new live roots. -/
theorem State.handleGraphEvent_groupRoots_subset (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.rootGroups.Subset
        (queue.rootGroups
          ++ (queue.handleGraphEvent event available).2.1.flatMap
              rawGroupNoticeRefs) := by
  by_cases control : ∃ failure, event = .groupFailure failure
  · obtain ⟨failure, rfl⟩ := control
    intro ref member
    change ref ∈ ((queue.cacheTaskFailures available).groupFailure failure).1.rootGroups at member
    rw [State.groupFailure_rootGroups, State.cacheTaskFailures_rootGroups] at member
    exact List.mem_append_left _ member
  · exact (queue.handleGraphEvent_rootFailureNotices event available
      (by intro failure same; exact control ⟨failure, same⟩)).1.1

/-- Dispatch preserves prior announcements for the remaining and freshly queued notices. -/
theorem State.dispatchGraphEvent_groupFailureNotices (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : FifoFailureNoticeAccounting queue.groupNoticeSupport
        (queue.dispatchGraphEvent event available) := by
  have localFacts := queue.handleGraphEvent_groupFailureNotices event available
  refine ⟨⟨localFacts.1.1, localFacts.1.2⟩, ?_⟩
  intro ref member
  change ref ∈ ((queue.handleGraphEvent event available).1.groupFailureEvents
    ++ (queue.handleGraphEvent event available).2.2).map (fun failure => failure.group.ref) at member
  obtain ⟨failure, listed, rfl⟩ := List.mem_map.mp member
  rcases List.mem_append.mp listed with earlier | fresh
  · apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨failure,
      queue.handleGraphEvent_groupFailureEvents_subset event available earlier, rfl⟩
  · exact localFacts.2 failure fresh

/-- FIFO replay retains each waiting notice's earlier announcement across dispatch. -/
theorem State.rawEventReplay_groupFailureNotices (queue : State)
    (events : List GraphEvent) (available : List (Occurrence × Nat) := [])
    : FifoFailureNoticeAccounting queue.groupNoticeSupport
        (queue.rawEventReplay events available) := by
  induction events generalizing queue with
  | nil => exact .refl queue
  | cons event rest ih =>
      rw [State.rawEventReplay_cons queue event rest available]
      exact (queue.dispatchGraphEvent_groupFailureNotices event available).append (ih _)

/-- Batch boundaries preserve announcement evidence for live and pending groups. -/
theorem State.handleGraphEvents_fifoGroupFailureNotices (queue : State)
    (events : List GraphEvent)
    : FifoFailureNoticeAccounting queue.groupNoticeSupport
        (queue.handleGraphEvents events) := by
  have raw := queue.rawEventReplay_groupFailureNotices events (GraphEvent.availableFailures events)
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact .refl queue
  · dsimp only
    split
    · refine ⟨⟨?_, raw.1.2.append ?_⟩, ?_⟩
      · simpa only [List.flatMap_append, List.flatMap_singleton, rawGroupNoticeRefs,
          List.append_nil] using raw.1.1
      · exact ⟨by simp [rawGroupFailureRefs, List.Subset], trivial⟩
      · simpa only [State.pendingGroupFailureRefs, List.flatMap_append,
          List.flatMap_singleton, rawGroupNoticeRefs, List.append_nil] using raw.2
    · exact raw

/-- Emitted failed closures use already announced live roots or queued notices. -/
theorem State.handleGraphEvents_groupFailureNotices (queue : State)
    (events : List GraphEvent)
    : GroupFailureNoticeAccounting queue.groupNoticeSupport
        (queue.handleGraphEvents events) :=
  (queue.handleGraphEvents_fifoGroupFailureNotices events).1

/-- Group refs announced by a normalized output carrier, before wire ID allocation. -/
def groupNoticeRefs : Execution.WorkQueueEvent → NodeRefs
  | .groupSuccess _ groups _ | .streamValues _ _ groups _ =>
      groups.map Execution.DeliveryNode.ref
  | _ => []

/-- Group refs referenced by normalized failed closures. -/
def groupFailureRefs : Execution.WorkQueueEvent → NodeRefs
  | .groupFailure group _ => [group.ref]
  | _ => []

/-- Normalizing one raw event retains exactly its group notices.
Witness: owner remapping changes only value events; carriers retain their notice lists.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_groupNotices
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap groupNoticeRefs
      = rawGroupNoticeRefs event := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, rawGroupNoticeRefs,
    groupNoticeRefs, List.flatMap_map]

/-- Publisher processing retains exactly the raw failed-group references.
Witness: failed closures are unchanged and no other constructor produces one.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_groupFailureRefs
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap groupFailureRefs
      = rawGroupFailureRefs event := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, rawGroupFailureRefs,
    groupFailureRefs, List.flatMap_map]

/-- Stateful normalization retains the ordered group-notice projection of a batch.
Witness: each raw head preserves notices and its normalized output precedes the tail.
-/
theorem IncrementalPublisher.normalizeBatch_groupNotices
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.flatMap groupNoticeRefs
      = events.flatMap rawGroupNoticeRefs := by
  induction events generalizing publisher with
  | nil => rfl
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      simp only [List.flatMap_append, IncrementalPublisher.handleWorkQueueEvent_groupNotices,
        ih, List.flatMap_cons]

/-- Publisher normalization preserves strict notice-before-failure ordering.
Witness: each normalized head uses its old refs and passes its exact notices to the tail.
-/
theorem ReferencesAnnounced.normalizeGroupFailures {initial events}
    (announced
      : ReferencesAnnounced rawGroupNoticeRefs rawGroupFailureRefs initial events)
    (publisher : IncrementalPublisher)
    : ReferencesAnnounced groupNoticeRefs groupFailureRefs initial
        (publisher.normalizeBatch events).2 := by
  induction events generalizing initial publisher with
  | nil => trivial
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      apply ReferencesAnnounced.append
      · apply ReferencesAnnounced.of_references
        rw [IncrementalPublisher.handleWorkQueueEvent_groupFailureRefs]
        exact announced.1
      · rw [IncrementalPublisher.handleWorkQueueEvent_groupNotices]
        exact ih announced.2 _

/-- Actual normalized failures use initially announced or strictly earlier group notices.
Witness: joint replay of active-root support and each batch's notice-before-failure law.
This holds for arbitrary work and inputs; notice freshness and openness are not asserted.
-/
theorem createWorkQueue_runNormalized_groupFailureNotices (work : Work)
    (batches : List (List GraphEvent))
    : ReferencesAnnounced groupNoticeRefs groupFailureRefs
        ((State.initialize work).initialGroups.map Execution.DeliveryNode.ref)
        ((State.initialize work).runNormalized batches).2.flatten := by
  let initial := (State.initialize work).initialGroups.map Execution.DeliveryNode.ref
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (roots : acc.1.groupNoticeSupport.Subset (initial ++ acc.2.2.flatten.flatMap groupNoticeRefs))
      (announced : ReferencesAnnounced groupNoticeRefs groupFailureRefs initial
        acc.2.2.flatten)
      : ReferencesAnnounced groupNoticeRefs groupFailureRefs initial
          (more.foldl normalizedStep acc).2.2.flatten := by
    induction more generalizing acc with
    | nil => exact announced
    | cons batch rest ih =>
        have localFacts := acc.1.handleGraphEvents_fifoGroupFailureNotices batch
        apply ih
        · rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupNotices]
          intro ref member
          rcases List.mem_append.mp (localFacts.known member) with old | added
          · exact (List.mem_append.mp (roots old)).elim
              (fun root => List.mem_append_left _ root)
              (fun prior => List.mem_append_right _ (List.mem_append_left _ prior))
          · exact List.mem_append_right _ (List.mem_append_right _ added)
        · rw [normalizedStep_flatten]
          exact announced.append ((localFacts.1.2.normalizeGroupFailures acc.2.1).mono roots)
  let queue := State.initialize work
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  exact loop batches (queue, publisher, [])
    (by
      rw [State.groupNoticeSupport, State.pendingGroupFailureRefs,
        State.initialize_groupFailureEvents, List.map_nil, List.append_nil,
        createWorkQueue_rootGroups]
      simp [initial, List.Subset])
    trivial

-----------------------------------------------------------------------------------------
-- Atomic output positions retain the carrier before any failed closure
-----------------------------------------------------------------------------------------

/-- Splitting a nonempty stream value batch keeps all group notices on its last item.
Witness: the singleton item carries notices; every preceding item carries none.
-/
theorem streamPublicationAtoms_groupNotices (stream groups streams values)
    (nonempty : values ≠ [])
    : (streamPublicationAtoms stream groups streams values).flatMap groupNoticeRefs
      = groups.map Execution.DeliveryNode.ref := by
  induction values using streamPublicationAtoms.induct with
  | case1 => contradiction
  | case2 => simp [streamPublicationAtoms, groupNoticeRefs]
  | case3 value next rest ih =>
      simpa [streamPublicationAtoms, groupNoticeRefs] using ih (by simp)

/-- Atomic expansion preserves group notices when its value payload is nonempty.
Witness: stream notices stay on the final item, while group/control events are immediate.
-/
theorem publicationAtoms_groupNotices (event : Execution.WorkQueueEvent)
    (nonempty : NonemptyValues event)
    : (publicationAtoms event).flatMap groupNoticeRefs = groupNoticeRefs event := by
  cases event with
  | streamValues stream values groups streams =>
      exact streamPublicationAtoms_groupNotices _ _ _ _ nonempty
  | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
    | workQueueTermination => simp [publicationAtoms, groupNoticeRefs, List.flatMap_map]

/-- Atomic expansion leaves failed-group references unchanged.
Witness: value atoms produce no failed closure and each control event stays a singleton.
-/
theorem publicationAtoms_groupFailureRefs (event : Execution.WorkQueueEvent)
    : (publicationAtoms event).flatMap groupFailureRefs = groupFailureRefs event := by
  cases event with
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => rfl
      | case2 => rfl
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, groupFailureRefs] using ih
  | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
    | workQueueTermination => simp [publicationAtoms, groupFailureRefs, List.flatMap_map]

/-- Expanding actual value batches keeps each failed closure after its earlier notices.
Witness: exact notice and failure projections compose through the atomic list traversal.
-/
theorem ReferencesAnnounced.groupFailureAtoms {initial events}
    (announced : ReferencesAnnounced groupNoticeRefs groupFailureRefs initial events)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    : ReferencesAnnounced groupNoticeRefs groupFailureRefs initial
        (events.flatMap publicationAtoms) := by
  induction events generalizing initial with
  | nil => trivial
  | cons event rest ih =>
      rw [List.flatMap_cons]
      apply ReferencesAnnounced.append
      · apply ReferencesAnnounced.of_references
        rw [publicationAtoms_groupFailureRefs]
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
      group.ref
      ∈ announcedRefs
          ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
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
    cases carrier <;> simp_all [groupNoticeRefs, eventPending, List.map_append]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
