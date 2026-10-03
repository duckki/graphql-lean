import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupCarrierUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemCarrierUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeSeparation

/-! Every group-notice list in actual matching source replay has unique refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Complete handlers compose local unique frontiers and recursive drains
-----------------------------------------------------------------------------------------

/-- A matching task-success handler carries only duplicate-free group-notice lists.
Witness: exact value installation and integration preserve child metadata; the actual
single-pass owner fold and its activated recursive drain each certify their carriers.
-/
theorem State.taskSuccess_groupNoticesUnique {queue : State} {parents}
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    (occurrence : Occurrence) (result : TaskResult)
    (canonical
      : ∀ group ∈ result.work.groups, group.parent = (parents group.node.ref).head?)
    : ∀ event ∈ (queue.taskSuccess occurrence result).2,
        (rawGroupNoticeRefs event).Nodup := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some incoming =>
      rw [queue.taskSuccess_eq occurrence result incoming found]
      split
      · simp
      · let stored := queue.putTaskNode { incoming with value := some result.value }
        let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
        let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
        have storedLinks : stored.ChildLinksCanonical parents := links
        have storedChildren : stored.ChildGroupsUnique := children
        have preparedLinks := storedLinks.maybeIntegrateWork result.work canonical (some occurrence)
        have preparedChildren := storedChildren.maybeIntegrateWork result.work (some occurrence)
        obtain ⟨foldedLinks, foldedChildren, notices⟩ :=
          prepared.successGroupFold_groupNoticesUnique preparedLinks preparedChildren
            incoming.task.groups
        intro event emitted
        rcases List.mem_append.mp emitted with owner | drain
        · exact notices event owner
        · exact State.drainReadyGroups_go_groupNoticesUnique
            (foldedLinks.startNewWork folded.2.2) (foldedChildren.startNewWork folded.2.2)
            _ event drain

/-- Matching item handling carries a unique leading group list and unique drain lists.
Witness: the item fold separates its fresh registered frontiers; each later success
carrier has the unique frontier certified by the structural drain theorem.
-/
theorem State.streamItems_groupNoticesUnique {queue : State} {work parents stream items}
    (refs : queue.GroupRefsUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (links : queue.ChildLinksCanonical parents)
    (children : queue.ChildGroupsUnique)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    : ∀ event ∈ (queue.streamItems stream items).2, (rawGroupNoticeRefs event).Nodup := by
  have leading := queue.streamItemFold_groupNoticesUnique refs live tasks links children
    canonical matched
  have preparedLinks : (queue.preparedStreamItems items).ChildLinksCanonical parents :=
    State.preparedStreamItems_preserves (fun current => current.ChildLinksCanonical parents)
      links items (fun current item member prior => by
        have fields := fun group included =>
          matched.streamItem_childGroups_parentCanonical canonical member
            (group := group) included
        exact ((prior.maybeIntegrateWork item.work fields).pruneEmptyGroups _).startNewWork _)
  have preparedChildren : (queue.preparedStreamItems items).ChildGroupsUnique :=
    State.preparedStreamItems_preserves (fun current => current.ChildGroupsUnique)
      children items (fun current item _ prior =>
        ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
  rw [queue.streamItems_eq stream items]
  split
  · simp
  · intro event emitted
    rcases List.mem_cons.mp emitted with rfl | drain
    · exact leading
    · exact State.drainReadyGroups_go_groupNoticesUnique preparedLinks preparedChildren _
        event drain

/-- Every matching source handler has duplicate-free group-notice lists.
Witness: the two producing handlers use real pruning and fold certificates; task failures
and stream controls have no group notices. Canonical parents are structural metadata only.
-/
theorem State.handleGraphEvent_groupNoticesUnique {queue : State} {work parents}
    (refs : queue.GroupRefsUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (links : queue.ChildLinksCanonical parents)
    (children : queue.ChildGroupsUnique)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matched : event.MatchesWork work)
    : ∀ output ∈ (queue.handleGraphEvent event).2, (rawGroupNoticeRefs output).Nodup := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_groupNoticesUnique links children occurrence result
        (fun _ member => matched.taskChildGroups_parentCanonical canonical member)
  | streamItems stream items =>
      exact queue.streamItems_groupNoticesUnique refs live tasks links children canonical matched
  | taskFailure occurrence errors =>
      intro output emitted
      have empty : rawGroupNoticeRefs output = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro ref noticed
        have impossible
            : ref ∈ (queue.taskFailure occurrence errors).2.flatMap rawGroupNoticeRefs :=
          List.mem_flatMap.mpr ⟨output, emitted, noticed⟩
        rw [queue.taskFailure_groupNoticeRefs] at impossible
        cases impossible
      rw [empty]
      exact List.nodup_nil
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [rawGroupNoticeRefs]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [rawGroupNoticeRefs]

-----------------------------------------------------------------------------------------
-- Matching source replay preserves every required implementation fact independently
-----------------------------------------------------------------------------------------

/-- Every notice list in matching raw replay is unique from a coherent structural entry.
Witness: per-handler uniqueness and the independently proved metadata and registration
preservation theorems. No already-admitted output history appears in the induction.
-/
theorem State.rawEventReplay_groupNoticesUnique {queue : State} {work parents}
    (refs : queue.GroupRefsUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (links : queue.ChildLinksCanonical parents)
    (children : queue.ChildGroupsUnique)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : ∀ output ∈ (queue.rawEventReplay events).2, (rawGroupNoticeRefs output).Nodup := by
  induction events generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      have matched := matching event List.mem_cons_self
      have registration := queue.handleGraphEvent_registration live tasks event matched
      intro output emitted
      rw [State.rawEventReplay_cons] at emitted
      rcases List.mem_append.mp emitted with first | later
      · exact queue.handleGraphEvent_groupNoticesUnique refs live tasks links children
          canonical event matched output first
      · exact ih (refs.handleGraphEvent event) registration.1 registration.2.1
          (links.handleGraphEvent event matched canonical) (children.handleGraphEvent event)
          (fun _ member => matching _ (List.mem_cons_of_mem _ member)) output later

/-- Every group-notice list produced by generated matching replay is duplicate-free.
Witness: generated canonical parent metadata and empty-queue initialization supply all
entry invariants of raw replay. This includes multi-item carriers and taskless promotion.
-/
theorem ExecutedWork.rawEventReplay_groupNoticesUnique {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ∀ output ∈ ((State.initialize (Work.fromExecution work)).rawEventReplay events).2,
        (rawGroupNoticeRefs output).Nodup := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := createWorkQueue_registration work
  exact State.rawEventReplay_groupNoticesUnique (createWorkQueue_groupRefsUnique _)
    registered.1 registered.2 (createWorkQueue_childLinksCanonical _ parents
      (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member))
    (createWorkQueue_childGroupsUnique _) canonical events matching

/-- Initial and all raw carried group refs are globally duplicate-free.
Witness: unique initialization and per-carrier lists combine with independently proved
cross-carrier separation and initial-ref exclusion. Repeated shared-owner registrations
and multi-item carriers need no extra uniqueness premise from the host source.
-/
theorem ExecutedWork.rawEventReplay_groupRefs_nodup {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ((State.initialize (Work.fromExecution work)).rootGroups
        ++ ((State.initialize (Work.fromExecution work)).rawEventReplay events).2.flatMap
            rawGroupNoticeRefs).Nodup := by
  obtain ⟨separated, initialFresh⟩ := generated.rawEventReplay_groupNoticeSeparation events matching
  have lists := generated.rawEventReplay_groupNoticesUnique events matching
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [createWorkQueue_rootGroups]
    exact generated.initialGroups_unique
  · apply List.pairwise_flatMap.mpr
    refine ⟨lists, ?_⟩
    apply separated.imp
    intro first second different ref member other included same
    subst other
    exact different ref member included
  · intro ref initial other noticed same
    exact initialFresh ref initial (same.symm ▸ noticed)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
