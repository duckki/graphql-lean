import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPresenceReplay

/-! Source-history completions for ancestors of actual carried notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A leading item notice cannot rely on a completion from its later recursive drain
-----------------------------------------------------------------------------------------

/-- An uncancelled, previously announced item-notice ancestor completed before this input.
Witness: prior raw replay tracks the ancestor as active, cancelled, or closed. Active
roots survive preparation, whose child's retired ancestry excludes any live contributor.
The surviving-root support certificate supplies that contributor instead of assuming one.
-/
theorem ExecutedWork.streamPrepared_noticeAncestor_completed
    {work before stream items child dependencies ref}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    : let initial := State.initialize (Work.fromExecution work)
      let queue := initial.replayGraphEvents before
      let prepared := items.foldl streamItemStep (queue, [], [], [])
      child ∈ prepared.2.1
      → ref ∉ queue.cancelledGroups
      → ref
        ∈ initial.rootGroups
          ++ (initial.rawEventReplay before).2.flatMap rawGroupNoticeRefs
      → ref ∈ (initial.rawEventReplay before).2.flatMap rawGroupClosureRefs := by
  intro initial queue prepared noticed uncancelled announced
  obtain ⟨parents, canonical, frame⟩ :=
    generated.streamItems_prepared_liveRootFrame matching matched
      (generated.replayGraphEvents_rootsPresent before matching)
  have ancestry := generated.streamItems_prepared_noticeAncestorsRetired matching matched
    child noticed
  have tracking := initial.rawEventReplay_groupNoticeTracking before
  apply tracking.completed_of_inactive_uncancelled announced
  · rw [State.rawEventReplay_state]
    intro retained
    have active : ref ∈ prepared.1.rootGroups := by
      rw [State.streamItemFold_rootGroups]
      exact List.mem_append_left _ retained
    obtain ⟨_, owner, producer, ownerKnown, same⟩ := frame.support.roots ref active
    obtain ⟨occurrence, owners, payload, task, contributes⟩ := ownerKnown.group_task
    have retired := ancestry child dependencies known rfl ref ancestor occurrence owners
      ⟨producer, payload, task⟩ (same ▸ contributes)
    exact retired.2 (frame.present ref active)
  · simpa only [State.rawEventReplay_state] using uncancelled

-----------------------------------------------------------------------------------------
-- Prior source notices and pending owner-fold notices use the same exact completion cut
-----------------------------------------------------------------------------------------

/-- A located raw group notice has a real structural contributor.
Witness: invert the descriptor map in either notice-carrying event and project its task.
-/
theorem
    _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.GroupNoticesLocated.contributor
    {work event ref} (located : WorkQueueEvent.GroupNoticesLocated work event)
    (noticed : ref ∈ rawGroupNoticeRefs event)
    : ∃ occurrence owners, TaskHasOwners work occurrence owners ∧ ref ∈ owners := by
  have fromGroups (groups : List Execution.DeliveryNode)
      (known : ∀ group ∈ groups,
        ∃ dependencies producer, NodeAt work group .group dependencies producer)
      (member : ref ∈ groups.map Execution.DeliveryNode.ref)
      : ∃ occurrence owners, TaskHasOwners work occurrence owners ∧ ref ∈ owners := by
    obtain ⟨group, included, same⟩ := List.mem_map.mp member
    obtain ⟨_, producer, node⟩ := known group included
    obtain ⟨occurrence, owners, payload, task, contributes⟩ := node.group_task
    exact ⟨occurrence, owners, ⟨producer, payload, task⟩, same ▸ contributes⟩
  cases event <;> simp only [rawGroupNoticeRefs] at noticed
  case groupSuccess group groups streams => exact fromGroups groups located noticed
  case streamValues stream values groups streams =>
    exact fromGroups groups located noticed
  all_goals cases noticed

/-- An uncancelled announced ancestor completes by its actual task owner-fold carrier.
Witness: earlier source notices are tracked into the live prepared roots or prior
completions. The exact owner-prefix theorem closes the former. Notices in this same
owner prefix are live pending releases and therefore cannot themselves be retired ancestors.
-/
theorem ExecutedWork.ownerNoticeAncestor_completed
    {work before occurrence result group groups streams child dependencies ref}
    {incoming : TaskNode} {index : Nat}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    : let initial := State.initialize (Work.fromExecution work)
      let queue := initial.replayGraphEvents before
      let prepared :=
        ((queue.putTaskNode
            { incoming with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      let output := (incoming.task.groups.foldl successGroupStep (prepared, [], {})).2.1
      output[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ref ∉ queue.cancelledGroups
      → ref
        ∈ initial.rootGroups
          ++ (((initial.rawEventReplay before).2 ++ output.take (index + 1)).flatMap
                rawGroupNoticeRefs)
      → ref
        ∈ (((initial.rawEventReplay before).2 ++ output.take (index + 1)).flatMap
            rawGroupClosureRefs) := by
  intro initial queue prepared output selected noticed uncancelled announced
  obtain ⟨parents, canonical, records, links, live, tasks, roots, _⟩ :=
    generated.replayGraphEvents_preparedRetirement before matching matched incoming
  obtain ⟨refs, _, support⟩ :=
    generated.taskSuccess_prepared_noticeMetadata matching matched incoming
  have storedPresent :
      (queue.putTaskNode { incoming with value := some result.value }).RootGroupsPresent :=
    generated.replayGraphEvents_rootsPresent before matching
  have present := storedPresent.maybeIntegrateWork result.work (some occurrence)
  have alternatives : ref ∈ initial.rootGroups ++ (initial.rawEventReplay before).2.flatMap
      rawGroupNoticeRefs ∨ ref ∈ (output.take (index + 1)).flatMap rawGroupNoticeRefs := by
    simpa only [List.flatMap_append, List.mem_append, or_assoc] using announced
  rw [List.flatMap_append]
  rcases alternatives with earlier | current
  · have tracked := initial.rawEventReplay_groupNoticeTracking before ref earlier
    rw [State.rawEventReplay_state] at tracked
    rcases tracked with active | cancelled | closed
    · have activePrepared : ref ∈ prepared.rootGroups := by
        change ref ∈ ((queue.putTaskNode
          { incoming with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.rootGroups
        rw [State.maybeIntegrateWork_rootGroups]
        exact active
      exact List.mem_append_right _
        (successGroupFold_noticeAncestor_completed generated refs records links canonical
          live tasks roots support present incoming.task.groups selected noticed known ancestor
          activePrepared)
    · exact False.elim (uncancelled cancelled)
    · exact List.mem_append_left _ closed
  · obtain ⟨event, included, mentioned⟩ := List.mem_flatMap.mp current
    have located := State.successGroupFold_groupNoticesLocated generated refs records support
      incoming.task.groups event (List.mem_of_mem_take included)
    obtain ⟨source, owners, task, contributes⟩ := located.contributor mentioned
    have absent := (successGroupFold_noticeAncestor_status generated refs records links canonical
      live tasks roots support present incoming.task.groups selected noticed known ancestor
      task contributes).1
    exact False.elim (absent (List.mem_flatMap.mpr ⟨event, included, mentioned⟩))

-----------------------------------------------------------------------------------------
-- A drain composes earlier source notices with its own exact carrier prefix
-----------------------------------------------------------------------------------------

/-- Earlier tracked notices and new drain notices complete at the same selected carrier.
Witness: prior tracking supplies an active root, old completion, or cancellation. The
local drain theorem handles active/new notices; cancellation persists and is excluded.
-/
theorem GroupNoticeTracking.drainNoticeAncestor_completed
    {initial before queue work parents}
    (tracked : GroupNoticeTracking initial (queue, before))
    (frame : LiveRootFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (fuel : Nat) {index group groups streams child dependencies ref}
    (selected
      : (State.drainReadyGroups.go fuel queue).2[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (uncancelled : ref ∉ (State.drainReadyGroups.go fuel queue).1.cancelledGroups)
    (announced
      : ref
        ∈ initial
          ++ ((before
                ++ (State.drainReadyGroups.go fuel queue).2.take (index + 1)).flatMap
                rawGroupNoticeRefs))
    : ref
      ∈ ((before ++ (State.drainReadyGroups.go fuel queue).2.take (index + 1)).flatMap
          rawGroupClosureRefs) := by
  have alternatives : ref ∈ initial ++ before.flatMap rawGroupNoticeRefs
      ∨ ref ∈ ((State.drainReadyGroups.go fuel queue).2.take
        (index + 1)).flatMap rawGroupNoticeRefs := by
    simpa only [List.flatMap_append, List.mem_append, or_assoc] using announced
  have localResult := frame.drainNoticeAncestor_completed generated canonical fuel selected
    noticed known ancestor uncancelled
  rw [List.flatMap_append]
  rcases alternatives with earlier | current
  · rcases tracked ref earlier with active | cancelled | closed
    · exact List.mem_append_right _ (localResult (List.mem_append_left _ active))
    · exact False.elim (uncancelled
        (State.drainReadyGroups_go_cancelledGroups_subset fuel queue cancelled))
    · exact List.mem_append_left _ closed
  · exact List.mem_append_right _ (localResult (List.mem_append_right _ current))

/-- Activation after the owner fold tracks all prior roots and its exact pending notices.
Witness: retained roots or actual closures cover old refs; every new notice is activated.
-/
theorem State.successGroupFold_groupNoticeTracking (queue : State)
    (owners : List Execution.DeliveryNode)
    : let folded := owners.foldl successGroupStep (queue, [], {})
      GroupNoticeTracking queue.rootGroups
        (folded.1.startNewWork folded.2.2, folded.2.1) := by
  intro folded ref member
  rw [(folded.1.startNewWork_groupCore _).2.2]
  rcases List.mem_append.mp member with old | noticed
  · rcases queue.successGroupFold_tracks_roots owners ref old with active | closed
    · exact .inl (List.mem_append_left _ active)
    · exact .inr (.inr closed)
  · exact .inl (List.mem_append_right _
      ((successGroupFold_groupNotices queue owners).symm ▸ noticed))

/-- The leading stream-values carrier tracks exactly the roots its item fold activated.
Witness: item integration preserves old roots and appends its complete notice frontier.
-/
theorem State.streamItemFold_groupNoticeTracking (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : let prepared := items.foldl streamItemStep (queue, [], [], [])
      GroupNoticeTracking queue.rootGroups
        (
          prepared.1,
          [.streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1]
        ) := by
  intro prepared ref member
  apply Or.inl
  rw [queue.streamItemFold_rootGroups items]
  simpa only [List.flatMap_singleton, rawGroupNoticeRefs] using member

-----------------------------------------------------------------------------------------
-- Actual preparation stages retain the earlier source-history tracking certificate
-----------------------------------------------------------------------------------------

/-- Earlier source notices remain tracked at task-success drain entry.
Witness: preparation keeps old roots, the owner fold closes or retains them, activation
adds its emitted frontier, and integration cannot erase earlier cancellation markers.
-/
theorem GroupNoticeTracking.taskSuccessPreparation {initial queue before}
    (tracked : GroupNoticeTracking initial (queue, before)) (occurrence : Occurrence)
    (result : TaskResult) (incoming : TaskNode)
    : let prepared :=
        ((queue.putTaskNode
            { incoming with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      GroupNoticeTracking initial
        (folded.1.startNewWork folded.2.2, before ++ folded.2.1) := by
  intro prepared folded
  have roots : prepared.rootGroups = queue.rootGroups :=
    State.maybeIntegrateWork_rootGroups _ _ _
  have first : GroupNoticeTracking queue.rootGroups
      (folded.1.startNewWork folded.2.2, folded.2.1) := by
    rw [← roots]
    exact prepared.successGroupFold_groupNoticeTracking incoming.task.groups
  apply tracked.append first
  intro ref member
  rw [State.startNewWork_cancelledGroups, successGroupFold_cancelledGroups]
  change ref ∈ ((queue.putTaskNode
    { incoming with value := some result.value }).maybeIntegrateWork
      result.work (some occurrence)).1.cancelledGroups
  rw [State.maybeIntegrateWork_cancelledGroups _ result.work (some occurrence)]
  exact State.addGroups_cancelledGroups_subset _ result.work.groups member

/-- Stream-item preparation retains every cancellation recorded before the input.
Witness: registration only appends cancellations; pruning and activation preserve them.
-/
theorem State.preparedStreamItems_cancelledGroups_subset (queue : State)
    (items : List StreamItem)
    : queue.cancelledGroups.Subset (queue.preparedStreamItems items).cancelledGroups := by
  apply State.preparedStreamItems_preserves
    (fun current => queue.cancelledGroups.Subset current.cancelledGroups)
    (List.Subset.refl _) items
  intro current item member prior
  apply prior.trans
  unfold State.integrateStreamItem
  rw [State.startNewWork_cancelledGroups, State.pruneEmptyGroups_cancelledGroups,
    State.maybeIntegrateWork_cancelledGroups]
  exact current.addGroups_cancelledGroups_subset item.work.groups

/-- Earlier source notices and the leading item notice are tracked at item drain entry.
Witness: item preparation activates its exact frontier while preserving prior cancellations.
-/
theorem GroupNoticeTracking.streamItemsPreparation {initial queue before}
    (tracked : GroupNoticeTracking initial (queue, before))
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : let prepared := items.foldl streamItemStep (queue, [], [], [])
      GroupNoticeTracking initial
        (
          prepared.1,
          before ++ [.streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1]
        ) :=
  tracked.append (queue.streamItemFold_groupNoticeTracking stream items)
    (queue.preparedStreamItems_cancelledGroups_subset items)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
