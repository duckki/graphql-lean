import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorCompletion

/-! Source-prefix notice completion at both handlers' exact recursive-drain carriers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Task success retains all preceding source output and its single-pass owner output
-----------------------------------------------------------------------------------------

/-- A task-drain notice's announced uncancelled ancestor completed by that exact carrier.
Witness: generated replay derives the live-root frame; source tracking composes with
preparation and the single-pass owner output before the local drain theorem is applied.
-/
theorem ExecutedWork.taskDrainNoticeAncestor_completed
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
      let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := folded.1.startNewWork folded.2.2
      let outputs :=
        (initial.rawEventReplay before).2
        ++ folded.2.1
        ++ active.drainReadyGroups.2.take (index + 1)
      active.drainReadyGroups.2[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ref ∉ active.drainReadyGroups.1.cancelledGroups
      → ref ∈ initial.rootGroups ++ outputs.flatMap rawGroupNoticeRefs
      → ref ∈ outputs.flatMap rawGroupClosureRefs := by
  intro initial queue prepared folded active outputs selected noticed uncancelled announced
  obtain ⟨parents, canonical, frame⟩ :=
    generated.taskSuccess_drain_liveRootFrame matching matched incoming
      (generated.replayGraphEvents_rootsPresent before matching)
  have sourceTracking : GroupNoticeTracking initial.rootGroups
      (queue, (initial.rawEventReplay before).2) := by
    have source := initial.rawEventReplay_groupNoticeTracking before
    change GroupNoticeTracking _ ((initial.rawEventReplay before).1, _) at source
    rw [State.rawEventReplay_state] at source
    exact source
  have tracked := sourceTracking.taskSuccessPreparation occurrence result incoming
  exact tracked.drainNoticeAncestor_completed frame generated canonical
    active.groupNodes.length selected noticed known ancestor uncancelled announced

-----------------------------------------------------------------------------------------
-- Stream items retain the leading item carrier before the recursive drain's own prefix
-----------------------------------------------------------------------------------------

/-- An item-drain notice's announced uncancelled ancestor completed by that exact carrier.
Witness: item preparation supplies live roots and the leading notice frontier; source
tracking includes that actual item event before the selected recursive-drain prefix.
-/
theorem ExecutedWork.streamDrainNoticeAncestor_completed
    {work before stream items group groups streams child dependencies ref} {index : Nat}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    : let initial := State.initialize (Work.fromExecution work)
      let queue := initial.replayGraphEvents before
      let prepared := items.foldl streamItemStep (queue, [], [], [])
      let outputs :=
        (initial.rawEventReplay before).2
        ++ [.streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1]
        ++ prepared.1.drainReadyGroups.2.take (index + 1)
      prepared.1.drainReadyGroups.2[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ref ∉ prepared.1.drainReadyGroups.1.cancelledGroups
      → ref ∈ initial.rootGroups ++ outputs.flatMap rawGroupNoticeRefs
      → ref ∈ outputs.flatMap rawGroupClosureRefs := by
  intro initial queue prepared outputs selected noticed uncancelled announced
  obtain ⟨parents, canonical, frame⟩ :=
    generated.streamItems_prepared_liveRootFrame matching matched
      (generated.replayGraphEvents_rootsPresent before matching)
  have sourceTracking : GroupNoticeTracking initial.rootGroups
      (queue, (initial.rawEventReplay before).2) := by
    have source := initial.rawEventReplay_groupNoticeTracking before
    change GroupNoticeTracking _ ((initial.rawEventReplay before).1, _) at source
    rw [State.rawEventReplay_state] at source
    exact source
  have tracked := sourceTracking.streamItemsPreparation stream items
  exact tracked.drainNoticeAncestor_completed frame generated canonical
    prepared.1.groupNodes.length selected noticed known ancestor uncancelled announced

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
