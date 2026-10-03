import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedNoticeReplay

/-! Task-success handlers cannot repeat a group notice from an earlier source prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Preparation, owner release, activation, and draining retain the same protected ref
-----------------------------------------------------------------------------------------

/-- A matching task-success handler emits no notice for a previously protected group.
Witness: value installation and child integration preserve permanent retirement. The
prepared live-root frame excludes the ref from the entire single-pass owner output;
activation preserves protection, and the actual subsequent drain also excludes it.
-/
theorem ExecutedWork.taskSuccess_noProtectedNotice
    {work before occurrence result ref} (generated : ExecutedWork work)
    (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (protectedRef
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).AncestorsRetired
          work ref)
    : ref
      ∉ ((((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).taskSuccess
            occurrence result).2.flatMap
          rawGroupNoticeRefs) := by
  let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
  change ref ∉ (queue.taskSuccess occurrence result).2.flatMap rawGroupNoticeRefs
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some incoming =>
      cases healthy : queue.taskHasHealthyOwner incoming.task with
      | false =>
          rw [queue.taskSuccess_eq occurrence result incoming found]
          simp [healthy]
      | true =>
          let stored := queue.putTaskNode { incoming with value := some result.value }
          let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
          let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
          let active := folded.1.startNewWork folded.2.2
          obtain ⟨parents, canonical, records, links, live, tasks, roots, _⟩ :=
            generated.replayGraphEvents_preparedRetirement before matching matched incoming
          obtain ⟨refs, _, support⟩ :=
            generated.taskSuccess_prepared_noticeMetadata matching matched incoming
          have storedPresent : stored.RootGroupsPresent :=
            generated.replayGraphEvents_rootsPresent before matching
          have preparedPresent := storedPresent.maybeIntegrateWork result.work (some occurrence)
          have preparedFrame : LiveRootFrame prepared work parents :=
            ⟨refs, records, links, live, tasks, roots, support, preparedPresent⟩
          have storedProtected : stored.AncestorsRetired work ref := protectedRef
          have preparedProtected := storedProtected.mono
            (fun _ retired => retired.maybeIntegrateWork result.work (some occurrence))
          have ownerExclusion := preparedFrame.successGroupFold_noProtectedNotice
            generated canonical preparedProtected incoming.task.groups
          have activeProtected : active.AncestorsRetired work ref :=
            ownerExclusion.2.1.mono (fun _ retired => retired.startNewWork folded.2.2)
          obtain ⟨activeParents, activeCanonical, activeFrame⟩ :=
            generated.taskSuccess_drain_liveRootFrame matching matched incoming
              (generated.replayGraphEvents_rootsPresent before matching)
          have drainExclusion := activeFrame.drainReadyGroups_go_noProtectedNotice generated
            activeCanonical activeProtected active.groupNodes.length
          have equation : queue.taskSuccess occurrence result
              = (active.drainReadyGroups.1, folded.2.1 ++ active.drainReadyGroups.2) := by
            rw [queue.taskSuccess_eq occurrence result incoming found]
            simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rfl
          rw [equation, List.flatMap_append, List.mem_append, not_or]
          exact ⟨ownerExclusion.2.2, drainExclusion⟩

-----------------------------------------------------------------------------------------
-- Earlier announcements supply protection, even when their nodes have since disappeared
-----------------------------------------------------------------------------------------

/-- A task-success handler never reannounces an initial or earlier-source group notice.
Witness: generated matching replay supplies permanent ancestry for every earlier notice;
the actual healthy, ignored, owner-fold, and drain branches all respect that protection.
Uniqueness within a single carrier and earlier carriers of this handler remain separate.
-/
theorem ExecutedWork.taskSuccess_noEarlierGroupNotice
    {work before occurrence result ref} (generated : ExecutedWork work)
    (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (announced
      : ref
        ∈ (State.initialize (Work.fromExecution work)).rootGroups
          ++ ((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
              rawGroupNoticeRefs)
    : ref
      ∉ ((((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).taskSuccess
            occurrence result).2.flatMap
          rawGroupNoticeRefs) :=
  generated.taskSuccess_noProtectedNotice matching matched
    (generated.rawEventReplay_announcedAncestorsRetired before matching ref announced)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
