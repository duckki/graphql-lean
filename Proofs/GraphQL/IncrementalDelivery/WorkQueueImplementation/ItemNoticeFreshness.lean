import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNoticeFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeRegistrationHistory

/-! Item handlers do not repeat group notices from earlier source inputs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Pruned integration frontiers remain outside the old permanent registry
-----------------------------------------------------------------------------------------

/-- Every group notice from integrated work is fresh for the pre-integration registry.
Witness: fresh candidates cannot have a live descendant path into the old registry.
Pruning retains only descendants of those candidates, including through taskless shells.
-/
theorem State.pruneIntegratedWork_notice_unregistered {queue : State}
    (registered : queue.LiveGroupsRegistered) (work : Work)
    (parentTask : Option Occurrence := none) {child}
    (noticed
      : child
        ∈ ((queue.maybeIntegrateWork work parentTask).1.pruneEmptyGroups
            (queue.maybeIntegrateWork work parentTask).2.newGroups).2)
    : child.key ∉ queue.registeredGroups := by
  obtain ⟨root, included, path⟩ := (State.pruneEmptyGroups_descendants _ _).2 child noticed
  change root ∈ (queue.addGroups work.groups).2 at included
  obtain ⟨_, _, _, _, fresh, _⟩ := queue.addGroups_newGroup_candidate work.groups included
  exact ((queue.maybeIntegrateWork_freshChildLinks registered work parentTask).descendant
    path fresh)

/-- A complete matching item fold emits no group notice from its entry registry.
Witness: each fresh pruned frontier excludes the current registry, which monotonically
contains the entry registry. This permits distinct items to prune genuine taskless parents.
-/
theorem State.streamItemFold_noRegisteredNotice {queue : State} {work stream items key}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    (registered : key ∈ queue.registeredGroups)
    : key
      ∉ ((items.foldl streamItemStep (queue, [], [], [])).2.1.map
          Execution.DeliveryNode.key) := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue)
      (live : acc.1.LiveGroupsRegistered) (tasks : acc.1.TaskGroupsRegistered)
      (registered : key ∈ acc.1.registeredGroups)
      (absent : key ∉ acc.2.1.map Execution.DeliveryNode.key)
      : key ∉ ((more.foldl streamItemStep acc).2.1.map Execution.DeliveryNode.key) := by
    induction more generalizing acc with
    | nil => exact absent
    | cons item rest ih =>
        have next := acc.1.integrateStreamItem_registration live tasks matched
          (included List.mem_cons_self)
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (streamItemStep acc item) next.1 next.2.1 (next.2.2 registered)
        simp only [streamItemStep, List.map_append, List.mem_append, not_or]
        refine ⟨absent, ?_⟩
        intro repeated
        obtain ⟨child, noticed, same⟩ := List.mem_map.mp repeated
        exact acc.1.pruneIntegratedWork_notice_unregistered live item.work none noticed
          (same ▸ registered)
  exact loop items (List.Subset.refl _) (queue, [], [], []) live tasks registered
    (by simp)

-----------------------------------------------------------------------------------------
-- Earlier announced keys are both registered and protected through the later drain
-----------------------------------------------------------------------------------------

/-- An item handler cannot reannounce any initial or earlier-source group notice.
Witness: the leading item fold excludes all old registered keys. Its following drain
excludes their permanently protected ancestry, using the generated prepared live-root frame.
-/
theorem ExecutedWork.streamItems_noEarlierGroupNotice
    {work before stream items key} (generated : ExecutedWork work)
    (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    (announced
      : key
        ∈ (State.initialize (Work.fromExecution work)).rootGroups
          ++ ((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
              rawGroupNoticeKeys)
    : key
      ∉ ((((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).streamItems
            stream items).2.flatMap
          rawGroupNoticeKeys) := by
  let initial := State.initialize (Work.fromExecution work)
  let queue := initial.replayGraphEvents before
  have registry := createWorkQueue_registration work
  have covered := initial.replayGraphEvents_registration registry.1 registry.2 before matching
  have registered :=
    createWorkQueue_rawEventReplay_announcedRegistered before matching key announced
  have protectedKey :=
    generated.rawEventReplay_announcedAncestorsRetired before matching key announced
  have noLeading := queue.streamItemFold_noRegisteredNotice covered.1 covered.2.1 matched registered
  have preparedProtected : (queue.preparedStreamItems items).AncestorsRetired work key :=
    State.preparedStreamItems_preserves (fun current => current.AncestorsRetired work key)
      protectedKey items (fun current item _ prior => prior.mono (fun _ retired =>
        ((retired.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _))
  obtain ⟨parents, canonical, frame⟩ := generated.streamItems_prepared_liveRootFrame
    matching matched (generated.replayGraphEvents_rootsPresent before matching)
  have noDrain := frame.drainReadyGroups_go_noProtectedNotice generated canonical
    preparedProtected (queue.preparedStreamItems items).groupNodes.length
  change key ∉ (queue.streamItems stream items).2.flatMap rawGroupNoticeKeys
  rw [queue.streamItems_eq stream items]
  split
  · simp
  · rw [List.flatMap_cons, List.mem_append, not_or]
    exact ⟨noLeading, noDrain⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
