import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFrontierUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeFreshness

/-! One multi-item carrier cannot contain repeated group-notice refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Each item's unique pruned frontier excludes all earlier item registrations
-----------------------------------------------------------------------------------------

/-- The accumulated group notices from matching item preparation have unique refs.
Witness: each individual integration has a unique pruned frontier. Earlier notices remain
registered, so the next item's fresh links exclude them even after taskless-shell pruning.
The metadata induction follows the actual item fold; no source-order freshness premise is used.
-/
theorem State.streamItemFold_groupNoticesUnique {queue : State}
    {work parents stream items} (refs : queue.GroupRefsUnique)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    : (((items.foldl streamItemStep (queue, [], [], [])).2.1).map
        Execution.DeliveryNode.ref).Nodup := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue)
      (refs : acc.1.GroupRefsUnique) (live : acc.1.LiveGroupsRegistered)
      (tasks : acc.1.TaskGroupsRegistered) (links : acc.1.ChildLinksCanonical parents)
      (children : acc.1.ChildGroupsUnique)
      (known : ∀ child ∈ acc.2.1, child.ref ∈ acc.1.registeredGroups)
      (unique : (acc.2.1.map Execution.DeliveryNode.ref).Nodup)
      : (((more.foldl streamItemStep acc).2.1).map Execution.DeliveryNode.ref).Nodup := by
    induction more generalizing acc with
    | nil => exact unique
    | cons item rest ih =>
        have member := included List.mem_cons_self
        have parentFields := fun group candidate =>
          matched.streamItem_childGroups_parentCanonical canonical member
            (group := group) candidate
        have nextRegistration := acc.1.integrateStreamItem_registration live tasks matched member
        have nextRefs : (acc.1.integrateStreamItem item).GroupRefsUnique :=
          ((refs.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
        have nextLinks : (acc.1.integrateStreamItem item).ChildLinksCanonical parents :=
          ((links.maybeIntegrateWork item.work parentFields).pruneEmptyGroups _).startNewWork _
        have nextChildren : (acc.1.integrateStreamItem item).ChildGroupsUnique :=
          ((children.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
        apply ih (fun _ later => included (List.mem_cons_of_mem _ later))
          (streamItemStep acc item) nextRefs nextRegistration.1 nextRegistration.2.1
          nextLinks nextChildren
        · intro child noticed
          rcases List.mem_append.mp noticed with old | new
          · exact nextRegistration.2.2 (known child old)
          · exact acc.1.integrateStreamItem_groupNoticesRegistered refs live tasks
              matched member child new
        · change ((acc.2.1 ++
            ((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
              (acc.1.maybeIntegrateWork item.work).2.newGroups).2).map
                Execution.DeliveryNode.ref).Nodup
          rw [List.map_append, List.nodup_append]
          refine ⟨unique, acc.1.maybeIntegrateWork_pruned_unique links children item.work
            parentFields, ?_⟩
          intro ref earlier other later same
          obtain ⟨prior, priorMember, priorRef⟩ := List.mem_map.mp earlier
          obtain ⟨child, noticed, childRef⟩ := List.mem_map.mp later
          exact acc.1.pruneIntegratedWork_notice_unregistered live item.work none noticed
            ((childRef.trans (same.symm.trans priorRef.symm)).symm ▸ known prior priorMember)
  exact loop items (List.Subset.refl _) (queue, [], [], []) refs live tasks links children
    (by simp) (by simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
