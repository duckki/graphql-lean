import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationStreamReplay

/-! Source-derived item-prefix certificates shared by task and source progress proofs. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

/-- Actual reference item prefixes supply native receipt certificates independently of
resource representation or cleanup conclusions.
-/
theorem streamItems_cacheFrames_of_structural {queue : ReferenceWorkQueue.State}
    {work parents} (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (roots : ReferenceWorkQueue.LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work)
    (owners : queue.TaskOwnerFrame work) (children : queue.ChildGroupsUnique)
    (keys : queue.TaskNodeKeysUnique) (stream : DeliveryNode)
    (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat))
    : ∀ earlier item later,
        items = earlier ++ item :: later
        → StreamItemCacheFrame (queue.preparedStreamItems earlier available) work
            item := by
  intro earlier item later partition
  have included : earlier.Subset items := by
    intro supplied member
    rw [partition]
    exact List.mem_append_left _ member
  have member : item ∈ items := by
    rw [partition]
    exact List.mem_append_right _ List.mem_cons_self
  have partialMatch : (ReferenceWorkQueue.GraphEvent.streamItems stream earlier
      ).MatchesWork work := fun item member => matched item (included member)
  have preparedRoots := (roots.prepareItems retired generated canonical partialMatch available).1
  have preparedOwners := owners.prepareItems_of_registered roots.registered roots.tasks
    roots.present generated.declarations partialMatch available
  have preparedKeys : (queue.preparedStreamItems earlier available).TaskNodeKeysUnique := by
    apply ReferenceWorkQueue.State.preparedStreamItems_preserves
      (fun queue => queue.TaskNodeKeysUnique) keys earlier available
    intro queue item _ prior
    exact ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available
  exact ⟨preparedRoots.present, preparedOwners.matching, preparedKeys, parents,
    streamItem_startFrames generated canonical roots retired owners children stream items
      matched earlier included item member available⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
