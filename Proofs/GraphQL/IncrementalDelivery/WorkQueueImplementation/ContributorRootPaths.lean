import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledProducedGroupCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshLiveRegionCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPathContinuation

/-! Concrete root paths for all surviving registered contributors, independent of failure health. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every live contributor of a permanently registered task lies below an active root. -/
def State.ContributorsCovered (queue : State) : Prop :=
  ∀ task ∈ queue.tasks,
  ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
    (∃ node, queue.groupNode? ref = some node)
    → ∃ root ∈ queue.rootGroups, queue.LiveDescendant root ref

/-- Pending controls leave every permanent contributor path unchanged. -/
theorem State.ContributorsCovered.withGroupFailures {queue}
    (covered : State.ContributorsCovered queue)
    (groupFailureEvents : List GroupFailureEvent)
    : ({ queue with groupFailureEvents } : State).ContributorsCovered := by
  intro task registered ref contributes live
  obtain ⟨root, active, path⟩ := covered task registered ref contributes live
  exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩

/-- Cache exposure changes neither permanent registrations nor root paths. -/
theorem State.ContributorsCovered.cacheTaskFailures {queue}
    (covered : State.ContributorsCovered queue) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).ContributorsCovered := by
  intro task registered ref contributes live
  rw [State.cacheTaskFailures_tasks] at registered
  have beforeLive : ∃ node, queue.groupNode? ref = some node := by
    simpa only [State.groupNode?, State.cacheTaskFailures_groupNodes] using live
  obtain ⟨root, active, path⟩ := covered task registered ref contributes beforeLive
  exact ⟨
    root,
    by rwa [State.cacheTaskFailures_rootGroups],
    path.of_groupNodes_eq (queue.cacheTaskFailures_groupNodes available)
  ⟩

/-- Success-only draining retains root coverage for every surviving contributor. -/
theorem State.ContributorsCovered.drainReadyGroups {queue work parents}
    (covered : State.ContributorsCovered queue)
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat))
    : (queue.drainReadyGroups available).1.ContributorsCovered := by
  intro task registered ref contributes live
  rw [State.drainReadyGroups_tasks queue available] at registered
  obtain ⟨node, found⟩ := live
  obtain ⟨old, earlier, _⟩ := (queue.drainReadyGroups_descendants frame.keys available).1
    ref node found
  exact State.drainReadyGroups_root_coverage frame.keys
    (State.RemovalForest.of_generated generated frame.children frame.links frame.records canonical)
    available ref (covered task registered ref contributes ⟨old, earlier⟩) ⟨node, found⟩

/-- Fresh item integration covers both surviving old owners and the new live region. -/
theorem State.ContributorsCovered.integrateStreamItem
    {queue work parents seen stream items item}
    (covered : State.ContributorsCovered queue)
    (frame : ParentCutFrame queue work parents)
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items) (fresh : item.occurrence ∉ seen)
    (available : List (Occurrence × Nat))
    : (queue.integrateStreamItem item available).ContributorsCovered := by
  intro task registered ref contributes live
  rw [State.integrateStreamItem_tasks queue item available] at registered
  rcases List.mem_append.mp registered with old | new
  · have beforeLive : ∃ node, queue.groupNode? ref = some node := by
      cases found : queue.groupNode? ref with
      | some node => exact ⟨node, rfl⟩
      | none =>
          have retired : (queue.integrateStreamItem item available).RetiredGroup ref :=
            (((State.RetiredGroup.of_lookup_none
            (frame.tasks task old ref contributes) found).maybeIntegrateWork item.work
            ).pruneEmptyGroups _).startNewWork _ available
          obtain ⟨node, lookup⟩ := live
          rw [retired.lookup_none] at lookup
          contradiction
    rcases frame.integrateStreamItem_rootCoveredOrRetired generated canonical matching member
        (.inl (covered task old ref contributes beforeLive)) available with path | retired
    · exact path
    · obtain ⟨node, lookup⟩ := live
      rw [retired.lookup_none] at lookup
      contradiction
  · obtain ⟨group, groupMember, same⟩ := matching.streamItem_childTasksCovered generated.declarations member
      task new ref contributes
    exact same ▸ frame.streamItem_live_group_root_coverage inventory generated canonical
      matching member fresh groupMember available (same.symm ▸ live)

/-- An actual multi-item receipt retains coverage through preparation and its final drain. -/
theorem State.ContributorsCovered.streamItems {queue work parents seen stream items}
    (covered : State.ContributorsCovered queue)
    (frame : ParentCutFrame queue work parents)
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (distinct : (items.map StreamItem.occurrence).Nodup)
    (fresh : ∀ item ∈ items, item.occurrence ∉ seen) (available : List (Occurrence × Nat))
    : (queue.streamItems stream items available).1.ContributorsCovered := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (current : State) (observed : List Occurrence)
      (frame : ParentCutFrame current work parents)
      (inventory : current.RegionInventory work observed) (covered : current.ContributorsCovered)
      (nodup : (more.map StreamItem.occurrence).Nodup)
      (fresh : ∀ item ∈ more, item.occurrence ∉ observed)
      : ∃ finalSeen,
          let prepared := current.preparedStreamItems more available
          ParentCutFrame prepared work parents
          ∧ prepared.RegionInventory work finalSeen ∧ prepared.ContributorsCovered := by
    induction more generalizing current observed with
    | nil => exact ⟨observed, frame, inventory, covered⟩
    | cons item rest ih =>
        have separate := List.nodup_cons.mp nodup
        rw [State.preparedStreamItems_cons current item rest available]
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (current.integrateStreamItem item available) (item.occurrence :: observed)
          (frame.integrateStreamItem generated canonical matching
            (included List.mem_cons_self) available)
          (inventory.integrateStreamItem matching (included List.mem_cons_self) available)
          (covered.integrateStreamItem frame inventory generated canonical matching
            (included List.mem_cons_self) (fresh item List.mem_cons_self) available)
          separate.2
        intro next member known
        rcases List.mem_cons.mp known with same | old
        · exact separate.1 (same ▸ List.mem_map_of_mem member)
        · exact fresh next (List.mem_cons_of_mem _ member) old
  rw [queue.streamItems_eq stream items available]
  split
  · exact covered
  · obtain ⟨_, parent, _, prepared⟩ := loop items (List.Subset.refl _) queue seen
      frame inventory covered distinct fresh
    exact prepared.drainReadyGroups parent generated canonical available

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
