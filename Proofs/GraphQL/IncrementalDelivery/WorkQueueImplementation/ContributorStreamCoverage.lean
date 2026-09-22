import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshRegionCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeContents

/-! Healthy contributor coverage through sequential fresh item integrations and their drain. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A mixed ready drain preserves coverage of healthy surviving permanent contributors.
Witness: registrations are unchanged, backward edge provenance supplies earlier survival,
and the pointwise root-coverage theorem transports the actual stored path.
-/
theorem State.HealthyContributorsCovered.drainReadyGroups
    {queue : State} {work failed parents}
    (covered : queue.HealthyContributorsCovered work failed)
    (unique : queue.GroupKeysUnique) (forest : queue.RemovalForest parents)
    : queue.drainReadyGroups.1.HealthyContributorsCovered work failed := by
  intro task member key contributes healthy survives
  rw [State.drainReadyGroups_tasks] at member
  obtain ⟨node, found⟩ := survives
  obtain ⟨old, earlier, _⟩ := (queue.drainReadyGroups_descendants unique).1 key node found
  exact State.drainReadyGroups_root_coverage unique forest key
    (covered task member key contributes healthy ⟨old, earlier⟩) ⟨node, found⟩

-----------------------------------------------------------------------------------------
-- Item registration covers both old contributors and fresh-region contributors
-----------------------------------------------------------------------------------------

/-- Fresh item integration preserves healthy contributor coverage, including new tasks.
Witness: permanent retirement excludes revival of old missing contributors; old paths
survive integration, and source-region freshness supplies coverage for new contributors.
-/
theorem State.HealthyContributorsCovered.integrateStreamItem
    {queue : State} {work : Execution.Work} {parents failed seen}
    (covered : queue.HealthyContributorsCovered work failed)
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupKeysUnique)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (records : queue.GroupNodesMatchWork work) (children : queue.ChildGroupsUnique)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items) (fresh : item.occurrence ∉ seen)
    : (queue.integrateStreamItem item).HealthyContributorsCovered work failed := by
  intro task member key contributes healthy survives
  rw [State.integrateStreamItem_tasks] at member
  rcases List.mem_append.mp member with old | new
  · have priorLive : ∃ node, queue.groupNode? key = some node := by
      cases earlier : queue.groupNode? key with
      | some node => exact ⟨node, rfl⟩
      | none =>
          have retired := State.RetiredGroup.of_lookup_none (tasks task old key contributes) earlier
          have integrated := retired.maybeIntegrateWork item.work
          let candidates := (queue.maybeIntegrateWork item.work).2.newGroups
          have pruned := integrated.pruneEmptyGroups candidates
          have next := pruned.startNewWork
            { (queue.maybeIntegrateWork item.work).2 with
              newGroups := ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
                (queue.maybeIntegrateWork item.work).2.newGroups).2 }
          obtain ⟨node, lookup⟩ := survives
          have absent : (queue.integrateStreamItem item).groupNode? key = none := next.lookup_none
          rw [absent] at lookup
          contradiction
    exact State.integrateStreamItem_old_root_coverage unique registered item
      (covered task old key contributes healthy priorLive)
  · obtain ⟨group, member, same⟩ := matching.streamItem_childTasksCovered itemMember
      task new key contributes
    have taskMatch : TaskMatches work task := by
      obtain ⟨address, payload, equation, known⟩ :=
        matching.streamItem_childTask_producer itemMember new
      exact ⟨⟨address, payload, some item.occurrence, equation, known⟩,
        matching.streamItem_childTask_groupsExact itemMember new⟩
    have recordHealthy := taskMatch.contributor_recordHealthy generated contributes healthy
    exact same ▸ inventory.streamItem_healthy_group_root_coverage generated complete unique
      registered closed cancelled records children links canonical matching itemMember fresh
      member (same.symm ▸ recordHealthy) (same.symm ▸ survives)

-----------------------------------------------------------------------------------------
-- Thread independent bookkeeping through the actual multi-item preparation loop
-----------------------------------------------------------------------------------------

/-- Local induction evidence at an item boundary, with exactly the identities seen so far.
Every field is independently derived bookkeeping; only `covered` is the new induction goal.
-/
private structure StreamCoverageFrame (queue : State) (work : Execution.Work)
    (parents : Nat → Keys) (failed seen : List Occurrence)
    : Prop where
  covered : queue.HealthyContributorsCovered work failed
  inventory : queue.RegionInventory work seen
  complete : queue.ParentLinksComplete parents
  unique : queue.GroupKeysUnique
  registered : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  closed : queue.ParentRegistryClosed parents
  cancelled : queue.CancelledRecordsSupported work failed
  records : queue.GroupNodesMatchWork work
  children : queue.ChildGroupsUnique
  links : queue.ChildLinksCanonical parents

/-- One fresh item extends all preparation certificates at the same actual queue state.
Witness: reuse the independent registration, topology, cancellation, and region invariants.
-/
private theorem StreamCoverageFrame.integrateStreamItem {queue : State}
    {work parents failed seen stream items}
    (frame : StreamCoverageFrame queue work parents failed seen)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items) (fresh : item.occurrence ∉ seen)
    : StreamCoverageFrame (queue.integrateStreamItem item) work parents failed
        (item.occurrence :: seen) := by
  have exactParents : ∀ group ∈ item.work.groups,
      group.parent = (parents group.node.key).head? :=
    fun _ included => matching.streamItem_childGroups_parentCanonical canonical member included
  have descriptors : ∀ group ∈ item.work.groups,
      ∃ dependencies, GroupRecordAt work group.node dependencies :=
    fun _ included => matching.streamItem_childGroups_recordAt member included
  have registered := queue.integrateStreamItem_registration frame.registered frame.tasks
    matching member
  have cancelled := frame.cancelled.maybeIntegrateWork item.work none (by
    intro group included
    obtain ⟨dependencies, known⟩ := descriptors group included
    exact ⟨dependencies, known, by rw [canonical _ _ known]; exact exactParents group included⟩)
  refine ⟨
    frame.covered.integrateStreamItem frame.inventory generated frame.complete
      frame.unique frame.registered frame.tasks frame.closed frame.cancelled frame.records
      frame.children frame.links canonical matching member fresh,
    frame.inventory.integrateStreamItem matching member,
    frame.complete.integrateStreamItem frame.unique frame.registered frame.closed item
      exactParents,
    ((frame.unique.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
    registered.1,
    registered.2.1,
    frame.closed.integrateStreamItem frame.registered frame.tasks matching member
      canonical,
    ?_,
    ((frame.records.maybeIntegrateWork item.work descriptors).pruneEmptyGroups
      _).startNewWork
      _,
    ((frame.children.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
    ((frame.links.maybeIntegrateWork item.work exactParents).pruneEmptyGroups
      _).startNewWork
      _
  ⟩
  intro key included
  apply cancelled key
  simpa only [State.integrateStreamItem, State.startNewWork_cancelledGroups,
    State.pruneEmptyGroups_cancelledGroups]
    using included

/-- A matched fresh item batch preserves healthy contributor coverage through final drain.
Witness: source identities are threaded item by item, so freshness is derived at each
actual integration boundary rather than assumed for a preselected set of future states.
-/
theorem State.HealthyContributorsCovered.streamItems
    {queue : State} {work : Execution.Work} {parents failed seen}
    (covered : queue.HealthyContributorsCovered work failed)
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupKeysUnique)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (records : queue.GroupNodesMatchWork work) (children : queue.ChildGroupsUnique)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (distinct : (items.map StreamItem.occurrence).Nodup)
    (fresh : ∀ item ∈ items, item.occurrence ∉ seen)
    : (queue.streamItems stream items).1.HealthyContributorsCovered work failed := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (current : State) (observed : List Occurrence)
      (frame : StreamCoverageFrame current work parents failed observed)
      (nodup : (more.map StreamItem.occurrence).Nodup)
      (unseen : ∀ item ∈ more, item.occurrence ∉ observed)
      : ∃ finalSeen,
          StreamCoverageFrame (current.preparedStreamItems more) work parents failed finalSeen := by
    induction more generalizing current observed with
    | nil => exact ⟨observed, frame⟩
    | cons item rest ih =>
        have separated := List.nodup_cons.mp nodup
        rw [State.preparedStreamItems_cons]
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (current.integrateStreamItem item) (item.occurrence :: observed)
          (frame.integrateStreamItem generated canonical matching
            (included List.mem_cons_self) (unseen item List.mem_cons_self)) separated.2
        intro next member seenBefore
        rcases List.mem_cons.mp seenBefore with same | old
        · exact separated.1 (same ▸ List.mem_map_of_mem member)
        · exact unseen next (List.mem_cons_of_mem _ member) old
  rw [queue.streamItems_eq stream items]
  split
  · exact covered
  · obtain ⟨finalSeen, frame⟩ := loop items (List.Subset.refl _) queue seen
      ⟨covered, inventory, complete, unique, registered, tasks, closed, cancelled,
        records, children, links⟩ distinct fresh
    have forest := State.RemovalForest.of_generated generated frame.children frame.links
      frame.records canonical
    exact frame.covered.drainReadyGroups frame.unique forest

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
