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
    (unique : queue.GroupRefsUnique) (forest : queue.RemovalForest parents)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.HealthyContributorsCovered work failed := by
  intro task member ref contributes healthy survives
  rw [State.drainReadyGroups_tasks queue available] at member
  obtain ⟨node, found⟩ := survives
  obtain ⟨old, earlier, _⟩ := (queue.drainReadyGroups_descendants unique available).1 ref node found
  exact State.drainReadyGroups_root_coverage unique forest available ref
    (covered task member ref contributes healthy ⟨old, earlier⟩) ⟨node, found⟩

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
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (records : queue.GroupNodesMatchWork work) (children : queue.ChildGroupsUnique)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items) (fresh : item.occurrence ∉ seen)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).HealthyContributorsCovered work
        failed := by
  intro task member ref contributes healthy survives
  rw [State.integrateStreamItem_tasks queue item available] at member
  rcases List.mem_append.mp member with old | new
  · have priorLive : ∃ node, queue.groupNode? ref = some node := by
      cases earlier : queue.groupNode? ref with
      | some node => exact ⟨node, rfl⟩
      | none =>
          have retired := State.RetiredGroup.of_lookup_none (tasks task old ref contributes) earlier
          have integrated := retired.maybeIntegrateWork item.work
          let candidates := (queue.maybeIntegrateWork item.work).2.newGroups
          have pruned := integrated.pruneEmptyGroups candidates
          have next := pruned.startNewWork
            { (queue.maybeIntegrateWork item.work).2 with
              newGroups := ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
                (queue.maybeIntegrateWork item.work).2.newGroups).2 } available
          obtain ⟨node, lookup⟩ := survives
          have absent : (queue.integrateStreamItem item available).groupNode? ref = none :=
            next.lookup_none
          rw [absent] at lookup
          contradiction
    have descriptors : ∀ group ∈ item.work.groups,
        ∃ dependencies, GroupRecordAt work group.node dependencies :=
      fun _ member => matching.streamItem_childGroups_recordAt itemMember member
    have fields : ∀ group ∈ item.work.groups,
        group.parent = (parents group.node.ref).head? :=
      fun _ member => matching.streamItem_childGroups_parentCanonical canonical itemMember member
    have forest := State.RemovalForest.of_generated generated
      (children.maybeIntegrateWork item.work) (links.maybeIntegrateWork item.work fields)
      (records.maybeIntegrateWork item.work descriptors) canonical
    exact State.integrateStreamItem_old_root_coverage unique registered item forest
      (covered task old ref contributes healthy priorLive) available survives
  · obtain ⟨group, member, same⟩ := matching.streamItem_childTasksCovered generated.declarations itemMember
      task new ref contributes
    have taskMatch : TaskMatches work task := by
      obtain ⟨address, payload, equation, known⟩ :=
        matching.streamItem_childTask_producer itemMember new
      exact ⟨⟨address, payload, some item.occurrence, equation, known⟩,
        matching.streamItem_childTask_groupsExact itemMember new⟩
    have recordHealthy := taskMatch.contributor_recordHealthy generated contributes healthy
    exact same ▸ inventory.streamItem_healthy_group_root_coverage generated complete unique
      registered closed cancelled records children links canonical matching itemMember fresh
      member (same.symm ▸ recordHealthy) available (same.symm ▸ survives)

-----------------------------------------------------------------------------------------
-- Thread independent bookkeeping through the actual multi-item preparation loop
-----------------------------------------------------------------------------------------

/-- Local induction evidence at an item boundary, with exactly the identities seen so far.
Every field is independently derived bookkeeping; only `covered` is the new induction goal.
-/
private structure StreamCoverageFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (failed seen : List Occurrence)
    : Prop where
  covered : queue.HealthyContributorsCovered work failed
  inventory : queue.RegionInventory work seen
  complete : queue.ParentLinksComplete parents
  unique : queue.GroupRefsUnique
  registered : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  closed : queue.ParentRegistryClosed parents
  cancelled : queue.CancelledRecordsSupported work failed
  records : queue.GroupNodesMatchWork work
  children : queue.ChildGroupsUnique
  links : queue.ChildLinksCanonical parents
  caches : queue.CachedFailuresSupported work failed
  started : queue.StartedTasksRegistered
  matching : queue.RegisteredTasksMatch work
  sound : queue.GroupMembershipSound
  registration : queue.RegistrationFrame work

/-- One fresh item extends all preparation certificates at the same actual queue state.
Witness: reuse the independent registration, topology, cancellation, and region invariants.
-/
private theorem StreamCoverageFrame.integrateStreamItem {queue : State}
    {work parents failed seen stream items}
    (frame : StreamCoverageFrame queue work parents failed seen)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items) (fresh : item.occurrence ∉ seen)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    : StreamCoverageFrame (queue.integrateStreamItem item available) work parents failed
        (item.occurrence :: seen) := by
  have exactParents : ∀ group ∈ item.work.groups,
      group.parent = (parents group.node.ref).head? :=
    fun _ included => matching.streamItem_childGroups_parentCanonical canonical member included
  have descriptors : ∀ group ∈ item.work.groups,
      ∃ dependencies, GroupRecordAt work group.node dependencies :=
    fun _ included => matching.streamItem_childGroups_recordAt member included
  have registered := queue.integrateStreamItem_registration frame.registered frame.tasks
    matching member frame.registration available
  have cancelled := frame.cancelled.maybeIntegrateWork item.work none (by
    intro group included
    obtain ⟨dependencies, known⟩ := descriptors group included
    exact ⟨dependencies, known, by rw [canonical _ _ known]; exact exactParents group included⟩)
  have known : ∀ task ∈ item.work.tasks, TaskMatches work task := by
    intro task supplied
    obtain ⟨address, payload, same, located⟩ :=
      matching.streamItem_childTask_producer member supplied
    exact ⟨⟨address, payload, some item.occurrence, same, located⟩,
      matching.streamItem_childTask_groupsExact member supplied⟩
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let more := { integrated.2 with newGroups := pruned.2 }
  have cached :=
    (frame.caches.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups
  have started :=
    (frame.started.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups
  have taskMatch :=
    (frame.matching.maybeIntegrateWork item.work known).pruneEmptyGroups integrated.2.newGroups
  have sound := (frame.sound.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups
  have records :=
    (frame.records.maybeIntegrateWork item.work descriptors).pruneEmptyGroups integrated.2.newGroups
  have links :=
    (frame.links.maybeIntegrateWork item.work exactParents).pruneEmptyGroups integrated.2.newGroups
  have prunedCancelled : pruned.1.CancelledRecordsSupported work failed := by
    intro ref included
    apply cancelled ref
    simpa only [pruned, State.pruneEmptyGroups_cancelledGroups] using included
  have supported := prunedCancelled.startNewWork cached started taskMatch sound
    records links canonical more available recorded
  refine ⟨
    frame.covered.integrateStreamItem frame.inventory generated frame.complete
      frame.unique frame.registered frame.tasks frame.closed frame.cancelled frame.records
      frame.children frame.links canonical matching member fresh available,
    frame.inventory.integrateStreamItem matching member available,
    frame.complete.integrateStreamItem frame.unique frame.registered frame.closed item
      exactParents available,
    ((frame.unique.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
      available,
    registered.1,
    registered.2.1,
    frame.closed.integrateStreamItem frame.registered frame.tasks frame.registration
      matching member canonical available,
    supported,
    ((frame.records.maybeIntegrateWork item.work descriptors).pruneEmptyGroups
      _).startNewWork
      _ available,
    ((frame.children.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
      available,
    ((frame.links.maybeIntegrateWork item.work exactParents).pruneEmptyGroups
      _).startNewWork
      _ available,
    cached.startNewWork_available started taskMatch more available recorded,
    started.startNewWork more available,
    taskMatch.startNewWork more available,
    sound.startNewWork more available,
    (frame.registration.integrateStreamItem matching member available).1
  ⟩

/-- A matched fresh item batch preserves healthy contributor coverage through final drain.
Witness: source identities are threaded item by item, so freshness is derived at each
actual integration boundary rather than assumed for a preselected set of future states.
-/
theorem State.HealthyContributorsCovered.streamItems
    {queue : State} {work : Execution.Work} {parents failed seen}
    (covered : queue.HealthyContributorsCovered work failed)
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (records : queue.GroupNodesMatchWork work) (children : queue.ChildGroupsUnique)
    (links : queue.ChildLinksCanonical parents)
    (caches : queue.CachedFailuresSupported work failed)
    (started : queue.StartedTasksRegistered) (taskMatch : queue.RegisteredTasksMatch work)
    (sound : queue.GroupMembershipSound)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (distinct : (items.map StreamItem.occurrence).Nodup)
    (fresh : ∀ item ∈ items, item.occurrence ∉ seen)
    (available : List (Occurrence × Nat) := [])
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.streamItems stream items available).1.HealthyContributorsCovered work
        failed := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (current : State) (observed : List Occurrence)
      (frame : StreamCoverageFrame current work parents failed observed)
      (nodup : (more.map StreamItem.occurrence).Nodup)
      (unseen : ∀ item ∈ more, item.occurrence ∉ observed)
      : ∃ finalSeen,
          StreamCoverageFrame (current.preparedStreamItems more available) work parents failed
            finalSeen := by
    induction more generalizing current observed with
    | nil => exact ⟨observed, frame⟩
    | cons item rest ih =>
        have separated := List.nodup_cons.mp nodup
        rw [State.preparedStreamItems_cons current item rest available]
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (current.integrateStreamItem item available) (item.occurrence :: observed)
          (frame.integrateStreamItem generated canonical matching
            (included List.mem_cons_self) (unseen item List.mem_cons_self) available recorded)
          separated.2
        intro next member seenBefore
        rcases List.mem_cons.mp seenBefore with same | old
        · exact separated.1 (same ▸ List.mem_map_of_mem member)
        · exact unseen next (List.mem_cons_of_mem _ member) old
  rw [queue.streamItems_eq stream items available]
  split
  · exact covered
  · obtain ⟨finalSeen, frame⟩ := loop items (List.Subset.refl _) queue seen
      ⟨covered, inventory, complete, unique, registered, tasks, closed, cancelled,
        records, children, links, caches, started, taskMatch, sound, context⟩ distinct fresh
    have forest := State.RemovalForest.of_generated generated frame.children frame.links
      frame.records canonical
    exact frame.covered.drainReadyGroups frame.unique forest available

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
