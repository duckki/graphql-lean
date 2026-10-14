import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiveContributorCoverage

/-! Live contributor coverage through the actual sequential fresh-item preparation fold. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Independent topology and exposure evidence follows the same item accumulator
-----------------------------------------------------------------------------------------

private structure LiveStreamFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (seen : List Occurrence)
    : Prop where
  covered : queue.LiveContributorsCovered
  inventory : queue.RegionInventory work seen
  complete : queue.ParentLinksComplete parents
  unique : queue.GroupRefsUnique
  registered : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  closed : queue.ParentRegistryClosed parents
  safe : queue.LiveParentsUncancelled
  fields : queue.GroupParentsCanonical parents
  records : queue.GroupNodesMatchWork work
  children : queue.ChildGroupsUnique
  links : queue.ChildLinksCanonical parents

private theorem LiveStreamFrame.integrateStreamItem {queue : State}
    {work parents seen stream items} (frame : LiveStreamFrame queue work parents seen)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items) (fresh : item.occurrence ∉ seen)
    : LiveStreamFrame (queue.integrateStreamItem item) work parents
        (item.occurrence :: seen) := by
  have exactParents : ∀ group ∈ item.work.groups,
      group.parent = (parents group.node.ref).head? :=
    fun _ included => matching.streamItem_childGroups_parentCanonical canonical member included
  have descriptors : ∀ group ∈ item.work.groups,
      ∃ dependencies, GroupRecordAt work group.node dependencies :=
    fun _ included => matching.streamItem_childGroups_recordAt member included
  have registered := queue.integrateStreamItem_registration frame.registered frame.tasks matching member
  exact ⟨frame.covered.integrateStreamItem frame.inventory generated frame.complete
      frame.unique frame.registered frame.tasks frame.closed frame.safe frame.fields
      frame.records frame.children frame.links canonical matching member fresh,
    frame.inventory.integrateStreamItem matching member,
    frame.complete.integrateStreamItem frame.unique frame.registered frame.closed item exactParents,
    ((frame.unique.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
    registered.1, registered.2.1,
    frame.closed.integrateStreamItem frame.registered frame.tasks matching member canonical,
    ((frame.safe.maybeIntegrateWork frame.registered frame.closed frame.fields item.work
      exactParents (matching.streamItem_parentsBefore member)).pruneEmptyGroups _).startNewWork _,
    ((frame.fields.maybeIntegrateWork item.work exactParents).pruneEmptyGroups _).startNewWork _,
    ((frame.records.maybeIntegrateWork item.work descriptors).pruneEmptyGroups _).startNewWork _,
    ((frame.children.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
    ((frame.links.maybeIntegrateWork item.work exactParents).pruneEmptyGroups _).startNewWork _⟩

-----------------------------------------------------------------------------------------
-- Sequential freshness and the final mixed ready drain
-----------------------------------------------------------------------------------------

/-- A matching fresh item batch preserves all live contributor coverage through its drain.
Witness: thread actual exposure, parent safety, and coverage together at each integration.
Within-batch uniqueness derives freshness after preceding items; no future snapshot is assumed.
-/
theorem State.LiveContributorsCovered.streamItems
    {queue : State} {work : Execution.Work} {parents seen}
    (covered : queue.LiveContributorsCovered)
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (safe : queue.LiveParentsUncancelled) (fields : queue.GroupParentsCanonical parents)
    (records : queue.GroupNodesMatchWork work) (children : queue.ChildGroupsUnique)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (distinct : (items.map StreamItem.occurrence).Nodup)
    (fresh : ∀ item ∈ items, item.occurrence ∉ seen)
    : (queue.streamItems stream items).1.LiveContributorsCovered := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (current : State) (observed : List Occurrence)
      (frame : LiveStreamFrame current work parents observed)
      (nodup : (more.map StreamItem.occurrence).Nodup)
      (unseen : ∀ item ∈ more, item.occurrence ∉ observed)
      : ∃ finalSeen, LiveStreamFrame (current.preparedStreamItems more) work parents finalSeen := by
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
      ⟨covered, inventory, complete, unique, registered, tasks, closed, safe, fields,
        records, children, links⟩ distinct fresh
    exact frame.covered.drainReadyGroups frame.unique
      (State.RemovalForest.of_generated generated frame.children frame.links frame.records canonical)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
