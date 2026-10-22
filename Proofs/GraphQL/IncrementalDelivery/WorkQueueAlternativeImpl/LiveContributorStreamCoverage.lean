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
  context : queue.RegistrationFrame work
  cancelled : queue.CancellationsRetired

private theorem LiveStreamFrame.integrateStreamItem {queue : State}
    {work parents seen stream items} (frame : LiveStreamFrame queue work parents seen)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items) (fresh : item.occurrence ∉ seen)
    (available : List (Occurrence × Nat))
    : LiveStreamFrame (queue.integrateStreamItem item available) work parents
        (item.occurrence :: seen) := by
  have exactParents : ∀ group ∈ item.work.groups,
      group.parent = (parents group.node.ref).head? :=
    fun _ included => matching.streamItem_childGroups_parentCanonical canonical member included
  have descriptors : ∀ group ∈ item.work.groups,
      ∃ dependencies, GroupRecordAt work group.node dependencies :=
    fun _ included => matching.streamItem_childGroups_recordAt member included
  have registered := queue.integrateStreamItem_registration frame.registered frame.tasks
    matching member frame.context available
  have certificate := generated.declarations.sourceStreamItem matching member queue.registeredGroups
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have integratedRegistration := queue.maybeIntegrateWork_registration frame.registered frame.tasks
    item.work certificate.contributors
  have prunedRegistration := State.pruneEmptyGroups_registration integratedRegistration.1
    integratedRegistration.2.1 integrated.2.newGroups
  have prunedRefs := (frame.unique.maybeIntegrateWork item.work).pruneEmptyGroups
    integrated.2.newGroups
  have prunedFields := (frame.fields.maybeIntegrateWork item.work exactParents).pruneEmptyGroups
    integrated.2.newGroups
  have prunedComplete := (frame.complete.maybeIntegrateWork frame.unique frame.registered
    frame.closed item.work exactParents).pruneEmptyGroups integrated.2.newGroups
  have forest := State.RemovalForest.of_generated generated
    ((frame.children.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups)
    ((frame.links.maybeIntegrateWork item.work exactParents).pruneEmptyGroups
      integrated.2.newGroups)
    ((frame.records.maybeIntegrateWork item.work descriptors).pruneEmptyGroups
      integrated.2.newGroups) canonical
  exact ⟨frame.covered.integrateStreamItem frame.inventory generated frame.complete
      frame.unique frame.registered frame.tasks frame.closed frame.safe frame.fields
      frame.records frame.children frame.links canonical matching member fresh available,
    frame.inventory.integrateStreamItem matching member available,
    frame.complete.integrateStreamItem frame.unique frame.registered frame.closed item
      exactParents available,
    ((frame.unique.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available,
    registered.1, registered.2.1,
    frame.closed.integrateStreamItem frame.registered frame.tasks frame.context matching member
      canonical available,
    ((frame.safe.maybeIntegrateWork frame.registered frame.closed frame.fields item.work
      exactParents frame.cancelled generated descriptors canonical certificate.parents).pruneEmptyGroups _).startNewWork
      prunedRefs prunedFields prunedComplete forest _ available,
    ((frame.fields.maybeIntegrateWork item.work exactParents).pruneEmptyGroups _).startNewWork
      _ available,
    ((frame.records.maybeIntegrateWork item.work descriptors).pruneEmptyGroups _).startNewWork
      _ available,
    ((frame.children.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available,
    ((frame.links.maybeIntegrateWork item.work exactParents).pruneEmptyGroups _).startNewWork
      _ available,
    (frame.context.integrateStreamItem matching member available).1,
    ((frame.cancelled.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork
      prunedRegistration.1 _ available⟩

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
    (context : queue.RegistrationFrame work) (cancelled : queue.CancellationsRetired)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (distinct : (items.map StreamItem.occurrence).Nodup)
    (fresh : ∀ item ∈ items, item.occurrence ∉ seen)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.LiveContributorsCovered := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (current : State) (observed : List Occurrence)
      (frame : LiveStreamFrame current work parents observed)
      (nodup : (more.map StreamItem.occurrence).Nodup)
      (unseen : ∀ item ∈ more, item.occurrence ∉ observed)
      : ∃ finalSeen,
          LiveStreamFrame (current.preparedStreamItems more available) work parents finalSeen := by
    induction more generalizing current observed with
    | nil => exact ⟨observed, frame⟩
    | cons item rest ih =>
        have separated := List.nodup_cons.mp nodup
        rw [State.preparedStreamItems_cons current item rest available]
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (current.integrateStreamItem item available) (item.occurrence :: observed)
          (frame.integrateStreamItem generated canonical matching
            (included List.mem_cons_self) (unseen item List.mem_cons_self) available) separated.2
        intro next member seenBefore
        rcases List.mem_cons.mp seenBefore with same | old
        · exact separated.1 (same ▸ List.mem_map_of_mem member)
        · exact unseen next (List.mem_cons_of_mem _ member) old
  rw [queue.streamItems_eq stream items available]
  split
  · exact covered
  · obtain ⟨finalSeen, frame⟩ := loop items (List.Subset.refl _) queue seen
      ⟨covered, inventory, complete, unique, registered, tasks, closed, safe, fields,
        records, children, links, context, cancelled⟩ distinct fresh
    exact frame.covered.drainReadyGroups frame.unique
      (State.RemovalForest.of_generated generated frame.children frame.links frame.records
        canonical)
      available

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
