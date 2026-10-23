import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedPreparationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupMembershipOrder

/-! One publication inventory and cancellation-aware owner frame through item preparation. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics

private structure PreparationFrame (queue : State) (work : Execution.Work)
    (property : Occurrence → Execution.ExecutionGroupValue → Prop)
    (published : List ObjectPublication)
    : Prop where
  refs : queue.GroupRefsUnique
  live : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  started : queue.StartedTasksRegistered
  links : queue.StoredTaskLinks
  settled : queue.ChildStreamsSettled
  children : queue.ChildStreamsMatchWork work
  inventory : queue.PublicationInventory property published
  memberships : queue.GroupMembershipOrder
  cancelled : queue.CancellationsRetired

/-- Item preparation retains its ledger and every uncancelled buffered owner. Failed
startup may remove buffers; the returned owner certificate records precisely that case.
The supplied snapshot excludes every successful stored value by source provenance.
-/
theorem State.PublicationInventory.preparedStreamItems_ledger {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (refs : queue.GroupRefsUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (started : queue.StartedTasksRegistered)
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work)
    (memberships : queue.GroupMembershipOrder) (cancelled : queue.CancellationsRetired)
    (items : List StreamItem)
    (allCovered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = ref)
    (available : List (Occurrence × Nat) := [])
    (clean
      : ∀ occurrence value,
          property occurrence value → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence value allowed errors impossible; cases impossible)
    : let prepared := queue.preparedStreamItems items available
      prepared.PublicationInventory property published
      ∧ prepared.StoredTaskLinks
      ∧ prepared.ChildStreamsSettled
      ∧ prepared.ChildStreamsMatchWork work
      ∧ prepared.GroupMembershipOrder
      ∧ prepared.CancellationsRetired
      ∧ prepared.LiveGroupsRegistered
      ∧ prepared.TaskGroupsRegistered
      ∧ queue.StoredOwnersConserved [] prepared := by
  let invariant (current : State) := PreparationFrame current work property published
    ∧ queue.StoredOwnersConserved [] current
  have initial : invariant queue :=
    ⟨⟨refs, live, tasks, started, links, settled, children, inventory, memberships, cancelled⟩,
      .refl queue⟩
  have prepared : invariant (queue.preparedStreamItems items available) := by
    apply State.preparedStreamItems_preserves invariant initial items available
    intro current item member prior
    obtain ⟨frame, owners⟩ := prior
    let integrated := current.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    let released : NewWork := { integrated.2 with newGroups := pruned.2 }
    have integratedRegistry := current.maybeIntegrateWork_registration frame.live frame.tasks
      item.work (by
        intro task taskMember ref contributor
        exact Or.inr (allCovered item member task taskMember ref contributor))
    have prunedRegistry := integrated.1.pruneEmptyGroups_registration integratedRegistry.1
      integratedRegistry.2.1 integrated.2.newGroups
    have nextRegistry := State.startNewWork_registration prunedRegistry.1 prunedRegistry.2.1
      released available
    have integratedLinks := frame.links.maybeIntegrateWork frame.refs frame.tasks frame.started
      item.work
    have prunedLinks := integratedLinks.pruneEmptyGroups integrated.2.newGroups
    have prunedInventory : pruned.1.PublicationInventory property published :=
      ⟨frame.inventory.unique, frame.inventory.provenance,
        (frame.inventory.stored.maybeIntegrateWork item.work).pruneEmptyGroups _⟩
    have prunedClean : pruned.1.StoredValuesSatisfy
        (fun occurrence _ => ∀ errors, (occurrence, errors) ∉ available) := by
      intro node included value stored
      exact clean _ _ (prunedInventory.stored node included value stored).1
    have first : current.StoredOwnersConserved [] pruned.1 := by
      simpa only [List.nil_append]
        using (current.maybeIntegrateWork_storedOwnersConserved item.work).append
          (State.pruneEmptyGroups_storedOwnersConserved integratedLinks
            integrated.2.newGroups)
          (by rw [State.pruneEmptyGroups_cancelledGroups]; exact List.Subset.refl _)
    have activation := pruned.1.startNewWork_storedOwnersConserved released available prunedClean
    have itemOwners : current.StoredOwnersConserved []
        (current.integrateStreamItem item available) := by
      simpa only [State.integrateStreamItem, integrated, pruned, released,
        List.nil_append]
        using first.append activation
          (State.startNewWork_cancelledGroups_subset pruned.1 released available)
    have retainedCancellations : current.cancelledGroups.Subset
        (current.integrateStreamItem item available).cancelledGroups := by
      have middle : current.cancelledGroups.Subset pruned.1.cancelledGroups := by
        dsimp only [pruned, integrated]
        rw [State.pruneEmptyGroups_cancelledGroups, State.maybeIntegrateWork_cancelledGroups]
        exact current.addGroups_cancelledGroups_subset item.work.groups
      exact middle.trans (State.startNewWork_cancelledGroups_subset pruned.1 released available)
    have next : PreparationFrame (current.integrateStreamItem item available) work property
        published := by
      exact ⟨((frame.refs.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
          available,
        nextRegistry.1, nextRegistry.2,
        ((frame.started.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available,
        prunedLinks.startNewWork _ available,
        ((frame.settled.integrateRoots item.work).pruneEmptyGroups _).startNewWork _ available,
        ((frame.children.integrateRoots item.work).pruneEmptyGroups _).startNewWork _ available,
        ⟨prunedInventory.unique, prunedInventory.provenance,
          prunedInventory.stored.startNewWork _ available⟩,
        ((frame.memberships.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
          available,
        ((frame.cancelled.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork
          prunedRegistry.1 released available⟩
    exact ⟨
      next,
      by simpa only [List.nil_append] using owners.append itemOwners retainedCancellations
    ⟩
  exact ⟨
    prepared.1.inventory,
    prepared.1.links,
    prepared.1.settled,
    prepared.1.children,
    prepared.1.memberships,
    prepared.1.cancelled,
    prepared.1.live,
    prepared.1.tasks,
    prepared.2
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
