import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PruningTaskProgress

/-! Exact decrement debt and live-owner retention through the accepting producer's
success fold. The proof reuses the reference's all-owner bound, including latent failed
owners; no node-value or native inventory assumptions are introduced.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Actual task-success registration reserves its exact contributor decrement debt
-----------------------------------------------------------------------------------------

/-- The original pending ledger constructs decrement debt at accepted registration.
Exact catalogue matching supplies the settling computation's owners, not a new source law.
-/
theorem taskSuccess_registrationDebt {queue : Kernel}
    {work settled occurrence result node}
    (accounted : queue.PendingAccounting work settled)
    (matching
      : (ReferenceWorkQueue.GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (found : queue.taskNode? occurrence = some node)
    (healthy : queue.taskHasHealthyOwner node.task = true) (fresh : occurrence ∉ settled)
    : (registrationSnapshot queue (.taskSuccess occurrence result)).PendingDebtBound
        (fun _ => True) (occurrence :: settled)
        (node.task.groups.map DeliveryNode.ref) := by
  let stored := queue.putTaskNode { node with value := some result.value }
  let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
  have storedCounts : stored.PendingBound (fun _ => True) settled := accounted.pending
  have storedMembers : stored.TaskMembershipsUnique := accounted.memberships
  have storedSound : stored.GroupMembershipSound := accounted.sound
  have storedMatch : stored.RegisteredTasksMatch work := accounted.matching
  have integratedLinks : integrated.UnsettledTaskLinks settled :=
    (accounted.links.putTaskNode _).maybeIntegrateWork accounted.refs accounted.taskGroups
      result.work (some occurrence)
  have integratedCounts : integrated.PendingBound (fun _ => True) settled :=
    storedCounts.maybeIntegrateWork result.work (some occurrence)
  have integratedMembers : integrated.TaskMembershipsUnique :=
    storedMembers.maybeIntegrateWork result.work (some occurrence)
  have integratedSound : integrated.GroupMembershipSound :=
    storedSound.maybeIntegrateWork result.work (some occurrence)
  have integratedMatch : integrated.RegisteredTasksMatch work :=
    storedMatch.maybeIntegrateWork result.work (by
      intro task member
      obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
      exact ⟨⟨address, payload, some occurrence, same, known⟩,
        matching.childTask_groupsExact member⟩) (some occurrence)
  have taskMember : node.task ∈ integrated.tasks := by
    rw [ReferenceWorkQueue.State.maybeIntegrateWork_tasks_append]
    exact List.mem_append_left _ (accounted.started node (List.mem_of_find?_eq_some found))
  have same := (ReferenceWorkQueue.State.taskNode?_some found).2
  have owned := integratedLinks.ownedExactlyBy integratedSound integratedMatch taskMember
    (same.symm ▸ fresh)
  rw [same] at owned
  have debt := integratedCounts.beginSettlement integratedMembers
    (fun candidate member _ => owned candidate member) fresh
  change (registrationCore (registrationSnapshot queue (.taskSuccess occurrence result))).PendingDebtBound
    (fun _ => True) (occurrence :: settled) (node.task.groups.map DeliveryNode.ref)
  simp only [registrationSnapshot, found, healthy, ↓reduceIte]
  rw [State.maybeIntegrateWork_registrationCore { queue := stored } result.work (some occurrence)]
  exact debt

-----------------------------------------------------------------------------------------
-- The original debt-aware success fold retains every fresh task owner
-----------------------------------------------------------------------------------------

/-- Decrementing the completed producer cannot publish an unsettled linked task or
silently prune one of its live owners. The original debt-aware fold supplies both the
retained memberships/owners and the all-owner pending bound for the following drain.
-/
theorem successGroupFold_unsettledOwners {queue : Kernel} {occurrence keys settled}
    (uniqueRefs : queue.GroupRefsUnique) (links : queue.TaskLinkedOn occurrence keys)
    (fresh : occurrence ∉ settled) (groups : List DeliveryNode)
    (unique : (groups.map DeliveryNode.ref).Nodup)
    (debt : queue.PendingDebtBound (fun _ => True) settled (groups.map DeliveryNode.ref))
    : let folded := groups.foldl ReferenceWorkQueue.successGroupStep (queue, [], {})
      folded.1.TaskLinkedOn occurrence keys
      ∧ (∀ key ∈ keys,
          key ∈ queue.groupNodes.map (fun node => node.group.node.ref)
          → key ∈ folded.1.groupNodes.map (fun node => node.group.node.ref))
      ∧ folded.1.PendingBound (fun _ => True) settled := by
  let invariant (current : Kernel) := current.GroupRefsUnique
    ∧ current.TaskLinkedOn occurrence keys
    ∧ ∀ key ∈ keys, key ∈ queue.groupNodes.map (fun node => node.group.node.ref)
      → key ∈ current.groupNodes.map (fun node => node.group.node.ref)
  have loop := ReferenceWorkQueue.successGroupFold_preservesBound (fun _ => True) settled invariant
    (fun _ prior => prior.1) (by intros; trivial)
    (by
      intro current node prior found
      refine ⟨prior.1.putGroupNode _, prior.2.1.putGroupNodeSameTasks prior.1 node
        (List.mem_of_find?_eq_some found) _ rfl rfl, ?_⟩
      intro key contributes present
      rw [ReferenceWorkQueue.State.putGroupNode_refs]
      exact prior.2.2 key contributes present)
    (by
      intro current node remaining prior bounded member active zero all
      have unlisted : occurrence ∉ node.tasks := fun listed => fresh (all occurrence listed)
      exact ⟨prior.1.finishGroupSuccess node, prior.2.1.finishOtherGroupSuccess node unlisted,
        fun key contributes present => finishGroupSuccess_linkedOwner_present prior.2.1 node member unlisted
          contributes (prior.2.2 key contributes present)⟩)
    groups unique (queue, [], {}) ⟨uniqueRefs, links, fun _ _ present => present⟩ debt
  exact ⟨loop.1.2.1, loop.1.2.2, loop.2⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
