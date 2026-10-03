import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamConservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamInventoryReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredLinkPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationMonotonicity

/-! Concrete owner folds and recursive draining cannot strand buffered child streams. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- The bounded mixed drain retains the same buffered producer or emits its child notice
-----------------------------------------------------------------------------------------

/-- Every bounded drain releases or retains each buffered stream with an uncancelled owner.
Witness: complete successful flushes emit the child notice; activation keeps old lookups;
failed cleanup records removed owners. Sequential composition follows the actual budget.
-/
theorem State.drainReadyGroups_go_bufferedStreamsConserved {queue : State}
    (links : queue.StoredTaskLinks) (inventory : queue.ChildStreamInventory) (fuel : Nat)
    : queue.BufferedStreamsConserved (State.drainReadyGroups.go fuel queue).2
        (State.drainReadyGroups.go fuel queue).1 := by
  induction fuel generalizing queue with
  | zero => exact .refl queue
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact .refl queue
      · rename_i group selected
        have live : group ∈ queue.groupNodes := by
          obtain ⟨ref, _, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : queue.groupNode? ref with
          | none => simp [found] at choice
          | some node =>
              simp only [found] at choice
              change (if node.failure.isSome || node.pending == 0 then some node else none)
                = some group at choice
              split at choice
              · cases Option.some.inj choice
                exact List.mem_of_find?_eq_some found
              · contradiction
        cases cached : group.failure with
        | none =>
            dsimp only
            have flushed := State.finishGroupSuccess_bufferedStreamsConserved
              links inventory group live
            have active := State.BufferedStreamsConserved.of_emptyOwners
              ((queue.finishGroupSuccess group).1.startNewWork_storedOwnersConserved
                (queue.finishGroupSuccess group).2.2) []
            have first := flushed.append active (by
              rw [State.startNewWork_cancelledGroups]
              exact List.Subset.refl _)
            simp only [List.append_nil] at first
            exact first.append
              (ih ((links.finishGroupSuccess group).startNewWork _)
                ((inventory.finishGroupSuccess group).startNewWork _))
              (State.drainReadyGroups_go_cancelledGroups_subset _ _)
        | some errors =>
            exact (State.BufferedStreamsConserved.of_emptyOwners
              (queue.removeGroup_storedOwnersConserved group.group.node.ref)
              [.groupFailure group.group.node errors]).append
              (ih (links.removeGroup _) (inventory.removeGroup _))
              (State.drainReadyGroups_go_cancelledGroups_subset _ _)

/-- The implementation's full drain has buffered-stream conservation.
Witness: specialize the bounded theorem to the live group-node budget.
-/
theorem State.drainReadyGroups_bufferedStreamsConserved {queue : State}
    (links : queue.StoredTaskLinks) (inventory : queue.ChildStreamInventory)
    : queue.BufferedStreamsConserved queue.drainReadyGroups.2 queue.drainReadyGroups.1 :=
  State.drainReadyGroups_go_bufferedStreamsConserved links inventory
    queue.groupNodes.length

-----------------------------------------------------------------------------------------
-- The single-pass owner fold retains earlier streams while emitting new release carriers
-----------------------------------------------------------------------------------------

/-- The complete successful-owner fold releases or retains every earlier buffered stream.
Witness: counter updates keep old nodes; each actual flush has complete child selection.
Unique group refs preserve stored memberships throughout the fold's original order.
-/
theorem State.successGroupFold_bufferedStreamsConserved {queue : State}
    (refs : queue.GroupRefsUnique) (links : queue.StoredTaskLinks)
    (inventory : queue.ChildStreamInventory) (groups : List Execution.DeliveryNode)
    : let result := groups.foldl successGroupStep (queue, [], {})
      queue.BufferedStreamsConserved result.2.1 result.1 := by
  have loop (remaining : List Execution.DeliveryNode)
      (current : State) (events : List WorkQueueEvent) (released : NewWork)
      (refs : current.GroupRefsUnique) (links : current.StoredTaskLinks)
      (inventory : current.ChildStreamInventory)
      (prior : queue.BufferedStreamsConserved events current)
      : let result := remaining.foldl successGroupStep (current, events, released)
        queue.BufferedStreamsConserved result.2.1 result.1 := by
    induction remaining generalizing current events released with
    | nil => exact prior
    | cons group rest ih =>
        simp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ _ _ refs links inventory prior
        · rename_i node found
          let updated := { node with pending := node.pending - 1 }
          have live := List.mem_of_find?_eq_some found
          have nextLinks := links.putGroupNodeSameTasks refs node live updated rfl rfl
          have nextInventory := inventory.putGroupNode updated
          have nextRefs := refs.putGroupNode updated
          have conserved := State.BufferedStreamsConserved.of_emptyOwners
            (current.putGroupNode_storedOwnersConserved updated) []
          have next := prior.append conserved (List.Subset.refl _)
          simp only [List.append_nil] at next
          split
          · have updatedLive : updated ∈ (current.putGroupNode updated).groupNodes := by
              exact List.mem_map.mpr ⟨node, live, by simp [updated]⟩
            exact ih _ _ _ (nextRefs.finishGroupSuccess _)
              (nextLinks.finishGroupSuccess _) (nextInventory.finishGroupSuccess _)
              (next.append (State.finishGroupSuccess_bufferedStreamsConserved
                nextLinks nextInventory updated updatedLive)
                (by rw [State.finishGroupSuccess_cancelledGroups]; exact List.Subset.refl _))
          · exact ih _ _ _ nextRefs nextLinks nextInventory next
  exact loop groups queue [] {} refs links inventory (.refl queue)

/-- The owner fold retains unique, registered links on every surviving task node.
Witness: counter updates preserve links and successful flushes only remove whole nodes.
-/
theorem State.ChildStreamInventory.successGroupFold {queue : State}
    (inventory : queue.ChildStreamInventory) (groups : List Execution.DeliveryNode)
    (events : List WorkQueueEvent) (released : NewWork)
    : (groups.foldl successGroupStep
        (queue, events, released)).1.ChildStreamInventory := by
  induction groups generalizing queue events released with
  | nil => exact inventory
  | cons group rest ih =>
      simp only [List.foldl_cons, successGroupStep]
      split
      · exact ih inventory _ _
      · split
        · exact ih ((inventory.putGroupNode _).finishGroupSuccess _) _ _
        · exact ih (inventory.putGroupNode _) _ _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
