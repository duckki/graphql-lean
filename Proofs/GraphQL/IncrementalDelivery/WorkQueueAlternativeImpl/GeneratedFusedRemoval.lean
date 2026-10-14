import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerHandlers

/-! Independently construct the actual-removal frame on the original generated source
domain. This closes the local full-state projection leaf; handler and alternative replay
lifts still have to carry the same frame through their internal registration/release phases.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs)

/-- The reference source construction supplies actual live-node registration, complete
contributor links and owner existence. No cleanup target or projected endpoint is assumed.
-/
theorem
    _root_.GraphQL.IncrementalDelivery.ReferenceWorkQueue.State.TaskOwnerFrame.removalTaskFrame
    {queue : ReferenceWorkQueue.State} {work : Work} (frame : queue.TaskOwnerFrame work)
    : RemovalTaskFrame queue := by
  refine ⟨frame.registered, fun _ member => frame.disposition.startedLinks frame.registered member, ?_⟩
  intro node member
  obtain ⟨key, contributes, present⟩ := frame.owners node member
  obtain ⟨owner, ownerMember, ownerKey⟩ := List.mem_map.mp contributes
  obtain ⟨group, groupMember, groupKey⟩ := List.mem_map.mp present
  exact List.any_eq_true.mpr ⟨owner, ownerMember,
    List.any_eq_true.mpr ⟨group, groupMember, beq_iff_eq.mpr (groupKey.trans ownerKey.symm)⟩⟩

/-- Exact full-queue removal projection at every original valid started generated
reference prefix. The local record frame, matching, membership soundness and finite forest
are all derived; callers supply no additional bookkeeping or cleanup contract.
-/
def GeneratedReferenceRemovalProjection : Prop :=
  ∀ (work : Work) (batches : List (List GraphEvent)),
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work batches.flatten
    → ReferenceWorkQueue.inputsStarted work batches = true
    → ∀ (root : Nat) (targets : List CleanupTarget),
        let queue :=
          ((ReferenceWorkQueue.State.initialize
              (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
            batches).1
        (({ queue } : State).removeGroup root targets).1.queue = queue.removeGroup root

theorem GeneratedReferenceRemovalProjection_holds
    : GeneratedReferenceRemovalProjection := by
  intro work batches generated valid started root targets
  obtain ⟨parents, forest⟩ := generated.runNormalized_removalForest batches valid
  have frame := generated.runNormalized_taskOwnerFrame batches valid started
  exact FusedRemovalProjection_holds _ work parents root targets
    frame.matching frame.sound forest frame.removalTaskFrame

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
