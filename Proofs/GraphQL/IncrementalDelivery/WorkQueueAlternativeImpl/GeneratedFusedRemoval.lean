import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedStartupProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerHandlers

/-! Independently construct the actual-removal frame on the original generated source
domain. This closes the local full-state projection leaf; handler and alternative replay
lifts still have to carry the same frame through their internal registration/release phases.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs)

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
