import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActualNoticeCompletion

/-! Historical startup group notices stay tracked before their separate failure forwarding. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Synchronous cleanup either keeps an initially announced group active or marks it
cancelled. A forwarded report is not required at this initial computation cut.
-/
theorem State.initializeWithStartup_groupNoticeTracking (work : Execution.Work)
    (startup : InitialStartup)
    : GroupNoticeTracking
        ((State.initialize (Work.fromExecution work)).initialGroups.map
          Execution.DeliveryNode.ref)
        ((State.initialize (Work.fromExecution work) startup), []) := by
  intro ref member
  simp only [List.flatMap_nil, List.append_nil] at member
  have tracked := (initialPreparation work).1.startNewWork_tracks_roots
    (initialPreparation work).2 startup.failures ref (List.mem_append_right _ member)
  rw [State.initializeWithStartup_eq_preparation]
  exact tracked.imp_right Or.inl

/-- Every actual startup batch/FIFO cut tracks the complete historical initial inventory.
The source-handler ledger can omit forwarded initial reports because cancellation markers
already explain those refs until their actual output completions are observed.
-/
theorem State.startup_batchPrefix_groupNoticeTracking (work : Execution.Work)
    (startup : InitialStartup) (earlier : List (List GraphEvent)) (fifo : List GraphEvent)
    (available : List (Occurrence × Nat))
    : let initial := (State.initialize (Work.fromExecution work) startup)
      GroupNoticeTracking
        ((State.initialize (Work.fromExecution work)).initialGroups.map
          Execution.DeliveryNode.ref)
        (
          ((initial.replayBatches earlier).replayGraphEvents fifo available),
          (initial.rawBatches earlier).2
          ++ ((initial.replayBatches earlier).rawEventReplay fifo available).2
        ) := by
  let initial := (State.initialize (Work.fromExecution work) startup)
  have earlierCancelled := initial.rawBatches_cancelledGroups_subset earlier
  rw [State.rawBatches_state] at earlierCancelled
  exact (State.initializeWithStartup_groupNoticeTracking work startup).append
    (initial.batchPrefix_groupNoticeTracking earlier fifo available)
    (earlierCancelled.trans (State.replayGraphEvents_cancelledGroups_subset _ fifo available))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
