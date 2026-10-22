import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchedNoticeHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupSourceFrames

/-! Historical startup announcements retain permanent registration and ancestor protection. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial announcements include groups already removed by synchronous activation.
Their registration and retired ancestors protect those historical refs from reannouncement.
-/
theorem ExecutedWork.initialStartup_noticeHistory {work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    : NoticeHistoryFrame (State.initialize (Work.fromExecution work) startup)
        work
        ((State.initialize (Work.fromExecution work)).initialGroups.map
          Execution.DeliveryNode.ref) := by
  refine ⟨generated.initialGroups_unique, ?_, ?_⟩
  · intro ref member
    obtain ⟨group, included, same⟩ := List.mem_map.mp member
    have present := (initialPreparation_frontier (work := work)).2.1 group included
    obtain ⟨record, stored, identity⟩ := List.mem_map.mp present
    have registered := (initialPreparation_pendingAccounting work generated.declarations).liveGroups record stored
    rw [State.initializeWithStartup_eq_preparation]
    dsimp only [State.enqueueGroupFailures]
    rw [State.startNewWork_registeredGroups]
    exact same ▸ identity ▸ registered
  · intro ref member
    obtain ⟨group, included, same⟩ := List.mem_map.mp member
    have retired := (generated.initialPreparation_retirement.1 group included).mono
      (fun _ retired => retired.startNewWork (initialPreparation work).2 startup.failures)
    rw [State.initializeWithStartup_eq_preparation]
    exact same ▸ retired

/-- Initial and actual startup raw group notices form one duplicate-free inventory.
Notification-only forwarding adds no notice refs; the source proof uses the real startup
state and each host batch's rejection snapshot rather than ordinary initialization.
-/
theorem ExecutedWork.startup_rawBatches_groupRefs_nodup {work inputs}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      ((State.initialize (Work.fromExecution work)).initialGroups.map
          Execution.DeliveryNode.ref
        ++ (initial.rawBatches inputs).2.flatMap rawGroupNoticeRefs).Nodup := by
  let initial := State.initialize (Work.fromExecution work) startup
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have source := generated.initialStartup_uncancelledReplayFrame canonical startup matched
  have history := generated.initialStartup_noticeHistory startup
  have unique := (history.rawBatches source generated canonical inputs valid
    (by rwa [← inputsStartedWithStartup_eq_batchesStarted])).unique
  exact unique

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
