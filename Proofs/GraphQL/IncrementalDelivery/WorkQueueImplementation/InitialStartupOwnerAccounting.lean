import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupCancellation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplay

/-! Initial synchronous activation establishes the healthy-owner replay ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial activation balances every surviving group's counter, including cached failures. -/
theorem State.initializeWithStartup_initialCounts (work : Work) (startup : InitialStartup)
    : (State.initialize work startup).InitialCounts := by
  have empty : ({} : State).InitialCounts := by intro node member; cases member
  unfold State.initialize
  exact ((empty.maybeIntegrateWork work).pruneEmptyGroups _).startNewWork _
    startup.failures

/-- Each retained initial rejection is supported by an initially announced task cause. -/
theorem State.initializeWithStartup_cached_supported (work : Execution.Work)
    (startup : InitialStartup)
    : let initialized := State.initialize (Work.fromExecution work) startup
      let initial :=
        (initialized.initialGroups ++ initialized.initialStreams).map
          Execution.DeliveryNode.ref
      initialized.CachedFailuresSupported work
        (startup.reportingOccurrences work initial) := by
  let initialized := State.initialize (Work.fromExecution work) startup
  have facts := State.initializeWithStartup_announcementFacts work startup
  have rejected := State.initializeWithStartup_taskRejections (Work.fromExecution work) startup
    (fun occurrence errors => (occurrence, errors) ∈ startup.failures) (fun _ _ member => member)
  dsimp only
  intro node member errors rejection group contributes
  obtain ⟨owner, owns, announced⟩ := facts.known node member
  obtain ⟨address, payload, producer, shape, task⟩ :=
    (facts.matching node.task (facts.registered node member)).1
  have recorded : node.task.occurrence ∈ startup.reportingOccurrences work
      ((initialized.initialGroups ++ initialized.initialStreams).map
        Execution.DeliveryNode.ref) := by
    apply InitialStartup.mem_reportingOccurrences.mpr
    refine ⟨List.mem_map_of_mem (rejected node member errors rejection),
      node.task.groups.map Execution.DeliveryNode.ref, ⟨producer, payload, task⟩,
      owner.ref, List.mem_map_of_mem owns, ?_⟩
    rw [List.map_append]
    exact List.mem_append_left _ announced
  exact ⟨node.task.occurrence, recorded, node.task.groups.map Execution.DeliveryNode.ref,
    ⟨producer, payload, task⟩, List.mem_map_of_mem contributes⟩

/-- Initial healthy contributors retain their exact unsettled owner memberships. -/
theorem ExecutedWork.initialStartup_healthyOwners {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup)
    : let initialized := State.initialize (Work.fromExecution work) startup
      let initial :=
        (initialized.initialGroups ++ initialized.initialStreams).map
          Execution.DeliveryNode.ref
      initialized.HealthyRegisteredTaskAccounting work []
        (startup.reportingOccurrences work initial) := by
  have owners := State.initializeWithStartup_uncancelledTaskAccounting work generated startup
  have cancelled := State.initializeWithStartup_cancelled_supported generated canonical startup
  have tasks := State.initializeWithStartup_taskOwnerFrame work startup
  dsimp only
  intro task member fresh ref contributes healthy
  obtain ⟨dependencies, node, producer, known, same⟩ :=
    (tasks.matching task member).contributorKnown contributes
  have uncancelled := cancelled.contributor_healthy_not_mem generated known (by rwa [same])
  rw [same] at uncancelled
  exact owners task member fresh ref contributes uncancelled

/-- Cached failures, counters, canonical records and healthy owners share one initial ledger.
The available failure coordinate includes synchronous observations, while consumed source
history remains empty. No output explanation or terminal accounting is assumed.
-/
theorem ExecutedWork.initialStartup_ownerAccounting {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup)
    : let initialized := State.initialize (Work.fromExecution work) startup
      let initial :=
        (initialized.initialGroups ++ initialized.initialStreams).map
          Execution.DeliveryNode.ref
      initialized.OwnerAccountingInInventory work parents []
        (startup.reportingOccurrences work initial) := by
  have parent := generated.initialStartup_parentCutFrame canonical startup
  have counts := State.initializeWithStartup_initialCounts (Work.fromExecution work) startup
  have healthy : let initialized := State.initialize (Work.fromExecution work) startup
      let initial := (initialized.initialGroups ++ initialized.initialStreams).map
        Execution.DeliveryNode.ref
      initialized.HealthyPendingTracks work [] (startup.reportingOccurrences work initial) := by
    dsimp only
    intro node member _
    classical
    simp only [GroupNode.PendingTracks, unsettledCount, List.not_mem_nil]
    rw [List.filter_eq_self.mpr (by simp)]
    exact counts node member
  exact ⟨
    ⟨
      State.initializeWithStartup_pendingAccounting work generated.declarations startup,
      healthy,
      State.initializeWithStartup_cached_supported work startup,
      parent.records,
      parent.fields,
      State.initializeWithStartup_cancelled_supported generated canonical startup,
      parent.links,
      (State.initializeWithStartup_producerOrder work startup).1,
      (State.initializeWithStartup_producerOrder work startup).2
    ⟩,
    generated.initialStartup_healthyOwners canonical startup,
    parent.links
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
