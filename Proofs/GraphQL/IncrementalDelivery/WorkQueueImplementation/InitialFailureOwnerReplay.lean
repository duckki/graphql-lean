import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupOwnerAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplayClosure

/-! Actual owner replay retains failures available before the first host notification. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A batch advances consumed notifications while retaining the initial failure inventory.
Retirement and exposed regions derive registration availability inside the FIFO induction.
-/
theorem ClosedOwnerAccounting.handleGraphEvents_withInitialFailures
    {queue work parents before initialFailed}
    (prior
      : ClosedOwnerAccounting queue work parents before
          (initialFailed ++ GraphEvent.failureSettlements before))
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : ClosedOwnerAccounting (queue.handleGraphEvents events).1 work parents
        (before ++ events)
        (initialFailed ++ GraphEvent.failureSettlements (before ++ events)) := by
  have included : (initialFailed ++ GraphEvent.failureSettlements before).Subset
      (initialFailed ++ GraphEvent.failureSettlements (before ++ events)) := by
    intro occurrence member
    rcases List.mem_append.mp member with initial | consumed
    · exact List.mem_append_left _ initial
    · apply List.mem_append_right
      rw [GraphEvent.failureSettlements_append_list]
      exact List.mem_append_right _ consumed
  have recorded : ∀ occurrence errors,
      (occurrence, errors) ∈ GraphEvent.availableFailures events →
        occurrence ∈ initialFailed ++ GraphEvent.failureSettlements (before ++ events) := by
    intro occurrence errors member
    obtain ⟨event, inEvents, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    apply List.mem_append_right
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨.taskFailure _ _, List.mem_append_right before inEvents,
      List.mem_cons_self⟩
  have result := (prior.weakenFailures included).replayGraphEvents canonical generated events valid
    accepted recorded (by
      intro occurrence errors member
      exact List.mem_filterMap.mpr ⟨.taskFailure occurrence errors, member, rfl⟩)
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact result.withTerminated terminal

/-- The initial inventory persists across actual host batches without flattening state. -/
theorem ClosedOwnerAccounting.runNormalized_withInitialFailures
    {queue work parents before initialFailed}
    (prior
      : ClosedOwnerAccounting queue work parents before
          (initialFailed ++ GraphEvent.failureSettlements before))
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : ClosedOwnerAccounting (queue.runNormalized batches).1 work parents
        (before ++ batches.flatten)
        (initialFailed ++ GraphEvent.failureSettlements (before ++ batches.flatten)) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil => simpa [State.replayBatches] using prior
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := prior.handleGraphEvents_withInitialFailures canonical generated batch
        (valid.prefix earlier) running accepted
      have result := ih next (by simpa [List.append_assoc] using valid) restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using result

/-- Startup constructs the joint retirement/owner frame without consumed notifications. -/
theorem ExecutedWork.initialStartup_closedOwnerAccounting {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      ClosedOwnerAccounting initial work parents []
        (startup.reportingOccurrences work refs) := by
  have roots := generated.initialStartup_rootReplayFrame canonical startup
  exact ⟨generated.initialStartup_ownerAccounting canonical startup,
    roots.live.registered, roots.live.roots, roots.retired,
    State.initializeWithStartup_regionInventory work startup⟩

/-- Every complete batch prefix of startup replay retains the joint accounting frame. -/
theorem ExecutedWork.startup_runNormalized_ownerAccounting {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      ClosedOwnerAccounting (initial.runNormalized batches).1 work parents
        batches.flatten
        (startup.reportingOccurrences work refs
          ++ GraphEvent.failureSettlements batches.flatten) := by
  let initial := State.initialize (Work.fromExecution work) startup
  have frame := generated.initialStartup_closedOwnerAccounting canonical startup
  have prior : ClosedOwnerAccounting initial work parents []
      (startup.reportingOccurrences work
        ((initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref)
        ++ GraphEvent.failureSettlements []) := by
    simpa only [GraphEvent.failureSettlements, List.flatMap_nil, List.reverse_nil,
      List.append_nil]
      using frame
  have result := prior.runNormalized_withInitialFailures canonical generated batches valid
    (by rwa [inputsStartedWithStartup_eq_batchesStarted] at started)
  dsimp only
  rw [State.runNormalized_replayBatches]
  rw [State.runNormalized_replayBatches] at result
  exact result

/-- Actual FIFO cuts retain initial availability and the current batch's entire snapshot.
The consumed prefix still contains only notifications already dispatched at this cut.
-/
theorem ExecutedWork.startup_ownerAccounting_atBatchPrefix {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup) (earlier : List (List GraphEvent))
    (batch : List GraphEvent) (later : List (List GraphEvent)) (fifo : List GraphEvent)
    (valid : ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : inputsStarted work (earlier ++ batch :: later) startup = true)
    (prefixOfBatch : fifo.IsPrefix batch)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      let current :=
        (initial.replayBatches earlier).replayGraphEvents fifo
          (GraphEvent.availableFailures batch)
      ClosedOwnerAccounting current work parents (earlier.flatten ++ fifo)
        (startup.reportingOccurrences work refs
          ++ GraphEvent.failureSettlements (earlier.flatten ++ batch)) := by
  let initial := State.initialize (Work.fromExecution work) startup
  let failed := startup.reportingOccurrences work
    ((initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref)
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rwa [← inputsStartedWithStartup_eq_batchesStarted]
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  have validEarlier : ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [List.flatten_append]⟩
  have before := generated.startup_runNormalized_ownerAccounting canonical startup earlier
    validEarlier (by rw [inputsStartedWithStartup_eq_batchesStarted]; exact checked.1)
  dsimp only at before
  rw [State.runNormalized_replayBatches] at before
  obtain ⟨_, accepted, _⟩ :=
    (initial.replayBatches earlier).batchesStarted_cons batch later checked.2
  obtain ⟨tail, same⟩ := prefixOfBatch
  have fifoAccepted : State.acceptsBatch.go (fun _ => false)
      (GraphEvent.availableFailures batch) (initial.replayBatches earlier) fifo = true := by
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [State.acceptsBatch, same] using accepted
  have validFifo : ValidGraphEvents work (earlier.flatten ++ fifo) := by
    apply valid.prefix
    exact ⟨tail ++ later.flatten, by simp [← same, List.append_assoc]⟩
  have included : (failed ++ GraphEvent.failureSettlements earlier.flatten).Subset
      (failed ++ GraphEvent.failureSettlements (earlier.flatten ++ batch)) := by
    intro occurrence member
    rcases List.mem_append.mp member with initial | consumed
    · exact List.mem_append_left _ initial
    · apply List.mem_append_right
      rw [GraphEvent.failureSettlements_append_list]
      exact List.mem_append_right _ consumed
  have recorded : ∀ occurrence errors, (occurrence, errors) ∈ GraphEvent.availableFailures batch
      → occurrence ∈ failed ++ GraphEvent.failureSettlements (earlier.flatten ++ batch) := by
    intro occurrence errors member
    obtain ⟨event, inBatch, outcome⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at outcome
    obtain ⟨rfl, rfl⟩ := outcome
    apply List.mem_append_right
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨.taskFailure _ _, List.mem_append_right _ inBatch,
      List.mem_cons_self⟩
  exact (before.weakenFailures included).replayGraphEvents canonical generated fifo
    validFifo fifoAccepted recorded
    (by
      intro occurrence errors member
      exact List.mem_filterMap.mpr
        ⟨
          .taskFailure occurrence errors,
          (by rw [← same]; exact List.mem_append_left _ member),
          rfl
        ⟩)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
