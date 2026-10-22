import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionWitness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SnapshotMembershipBoundaries

/-! Exact actual FIFO cuts share producer readiness, registration and membership exclusion. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The same publication ledger supplies all task certificates at an actual source cut. -/
theorem startup_batchPublicationCut {work inputs published} (startup : InitialStartup)
    (batches
      : ((State.initialize (Work.fromExecution work) startup)).BatchClosuresCovered
          inputs published)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent)
    (inputEq : inputs = earlier ++ batch :: later) (prefixPart : fifo.IsPrefix batch)
    : let boundary :=
        ((State.initialize (Work.fromExecution work) startup)).replayBatches earlier
      let available := GraphEvent.availableFailures batch
      let current := boundary.replayGraphEvents fifo available
      let offset :=
        ((((State.initialize (Work.fromExecution work) startup)).rawBatches
            earlier).2.flatMap
          WorkQueueEvent.objectValues).length
      let count :=
        ((boundary.rawEventReplay fifo available).2.flatMap
          WorkQueueEvent.objectValues).length
      TaskProducersSucceeded work current.tasks (earlier.flatten ++ fifo)
      ∧ ProducerOrder work (current.tasks.map Task.occurrence)
      ∧ ∀ publication ∈ published.take (offset + count),
          current.TaskMembershipAbsent publication.1
          ∧ publication.1 ∈ current.tasks.map Task.occurrence := by
  let initial := (State.initialize (Work.fromExecution work) startup)
  have ready := State.initializeWithStartup_producerOrder work startup
  obtain ⟨suffix, batchEq⟩ := prefixPart
  let current := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let offset := ((initial.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
  let count := ((current.handleGraphEvents batch).2.flatMap WorkQueueEvent.objectValues).length
  let localCount := ((current.rawEventReplay fifo available).2.flatMap
    WorkQueueEvent.objectValues).length
  have batchStarts : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rw [← inputEq, ← inputsStartedWithStartup_eq_batchesStarted]
    exact started
  rw [State.batchesStarted_append] at batchStarts
  have parts := Bool.and_eq_true_iff.mp batchStarts
  have running := (current.batchesStarted_cons batch later parts.2).1
  have priorValid : ValidGraphEvents work earlier.flatten := valid.prefix
    ⟨(batch :: later).flatten, by simp [inputEq]⟩
  have localValid : ValidGraphEvents work (earlier.flatten ++ fifo) := valid.prefix
    ⟨suffix ++ later.flatten, by simp [inputEq, ← batchEq, List.append_assoc]⟩
  have priorLedger := State.BatchClosuresCovered.prefix earlier (batch :: later)
    (inputEq ▸ batches)
  have atBatch := State.BatchClosuresCovered.atBatch earlier batch later (inputEq ▸ batches)
  have priorOrder := initial.rawBatches_producerOrder ready.1 ready.2 earlier
    (by simpa only [List.nil_append] using priorValid) parts.1
  simp only [State.rawBatches_state, List.nil_append] at priorOrder
  have prefixCovered := State.ReplayClosuresCovered.prefix fifo suffix
    (show current.ReplayClosuresCovered (fifo ++ suffix)
      ((published.drop offset).take count) available from by
        rw [batchEq]
        exact atBatch.1)
  have localLe : localCount ≤ count := by
    have same := congrArg (fun events => current.rawEventReplay events available) batchEq.symm
    have append := current.rawEventReplay_append fifo suffix available
    have lengths := congrArg (fun result : State × List WorkQueueEvent =>
      (result.2.flatMap WorkQueueEvent.objectValues).length) (same.trans append)
    have batchValues := congrArg List.length (current.handleGraphEvents_objectValues batch running)
    dsimp only [localCount, count, available]
    simp only [List.flatMap_append, List.length_append] at lengths
    dsimp only [available] at lengths
    omega
  have atFifo := current.replayGraphEvents_producerOrder priorOrder.1 priorOrder.2 fifo
    localValid available
  refine ⟨atFifo.1, atFifo.2, ?_⟩
  intro publication member
  change publication ∈ published.take (offset + localCount) at member
  rw [List.take_add] at member
  rcases List.mem_append.mp member with prior | fresh
  · have absent := priorLedger.membershipsAbsent ready.1 ready.2
      (by simpa only [List.nil_append] using priorValid) parts.1 publication prior
    have registered := priorLedger.registered publication prior
    rw [State.rawBatches_state] at absent registered
    refine ⟨absent.replayGraphEvents_registered registered priorOrder.1 priorOrder.2 fifo
      localValid available, ?_⟩
    obtain ⟨task, member, same⟩ := List.mem_map.mp registered
    exact List.mem_map.mpr
      ⟨task, current.replayGraphEvents_tasks_subset fifo available member, same⟩
  · have inSlice : publication ∈ ((published.drop offset).take count).take localCount := by
      rw [List.take_take, Nat.min_eq_left localLe]
      exact fresh
    exact ⟨prefixCovered.membershipsAbsent priorOrder.1 priorOrder.2 localValid
      publication inSlice, prefixCovered.registered publication inSlice⟩

/-- The exact next handler receives the original ledger suffix at its actual object offset. -/
theorem startup_batchHandlerPublicationCut
    {work inputs published earlier batch later fifo event tail}
    (startup : InitialStartup)
    (batches
      : ((State.initialize (Work.fromExecution work) startup)).BatchClosuresCovered
          inputs published)
    (started : inputsStarted work inputs startup = true)
    (inputEq : inputs = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ event :: tail)
    : let boundary :=
        ((State.initialize (Work.fromExecution work) startup)).replayBatches earlier
      let available := GraphEvent.availableFailures batch
      let offset :=
        ((((State.initialize (Work.fromExecution work) startup)).rawBatches
            earlier).2.flatMap
          WorkQueueEvent.objectValues).length
      let count :=
        ((boundary.rawEventReplay fifo available).2.flatMap
          WorkQueueEvent.objectValues).length
      (boundary.replayGraphEvents fifo available).ReplayClosuresCovered [event]
        (published.drop (offset + count)) available := by
  let initial := (State.initialize (Work.fromExecution work) startup)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let offset := ((initial.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
  have starts : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rwa [← inputEq, ← inputsStartedWithStartup_eq_batchesStarted]
  rw [State.batchesStarted_append, Bool.and_eq_true] at starts
  have running := (boundary.batchesStarted_cons batch later starts.2).1
  have atBatch := (State.BatchClosuresCovered.atBatch earlier batch later (inputEq ▸ batches)).1
  have values := congrArg List.length (boundary.handleGraphEvents_objectValues batch running)
  have complete : boundary.ReplayClosuresCovered batch (published.drop offset) available := by
    apply (boundary.replayClosuresCovered_take_iff batch (published.drop offset) available).mp
    change boundary.ReplayClosuresCovered batch
      ((published.drop offset).take
        ((boundary.handleGraphEvents batch).2.flatMap WorkQueueEvent.objectValues).length)
      available at atBatch
    rwa [values] at atBatch
  have atFifo := State.ReplayClosuresCovered.afterPrefix fifo (event :: tail)
    (show boundary.ReplayClosuresCovered (fifo ++ event :: tail) (published.drop offset)
      available from batchEq ▸ complete)
  simpa only [List.drop_drop] using State.ReplayClosuresCovered.prefix [event] tail atFifo

/-- Actual batch/FIFO evidence derives the handler's full common-ledger membership cut. -/
theorem startup_batchHandlerMembershipCut
    {work inputs published earlier batch later fifo event tail}
    (startup : InitialStartup)
    (batches
      : ((State.initialize (Work.fromExecution work) startup)).BatchClosuresCovered
          inputs published)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (inputEq : inputs = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ event :: tail)
    : let boundary :=
        ((State.initialize (Work.fromExecution work) startup)).replayBatches earlier
      let available := GraphEvent.availableFailures batch
      let current := boundary.replayGraphEvents fifo available
      let prior :=
        (((State.initialize (Work.fromExecution work) startup)).rawBatches earlier).2
        ++ (boundary.rawEventReplay fifo available).2
      HandlerMembershipCut current event published prior available := by
  let boundary := ((State.initialize (Work.fromExecution work)
    startup)).replayBatches earlier
  let available := GraphEvent.availableFailures batch
  have frame := startup_batchPublicationCut startup batches valid started earlier batch later
    fifo inputEq
    ⟨event :: tail, batchEq.symm⟩
  have prefixValid := valid.prefix (show (earlier.flatten ++ fifo ++ [event]).IsPrefix
    inputs.flatten from ⟨tail ++ later.flatten, by simp [inputEq, batchEq, List.append_assoc]⟩)
  obtain ⟨_, matching, fresh⟩ := validGraphEvents_last prefixValid
  refine ⟨?_, ?_⟩
  · intro publication member
    simp only [List.flatMap_append, List.length_append] at member
    obtain ⟨absent, registered⟩ := frame.2.2 publication member
    exact ⟨absent.cacheTaskFailures available, fun child incoming same =>
      matching.childTask_not_registered frame.1 fresh incoming (same ▸ registered)⟩
  · simpa only [List.flatMap_append, List.length_append]
      using startup_batchHandlerPublicationCut startup batches started inputEq batchEq

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
