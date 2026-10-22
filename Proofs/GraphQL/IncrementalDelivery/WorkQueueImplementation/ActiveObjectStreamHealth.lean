import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InformativeFailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReleasedObjectStreamHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamSourceBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectStreamSupportReplay

/-! Active object-produced streams obtain healthy support from their actual prior release. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- An active object-produced stream must have a successful group carrier
-----------------------------------------------------------------------------------------

/-- An active object-produced stream has a prior group-success carrier in the same replay.
Witness: activation requires an initial or emitted notice. Initial streams have no producer;
item-carried streams have no defer dependencies, unlike a generated object task's nonempty
owners. Notice provenance identifies the remaining carrier's exact producer and ref.
-/
theorem ExecutedWork.runNormalized_activeObjectStream_carrier
    {work batches stream dependencies source}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    (active
      : stream.ref
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.rootStreams)
    : ∃ group groups streams child owners,
        Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten
        ∧ child ∈ streams
        ∧ child.ref = stream.ref
        ∧ NodeAt work child .stream owners (some (.executionGroup source)) := by
  have noticed := createWorkQueue_runNormalized_streamRoots (Work.fromExecution work) batches active
  rcases List.mem_append.mp noticed with initial | later
  · cases generated.initialStream_producerNone known initial
  · obtain ⟨event, emitted, noticed⟩ := List.mem_flatMap.mp later
    cases event with
    | groupSuccess group groups streams =>
        obtain ⟨child, member, same⟩ := List.mem_map.mp noticed
        obtain ⟨owners, producer, located⟩ :=
          createWorkQueue_runNormalized_streamNoticesLocated valid _ emitted child member
        have parent := generated.streamProducer_unique located known same
        exact ⟨group, groups, streams, child, owners, emitted, member, same, parent ▸ located⟩
    | streamValues owner values groups streams =>
        obtain ⟨child, member, same⟩ := List.mem_map.mp noticed
        obtain ⟨index, atEvent⟩ := List.mem_iff_getElem?.mp emitted
        obtain ⟨producer, located, _⟩ :=
          createWorkQueue_runNormalized_itemStreamReleasePublications valid started
            index owner values groups streams atEvent child member
        obtain ⟨ancestor, path, result, producerTask⟩ :=
          NodeAt.stream_objectProducer_owners known
        exact False.elim (generated.taskOwners_nonempty producerTask
          (generated.streamDependencies_unique known located same.symm))
    | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
        cases noticed

/-- An active object-produced stream inherits healthy producer and stream guards.
Witness: actual activation supplies an uncancelled retired dependency and a consumed
producer success. Source-cut exposure and retirement health exclude mixed object failures. -/
theorem ObjectStreamReplayFrame.activeObjectStreamHealthy_of_itemSafety
    {queue work parents received matching events failures stream dependencies source
      objectFailures}
    (frame : ObjectStreamReplayFrame queue work parents received)
    (generated : ExecutedWork work)
    (_canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work received)
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    (active : stream.ref ∈ queue.rootStreams)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (retiredHealthy : queue.UncancelledRetiredHealthy work objectFailures)
    (objectsRecorded
      : ∀ occurrence owners producer path result,
          TaskAt work occurrence owners producer (.object path result)
          → occurrence ∈ failedBefore failures events.length
          → occurrence ∈ objectFailures)
    (itemsSafe
      : ∀ address index,
          Occurrence.item address index ∈ received.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item address index))
    (contributors
      : ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → stream.ref ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    : ¬TaskCancelled work matching events failures (.executionGroup source)
      ∧ ¬NodeFailed work matching events failures stream.ref := by
  obtain ⟨ref, dependency, retired, settled⟩ :=
    frame.support stream dependencies source known active
  obtain ⟨ancestor, path, result, producer⟩ := NodeAt.stream_objectProducer_owners known
  obtain ⟨owner, ownerDependencies, descriptor, sameRef⟩ :=
    TaskAt.executionGroup_owner producer dependency
  have healthy : ¬NodeFailed work matching events failures owner.ref := by
    intro failure
    have exposed := frame.source.regions.registered_exposed (sameRef.symm ▸ retired.retired.1)
    have invalid := generated.exposed_groupFailure_invalidated valid descriptor exposed
      failedPayloads itemsSafe failure
    have recorded := invalid.toRecordInvalidated.restrict_objectFailures generated
      (groupRecordAt_of_nodeAt descriptor) objectsRecorded
    exact retiredHealthy owner ownerDependencies
      (groupRecordAt_of_nodeAt descriptor) (sameRef.symm ▸ retired.retired)
      (sameRef.symm ▸ retired.uncancelled) recorded
  exact generated.objectProducedStream_healthy_of_dependency valid known settled
    dependency failedPayloads itemsSafe (sameRef ▸ healthy) contributors

/-- A real source stream action recovers its active support at the actual batch/FIFO cut.
The consumed failure ledger is separate from the whole-batch rejection snapshot. -/
theorem ExecutedWork.activeObjectStreamHealthy_atSourceCut
    {work batches received input stream dependencies source closing matching events
      failures}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    (action : input.streamAction = some (stream.ref, closing))
    (cut
      : ∃ earlier batch later fifo tail,
          batches = earlier ++ batch :: later
          ∧ batch = fifo ++ input :: tail
          ∧ received = earlier.flatten ++ fifo)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (objectsRecorded
      : ∀ occurrence owners producer path result,
          TaskAt work occurrence owners producer (.object path result)
          → occurrence ∈ failedBefore failures events.length
          → occurrence ∈ GraphEvent.failureSettlements batches.flatten)
    (itemsSafe
      : ∀ address index,
          Occurrence.item address index ∈ received.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item address index))
    (contributors
      : ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → stream.ref ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    : ¬TaskCancelled work matching events failures (.executionGroup source)
      ∧ ¬NodeFailed work matching events failures stream.ref := by
  obtain ⟨earlier, batch, later, fifo, tail, split, batchEq, beforeEq⟩ := cut
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := generated.objectStreamFrame_atBatchPrefix canonical earlier batch later fifo
    (split ▸ valid) (split ▸ started) ⟨input :: tail, batchEq.symm⟩
  have batchValid : ValidGraphEvents work (earlier.flatten ++ batch) :=
    valid.prefix ⟨later.flatten, by simp [split, List.append_assoc]⟩
  have checked : (State.initialize (Work.fromExecution work)).batchesStarted
      (earlier ++ batch :: later) = true := by
    rw [← split, ← inputsStarted_eq_batchesStarted]
    exact started
  have accepted := State.acceptsBatch_streamAction_live (fifo := fifo) (event := input) batchValid
    ((State.initialize (Work.fromExecution work)).batchesStarted_eachBatch earlier batch later
      checked) ⟨tail, by simp [batchEq]⟩ ⟨(stream.ref, closing), action⟩
  have active : stream.ref ∈ (((State.initialize (Work.fromExecution work)).replayBatches
      earlier).replayGraphEvents fifo (GraphEvent.availableFailures batch)).rootStreams := by
    cases input <;> simp only [GraphEvent.streamAction] at action
    all_goals try contradiction
    all_goals
      have refEq := (Prod.mk.inj (Option.some.inj action)).1
      simpa [State.acceptsGraphEvent, refEq] using accepted
  have prior : received.IsPrefix batches.flatten := by
    refine ⟨input :: (tail ++ later.flatten), ?_⟩
    simp only [split, List.flatten_append, List.flatten_cons, batchEq, beforeEq,
      List.append_assoc, List.cons_append]
  let initial := State.initialize (Work.fromExecution work)
  let entry := initial.replayBatches earlier
  have checkedParts : initial.batchesStarted earlier = true
      ∧ entry.batchesStarted (batch :: later) = true := by
    simpa only [State.batchesStarted_append, Bool.and_eq_true] using checked
  have running := (entry.batchesStarted_cons batch later checkedParts.2).1
  have retiredHealthy : (entry.replayGraphEvents fifo (GraphEvent.availableFailures batch)
      ).UncancelledRetiredHealthy work (GraphEvent.failureSettlements batches.flatten) := by
    intro node ancestors record retired uncancelled invalid
    have prior : UncancelledRetirement
        (entry.replayGraphEvents fifo (GraphEvent.availableFailures batch)) node.ref :=
      ⟨retired, uncancelled⟩
    have suffix := prior.replayGraphEvents (input :: tail) (GraphEvent.availableFailures batch)
    have whole : UncancelledRetirement
        (entry.replayGraphEvents batch (GraphEvent.availableFailures batch)) node.ref := by
      rw [← State.replayGraphEvents_append entry fifo (input :: tail)
        (GraphEvent.availableFailures batch), ← batchEq] at suffix
      exact suffix
    obtain ⟨terminal, same⟩ := entry.handleGraphEvents_stateCore batch running
    have atEnd := whole.withTerminated terminal
    rw [← same] at atEnd
    have final := atEnd.replayBatches later
    have health := (generated.runNormalized_retiredHealth batches valid started).1
    rw [State.admittedObjectFailureContributionsForBatches_eq_of_started _ batches
      (by rwa [inputsStarted_eq_batchesStarted] at started)] at health
    have stateEq : (initial.runNormalized batches).1
        = (entry.handleGraphEvents batch).1.replayBatches later := by
      rw [State.runNormalized_replayBatches, split, State.replayBatches_append]
      rfl
    rw [stateEq] at health
    exact health node ancestors record final.retired final.uncancelled invalid
  rw [← beforeEq] at frame
  exact frame.activeObjectStreamHealthy_of_itemSafety generated canonical
    (valid.prefix prior) known active failedPayloads retiredHealthy objectsRecorded
    itemsSafe contributors

-----------------------------------------------------------------------------------------
-- Actual item boundaries leave only safety of strictly earlier source items
-----------------------------------------------------------------------------------------

/-- A nonfailure action of an object-produced stream is healthy if earlier source items
are safe under the same matching and cuts. Witness: recover the exact pre-handler prefix,
derive active release support, align mixed object cuts with accepted failures there, and
exclude contributing stream failures by action order. Current handler items are excluded
from the induction premise; no output admission or extra source invariant is assumed.
-/
theorem ExecutedWork.atomicObjectStreamHealthy_of_earlierItems
    {work batches streams failures matching stream dependencies source index event
      closing}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) streams)
    (partition
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        failures.Perm
          (streams
            ++ informativeObjectFailureCuts work
                (queue.sourceRunBlocks publisher batches).2.2))
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    (selected
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (action : streamAction event = some (stream.ref, closing))
    (nonfailure : ∀ node errors, event ≠ .streamFailure node errors)
    : let atoms :=
        ((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten.flatMap
          publicationAtoms
      ∃ before input after,
        batches.flatten = before ++ input :: after
        ∧ input.streamAction = some (stream.ref, closing)
        ∧ (before.flatMap GraphEvent.itemPublications).length
          ≤ ((atoms.take index).flatMap normalizedItemValues).length
        ∧ ((∀ address ordinal,
              Occurrence.item address ordinal ∈ before.flatMap GraphEvent.successes
              → ¬TaskCancelled work matching (atoms.take index) failures
                  (.item address ordinal))
            → ¬TaskCancelled work matching (atoms.take index) failures
                (.executionGroup source)
              ∧ ¬NodeFailed work matching (atoms.take index) failures stream.ref) := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := informativeObjectFailureCuts work
    (queue.sourceRunBlocks publisher batches).2.2
  let atoms := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
  have objectKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨_, owners, producer, path, errors, descriptor, _⟩ :=
      createWorkQueue_informativeObjectFailureCuts_origin generated valid entry member
    exact ⟨owners, producer, path, errors, descriptor⟩
  have failedPayloads : ∀ cut occurrence,
      (cut, occurrence) ∈ failures
      → ∃ owners producer payload,
          TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true := by
    intro cut occurrence member
    rcases List.mem_append.mp (partition.mem_iff.mp member) with fromStream | fromObject
    · obtain ⟨owner, errors, parent, _, descriptor⟩ := cuts.2 _ fromStream
      exact ⟨_, _, _, descriptor, rfl⟩
    · obtain ⟨owners, parent, path, errors, descriptor⟩ := objectKnown _ fromObject
      exact ⟨_, _, _, descriptor, rfl⟩
  obtain ⟨before, input, after, split, sameAction, actualCut, _ledger, count⟩ :=
    createWorkQueue_atomicStream_sourcePrefix valid started selected action
  refine ⟨before, input, after, split, sameAction, count, ?_⟩
  intro itemsSafe
  have length : (atoms.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  apply generated.activeObjectStreamHealthy_atSourceCut valid started known sameAction
    actualCut failedPayloads ?_ itemsSafe ?_
  · intro occurrence owners producer path result descriptor member
    rw [length] at member
    have objectMember := (cuts.object_mem_iff partition descriptor).mp member
    obtain ⟨entry, selected, same⟩ := List.mem_map.mp objectMember
    have available := (informativeObjectFailureCuts_sublist work _).subset
      (List.mem_filter.mp selected).1
    obtain ⟨errors, received⟩ := createWorkQueue_availableObjectFailureCuts_source generated valid available
    rw [same] at received
    exact List.mem_reverse.mpr (List.mem_flatMap.mpr ⟨_, received, List.mem_cons_self⟩)
  · intro occurrence owners descriptor owner member
    rw [length] at member
    exact cuts.no_failure_at_action_mixed partition objectKnown generated
      (createWorkQueue_runNormalized_atomicStreamActions_ordered valid)
      known selected action nonfailure descriptor owner member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
