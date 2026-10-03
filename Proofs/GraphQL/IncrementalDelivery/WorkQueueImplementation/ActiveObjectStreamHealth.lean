import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReleasedObjectStreamHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamSourceBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape

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

/-- An actually active object-produced stream needs only mixed-cut and earlier-item safety.
Witness: replay the accepted nonempty prefix as one batch, recover its actual prior
group-success carrier, and apply release health. Neither a chosen supporting group nor
retirement, uncancelledness, or successful producer settlement is supplied as a premise.
-/
theorem ExecutedWork.replayGraphEvents_activeObjectStreamHealthy_of_itemSafety
    {work received matching events failures stream dependencies source}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch received = true)
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    (active
      : stream.ref
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            received).rootStreams)
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
          → occurrence
            ∈ (State.initialize (Work.fromExecution work)).objectFailureContributions
                received)
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
  have nonempty : received ≠ [] := by
    intro empty
    subst received
    have initial := createWorkQueue_streamRoots (Work.fromExecution work) active
    cases generated.initialStream_producerNone known initial
  have batchStarted : inputsStarted work [received] = true := by
    rw [inputsStarted_eq_batchesStarted]
    simp [State.batchesStarted, createWorkQueue_terminated, nonempty, started]
  have batchValid : ValidGraphEvents work [received].flatten := by simpa using valid
  have batchActive : stream.ref ∈
      ((State.initialize (Work.fromExecution work)).runNormalized [received]).1.rootStreams := by
    obtain ⟨terminal, state⟩ := createWorkQueue_runNormalized_stateCore batchStarted
    rw [state]
    simpa using active
  obtain ⟨group, groups, streams, child, owners, carrier, released, same, located⟩ :=
    generated.runNormalized_activeObjectStream_carrier batchValid batchStarted known batchActive
  have healthy := generated.runNormalized_releasedObjectStreamHealthy_of_itemSafety
    batchValid batchStarted carrier released located failedPayloads
    (by simpa using objectsRecorded) (by simpa using itemsSafe)
    (by simpa only [same] using contributors)
  exact ⟨healthy.1, same ▸ healthy.2⟩

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
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher batches).2.2)))
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
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
  let atoms := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
  have objectKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨_, owners, producer, path, errors, descriptor, _⟩ :=
      createWorkQueue_eligibleObjectFailureCuts_origin generated valid entry member
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
  obtain ⟨before, input, after, split, sameAction, accepted, ledger, count⟩ :=
    createWorkQueue_atomicStream_sourcePrefix started selected action
  refine ⟨before, input, after, split, sameAction, count, ?_⟩
  intro itemsSafe
  have prior : before.IsPrefix batches.flatten := ⟨input :: after, split.symm⟩
  have acceptedAll := queue.batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  rw [split] at acceptedAll
  have acceptedBefore := State.acceptsBatch_prefix acceptedAll
  have active : stream.ref ∈ (queue.replayGraphEvents before).rootStreams := by
    cases input <;> simp only [GraphEvent.streamAction] at sameAction
    all_goals try contradiction
    all_goals
      have refEq := (Prod.mk.inj (Option.some.inj sameAction)).1
      simpa [State.acceptsGraphEvent, refEq] using accepted
  have length : (atoms.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  apply generated.replayGraphEvents_activeObjectStreamHealthy_of_itemSafety
    (valid.prefix prior) acceptedBefore known active failedPayloads ?_ itemsSafe ?_
  · intro occurrence owners producer path result descriptor member
    rw [length] at member
    have objectMember := (cuts.object_mem_iff partition descriptor).mp member
    rw [← ledger]
    exact List.mem_reverse.mpr objectMember
  · intro occurrence owners descriptor owner member
    rw [length] at member
    exact cuts.no_failure_at_action_mixed partition objectKnown generated
      (createWorkQueue_runNormalized_atomicStreamActions_ordered valid)
      known selected action nonfailure descriptor owner member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
