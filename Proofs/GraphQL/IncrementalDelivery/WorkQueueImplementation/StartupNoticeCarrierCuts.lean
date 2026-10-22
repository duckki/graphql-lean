import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes

/-! Actual startup notice carriers retain one source cut and both exact publication ranks. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- A canonical item notice retains both prefix counts at one raw carrier position.
Witness: actual batches retain their publisher positions; invert atomization and
normalization without choosing a different publication matching or carrier occurrence.
-/
theorem Witness.startup_itemNotice_rawPrefix {work inputs} {w : Witness}
    {index owner values groups streams child}
    (startup : InitialStartup) (_started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ position rawValues,
        (((State.initialize (Work.fromExecution work) startup)).rawBatches
            inputs).2[position]?
          = some (.streamValues owner rawValues groups streams)
        ∧ ((w.events.take index).flatMap normalizedObjectValues).length
          = (((((State.initialize (Work.fromExecution work) startup)).rawBatches
                inputs).2.take
                position).flatMap
              WorkQueueEvent.objectValues).length
        ∧ ((w.events.take (index + 1)).flatMap normalizedItemValues).length
          = (((((State.initialize (Work.fromExecution work) startup)).rawBatches
                inputs).2.take
                (position + 1)).flatMap
              WorkQueueEvent.itemValues).length := by
  obtain ⟨atFull, prefixEq⟩ := Witness.startup_rawBatches_canonical startup history selected
  have inclusiveEq := Witness.startup_rawBatches_prefix startup history (index + 1)
    (by have bound := (List.getElem?_eq_some_iff.mp selected).1; omega)
  rw [← prefixEq, ← inclusiveEq]
  obtain ⟨sourceIndex, sourceValues, sourceAt, objectCount, itemCount⟩ :=
    publicationAtoms_noticeCarrier_prefix _ atFull noticed
  obtain ⟨position, rawValues, rawAt, rawObjects, rawItems⟩ :=
    IncrementalPublisher.normalizeBatch_streamCarrier_prefix _ _ sourceAt
  exact ⟨
    position,
    rawValues,
    rawAt,
    objectCount.trans rawObjects,
    itemCount.trans rawItems
  ⟩

/-- An item-carried notice has exactly the object prefix preceding its source handler.
Witness: recover its raw carrier and actual source input, then invert the accepted item's
leading-event position. The entire item-preparation phase emits no object publications.
-/
theorem Witness.startup_itemNotice_sourceBoundary
    {work inputs} {w : Witness} {index owner values groups streams child}
    (startup : InitialStartup) (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ earlier batch later fifo stream items tail,
        inputs = earlier ++ batch :: later
        ∧ batch = fifo ++ .streamItems stream items :: tail
        ∧ let current :=
            (((State.initialize (Work.fromExecution work) startup)).replayBatches
              earlier).replayGraphEvents
              fifo (GraphEvent.availableFailures batch)
          let cached := current.cacheTaskFailures (GraphEvent.availableFailures batch)
          current.rootStreams.contains stream.ref = true
          ∧ groups
            = (items.foldl
                (fun acc item =>
                  streamItemStep acc item (GraphEvent.availableFailures batch))
                (cached, [], [], [], [])).2.1
          ∧ ((w.events.take index).flatMap normalizedObjectValues).length
            = ((((State.initialize (Work.fromExecution work) startup)).rawBatches
                  earlier).2.flatMap
                WorkQueueEvent.objectValues).length
              + (((((State.initialize (Work.fromExecution work) startup)).replayBatches
                    earlier).rawEventReplay
                    fifo (GraphEvent.availableFailures batch)).2.flatMap
                  WorkQueueEvent.objectValues).length := by
  obtain ⟨rawIndex, rawValues, rawAt, atomicCount, _⟩ :=
    Witness.startup_itemNotice_rawPrefix startup started history selected noticed
  obtain ⟨earlier, batch, later, fifo, event, tail, position, split, batchEq, emitted, count⟩ :=
    ((State.initialize (Work.fromExecution work)
      startup)).rawBatches_immediate_handlerCut inputs rawAt
      (by intro _ _ impossible; cases impossible) (by intro impossible; cases impossible)
  let current := (((State.initialize (Work.fromExecution work)
    startup)).replayBatches earlier).replayGraphEvents fifo
    (GraphEvent.availableFailures batch)
  let available := GraphEvent.availableFailures batch
  obtain ⟨stream, items, rfl⟩ :=
    current.handleGraphEvent_streamValues_source event available emitted
  have leading : current.rootStreams.contains stream.ref = true ∧ position = 0 ∧
      groups = (items.foldl (fun acc item => streamItemStep acc item available)
        (current.cacheTaskFailures available, [], [], [], [])).2.1 := by
    change ((current.cacheTaskFailures available).streamItems stream items available).2.1[position]?
      = some (.streamValues owner rawValues groups streams) at emitted
    rw [State.streamItems_eq _ _ _ available] at emitted
    have sameRoots : (current.cacheTaskFailures available).rootStreams = current.rootStreams := by
      have frame := congrArg State.rootStreams (current.cacheTaskFailures_frame available)
      exact frame
    cases active : current.rootStreams.contains stream.ref with
    | false => simp only [sameRoots, active, Bool.not_false,
        ↓reduceIte, List.getElem?_nil, reduceCtorEq] at emitted
    | true =>
        simp only [sameRoots, active, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte] at emitted
        cases position with
        | zero => cases emitted; exact ⟨rfl, rfl, rfl⟩
        | succ index =>
            exact False.elim (State.drainReadyGroups_noStreamValues _ owner rawValues groups streams
              available (List.mem_of_getElem? emitted))
  exact ⟨
    earlier,
    batch,
    later,
    fifo,
    stream,
    items,
    tail,
    split,
    batchEq,
    leading.1,
    leading.2.2,
    atomicCount.trans
      (by simpa only [leading.2.1, List.take_zero,
        List.flatMap_nil, List.length_nil, Nat.add_zero] using count)
  ⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
