import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedOutputReplay

/-! Output prefixes retain their exact contents across actual host-batch boundaries. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A fixed-snapshot output cut retains its handler and exact earlier output prefix. -/
theorem State.rawEventReplay_output_prefix_atSnapshot (queue : State)
    (received : List GraphEvent) (available : List (Occurrence × Nat)) {index output}
    (selected : (queue.rawEventReplay received available).2[index]? = some output)
    : ∃ before event after position,
        received = before ++ event :: after
        ∧ ((queue.replayGraphEvents before available).handleGraphEvent event
            available).2.1[position]?
          = some output
        ∧ (queue.rawEventReplay received available).2.take index
          = (queue.rawEventReplay before available).2
            ++ ((queue.replayGraphEvents before available).handleGraphEvent event
                  available).2.1.take
                position := by
  induction received generalizing queue index with
  | nil => simp [State.rawEventReplay] at selected
  | cons event rest ih =>
      rw [State.rawEventReplay_cons queue event rest available] at selected ⊢
      by_cases earlier : index < (queue.dispatchGraphEvent event available).2.length
      · refine ⟨[], event, rest, index, rfl, ?_, ?_⟩
        · exact (List.getElem?_append_left earlier).symm.trans selected
        · rw [List.take_append_of_le_length (Nat.le_of_lt earlier)]
          simp [State.rawEventReplay, State.replayGraphEvents, State.dispatchGraphEvent]
      · have later : (queue.dispatchGraphEvent event available).2.length ≤ index := by omega
        obtain ⟨before, next, after, position, same, atEvent, count⟩ :=
          ih _ ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨event :: before, next, after, position, by simp [same], atEvent, ?_⟩
        rw [List.take_append, List.take_of_length_le later, count,
          State.rawEventReplay_cons queue event before available]
        simp only [List.append_assoc, State.replayGraphEvents, List.foldl_cons]

/-- A raw output cut retains its actual host batch and earlier output prefix. -/
theorem State.rawBatches_output_prefix_at (queue : State)
    (batches : List (List GraphEvent)) {index output}
    (selected : (queue.rawBatches batches).2[index]? = some output)
    : ∃ earlier batch later position,
        batches = earlier ++ batch :: later
        ∧ ((queue.replayBatches earlier).handleGraphEvents batch).2[position]?
          = some output
        ∧ (queue.rawBatches batches).2.take index
          = (queue.rawBatches earlier).2
            ++ ((queue.replayBatches earlier).handleGraphEvents batch).2.take
                position := by
  induction batches generalizing queue index with
  | nil => simp [State.rawBatches] at selected
  | cons batch rest ih =>
      change ((queue.handleGraphEvents batch).2 ++ _)[index]? = some output at selected
      by_cases earlier : index < (queue.handleGraphEvents batch).2.length
      · refine ⟨[], batch, rest, index, rfl, ?_, ?_⟩
        · exact (List.getElem?_append_left earlier).symm.trans selected
        · simp only [State.rawBatches, State.replayBatches, List.foldl_nil,
            List.take_append_of_le_length (Nat.le_of_lt earlier), List.nil_append]
      · have later : (queue.handleGraphEvents batch).2.length ≤ index := by omega
        obtain ⟨before, next, after, position, same, atEvent, count⟩ :=
          ih _ ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨batch :: before, next, after, position, by simp [same], atEvent, ?_⟩
        change ((queue.handleGraphEvents batch).2 ++ _).take index = _
        rw [List.take_append, List.take_of_length_le later, count]
        simp only [State.rawBatches, List.append_assoc,
          State.replayBatches, List.foldl_cons]

/-- An immediate batch output retains its exact FIFO position and strict prefix. -/
theorem State.handleGraphEvents_immediate_rawPrefix (queue : State)
    (batch : List GraphEvent) {index output}
    (selected : (queue.handleGraphEvents batch).2[index]? = some output)
    (_notStartup : ∀ group errors, output ≠ .groupFailure group errors)
    (notTermination : output ≠ .workQueueTermination)
    : (queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2[index]?
        = some output
      ∧ (queue.handleGraphEvents batch).2.take index
        = (queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2.take
            index := by
  have lift (controls : List WorkQueueEvent)
      (absent : output ∉ controls)
      (same : (queue.handleGraphEvents batch).2 =
        (queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2 ++ controls)
      : (queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2[index]?
            = some output
        ∧ (queue.handleGraphEvents batch).2.take index
          = (queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2.take index := by
    rw [same] at selected ⊢
    by_cases inside : index <
        (queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2.length
    · exact ⟨(List.getElem?_append_left inside).symm.trans selected,
        by rw [List.take_append_of_le_length (Nat.le_of_lt inside)]⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_gt inside)] at selected
      exact False.elim (absent (List.mem_of_getElem? selected))
  rw [State.handleGraphEvents_eq_rawEventReplay] at selected
  split at selected
  · cases selected
  · rename_i running
    dsimp only at selected
    split at selected
    · rename_i terminal
      apply lift [.workQueueTermination]
      · intro member
        exact notTermination (List.mem_singleton.mp member)
      · simp only [State.handleGraphEvents_eq_rawEventReplay, running,
          Bool.false_eq_true, ↓reduceIte, terminal]
    · rename_i terminal
      apply lift [] (by simp)
      simp only [State.handleGraphEvents_eq_rawEventReplay, running,
        Bool.false_eq_true, ↓reduceIte, terminal, List.append_nil]

/-- An immediate output retains its actual batch/FIFO handler and strict prefix. -/
theorem State.rawBatches_immediate_rawCut (queue : State)
    (batches : List (List GraphEvent)) {index output}
    (selected : (queue.rawBatches batches).2[index]? = some output)
    (notStartup : ∀ group errors, output ≠ .groupFailure group errors)
    (notTermination : output ≠ .workQueueTermination)
    : ∃ earlier batch later fifo source tail position,
        batches = earlier ++ batch :: later
        ∧ batch = fifo ++ source :: tail
        ∧ (((queue.replayBatches earlier).replayGraphEvents fifo
              (GraphEvent.availableFailures batch)).handleGraphEvent
            source (GraphEvent.availableFailures batch)).2.1[position]?
          = some output
        ∧ (queue.rawBatches batches).2.take index
          = (queue.rawBatches earlier).2
            ++ ((queue.replayBatches earlier).rawEventReplay fifo
                  (GraphEvent.availableFailures batch)).2
            ++ (((queue.replayBatches earlier).replayGraphEvents fifo
                  (GraphEvent.availableFailures batch)).handleGraphEvent
                  source (GraphEvent.availableFailures batch)).2.1.take
                position := by
  obtain ⟨earlier, batch, later, localIndex, split, atBatch, batchCount⟩ :=
    queue.rawBatches_output_prefix_at batches selected
  obtain ⟨atReplay, sameCount⟩ :=
    (queue.replayBatches earlier).handleGraphEvents_immediate_rawPrefix batch atBatch
      notStartup notTermination
  obtain ⟨fifo, source, tail, position, batchEq, atHandler, handlerCount⟩ :=
    (queue.replayBatches earlier).rawEventReplay_output_prefix_atSnapshot batch
      (GraphEvent.availableFailures batch) atReplay
  exact ⟨
    earlier,
    batch,
    later,
    fifo,
    source,
    tail,
    position,
    split,
    batchEq,
    atHandler,
    by rw [batchCount, sameCount, handlerCount, List.append_assoc]
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
