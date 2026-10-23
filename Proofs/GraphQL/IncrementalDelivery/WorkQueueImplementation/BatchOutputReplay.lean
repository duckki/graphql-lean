import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedClosureLedger

/-! Raw output and registration evidence follow actual host batches with their cache snapshots. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Retain actual batch output while following exactly the executable batch state fold.
This is a proof projection; it introduces neither queue storage nor an input schedule.
-/
def State.rawBatches (queue : State)
    : List (List GraphEvent) → State × List WorkQueueEvent
  | [] => (queue, [])
  | batch :: rest =>
      let next := queue.handleGraphEvents batch
      let last := next.1.rawBatches rest
      (last.1, next.2 ++ last.2)

/-- Concatenating actual batch lists retains their exact intermediate state and output. -/
theorem State.rawBatches_append (queue : State) (before after : List (List GraphEvent))
    : queue.rawBatches (before ++ after)
      = let first := queue.rawBatches before
        let last := first.1.rawBatches after
        (last.1, first.2 ++ last.2) := by
  induction before generalizing queue with
  | nil => simp [State.rawBatches]
  | cons batch rest ih =>
      simp only [List.cons_append, State.rawBatches, ih, List.append_assoc]

/-- An actual batch boundary recovers its exact consecutive publication-ledger slice.
The selected queue follows preceding host batches, and the inner replay certificate uses
the selected batch's complete rejection snapshot. No flattened source-state bridge is used.
-/
theorem State.BatchClosuresCovered.atBatch {queue : State} {published}
    (before : List (List GraphEvent)) (batch : List GraphEvent)
    (after : List (List GraphEvent))
    (covered : queue.BatchClosuresCovered (before ++ batch :: after) published)
    : let current := queue.replayBatches before
      let offset :=
        ((queue.rawBatches before).2.flatMap WorkQueueEvent.objectValues).length
      let count :=
        ((current.handleGraphEvents batch).2.flatMap WorkQueueEvent.objectValues).length
      current.ReplayClosuresCovered batch ((published.drop offset).take count)
        (GraphEvent.availableFailures batch)
      ∧ BlocksFollowRegistrations (current.handleGraphEvents batch).1.tasks
          ((published.drop offset).take count) (current.handleGraphEvents batch).2
      ∧ (current.handleGraphEvents batch).1.BatchClosuresCovered after
          ((published.drop offset).drop count) := by
  induction before generalizing queue published with
  | nil => exact covered
  | cons first rest ih =>
      have selected := ih covered.2.2
      simpa only [List.cons_append, State.replayBatches, List.foldl_cons, State.rawBatches,
        List.flatMap_append, List.length_append, List.drop_drop] using selected

/-- Raw batch output does not change the independently defined actual batch state. -/
theorem State.rawBatches_state (queue : State) (batches : List (List GraphEvent))
    : (queue.rawBatches batches).1 = queue.replayBatches batches := by
  induction batches generalizing queue with
  | nil => rfl
  | cons batch rest ih => exact ih _

/-- Permanent task registrations grow through each actual batch, including ignored batches. -/
theorem State.handleGraphEvents_tasks_sublist (queue : State) (events : List GraphEvent)
    : queue.tasks.Sublist (queue.handleGraphEvents events).1.tasks := by
  cases running : queue.terminated with
  | true => simp only [State.handleGraphEvents, running, ↓reduceIte]; exact .refl _
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      rw [same]
      exact queue.replayGraphEvents_tasks_sublist events (GraphEvent.availableFailures events)

/-- Earlier batch registries remain ordered subsequences of the final actual registry. -/
theorem State.rawBatches_tasks_sublist (queue : State) (batches : List (List GraphEvent))
    : queue.tasks.Sublist (queue.rawBatches batches).1.tasks := by
  induction batches generalizing queue with
  | nil => exact .refl _
  | cons batch rest ih => exact (queue.handleGraphEvents_tasks_sublist batch).trans (ih _)

/-- Valid started batching preserves producer order on the actual final task registry. -/
theorem State.rawBatches_producerOrder {queue : State} {work before}
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : TaskProducersSucceeded work (queue.rawBatches batches).1.tasks
        (before ++ batches.flatten)
      ∧ ProducerOrder work ((queue.rawBatches batches).1.tasks.map Task.occurrence) := by
  induction batches generalizing queue before with
  | nil =>
      simpa only [State.rawBatches, List.flatten_nil, List.append_nil] using And.intro ready ordered
  | cons batch rest ih =>
      obtain ⟨running, _, later⟩ := queue.batchesStarted_cons batch rest started
      have boundary : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have replayed := queue.replayGraphEvents_producerOrder ready ordered batch
        (valid.prefix boundary) (GraphEvent.availableFailures batch)
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore batch running
      have next : TaskProducersSucceeded work (queue.handleGraphEvents batch).1.tasks
          (before ++ batch)
          ∧ ProducerOrder work ((queue.handleGraphEvents batch).1.tasks.map Task.occurrence) := by
        rw [same]
        exact replayed
      simpa only [State.rawBatches, List.flatten_cons, List.append_assoc]
        using ih next.1 next.2
          (by simpa only [List.flatten_cons, List.append_assoc] using valid) later

/-- Creation supplies the producer-order premises for actual valid started batches. -/
theorem createWorkQueue_rawBatches_producerOrder {work batches}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ProducerOrder work
        (((State.initialize (Work.fromExecution work)).rawBatches batches).1.tasks.map
          Task.occurrence) :=
  ((State.initialize (Work.fromExecution work)).rawBatches_producerOrder
    (before := []) (createWorkQueue_producerOrder work).1
    (createWorkQueue_producerOrder work).2 batches valid
    (by rwa [← inputsStarted_eq_batchesStarted])).2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
