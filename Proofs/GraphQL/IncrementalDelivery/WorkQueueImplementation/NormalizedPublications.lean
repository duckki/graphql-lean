import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay

/-! Object publication uniqueness reaches the actual normalized scheduler output. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Publisher remapping changes owners, not payloads or their order
-----------------------------------------------------------------------------------------

/-- The same object-value projection at the normalized boundary; values are not converted.
-/
abbrev normalizedObjectValues := WorkQueueEvent.objectValues

/-- Normalizing one raw event preserves every object payload exactly and in order.
Witness: group values expand to singleton events; all other constructors have no object
payload. This statement is independent of which effective owner is selected. -/
theorem IncrementalPublisher.handleWorkQueueEvent_objectValues
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap normalizedObjectValues
      = event.objectValues := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent,
    WorkQueueEvent.objectValues, List.flatMap_map, normalizedObjectValues]

/-- Normalizing a raw batch preserves the flattened object payload sequence.
Witness: compose one-event payload preservation through the actual publisher-state fold. -/
theorem IncrementalPublisher.normalizeBatch_objectValues
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.flatMap normalizedObjectValues
      = (events.flatMap WorkQueueEvent.objectValues) := by
  let step (acc : IncrementalPublisher × List Execution.WorkQueueEvent) (event : WorkQueueEvent) :=
    let (next, output) := acc.1.handleWorkQueueEvent event
    (next, acc.2 ++ output)
  have loop (more : List WorkQueueEvent) (acc : IncrementalPublisher × List Execution.WorkQueueEvent)
      : (more.foldl step acc).2.flatMap normalizedObjectValues =
        acc.2.flatMap normalizedObjectValues ++
          (more.flatMap WorkQueueEvent.objectValues) := by
    induction more generalizing acc with
    | nil => simp
    | cons event rest ih =>
        rw [List.foldl_cons, ih]
        simp only [step, List.flatMap_append,
          IncrementalPublisher.handleWorkQueueEvent_objectValues,
          List.flatMap_cons, List.append_assoc]
  exact loop events (publisher, [])

/-- One normalized batch step adds exactly the raw batch's object values to prior output.
Witness: publisher payload preservation and omission of genuinely empty raw batches. -/
theorem normalizedStep_objectValues (acc : NormalizedAcc) (batch : List GraphEvent)
    : (normalizedStep acc batch).2.2.flatten.flatMap normalizedObjectValues
      = acc.2.2.flatten.flatMap normalizedObjectValues
        ++ ((acc.1.handleGraphEvents batch).2.flatMap WorkQueueEvent.objectValues) := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  dsimp only [normalizedStep]
  split
  · rename_i empty
    rw [List.isEmpty_iff.mp empty]
    simp
  · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.flatMap_append, IncrementalPublisher.normalizeBatch_objectValues]

/-- The publisher cannot change the queue state produced by its batch handler.
Witness: both productive and empty-output branches retain exactly the returned queue. -/
theorem normalizedStep_queue (acc : NormalizedAcc) (batch : List GraphEvent)
    : (normalizedStep acc batch).1 = (acc.1.handleGraphEvents batch).1 := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  dsimp only [normalizedStep]
  split <;> rfl

-----------------------------------------------------------------------------------------
-- A single occurrence-unique witness covers all emitted normalized batches
-----------------------------------------------------------------------------------------

/-- The real normalized runner publishes each object occurrence at most once across all
input batches. Witness: the source-fresh publication inventory, actual batch wrapper, and
payload-preserving publisher. Interruptions, empty outputs, and terminal batches are kept.
This proves object payload provenance/freshness, not notice or effective-owner admission.
-/
theorem createWorkQueue_runNormalized_publications {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ∃ published : List ObjectPublication,
        published.map (fun publication => publication.2)
          = ((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
              normalizedObjectValues
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.PublicationInventory
            (ObjectValueFrom batches.flatten) published := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (before : List GraphEvent) (published : List ObjectPublication)
      (inventory : acc.1.PublicationInventory (ObjectValueFrom before) published)
      (values : published.map (fun publication => publication.2) =
        acc.2.2.flatten.flatMap normalizedObjectValues)
      (valid : ValidGraphEvents work (before ++ more.flatten))
      : ∃ final : List ObjectPublication,
        final.map (fun publication => publication.2) =
          (more.foldl normalizedStep acc).2.2.flatten.flatMap normalizedObjectValues
        ∧ (more.foldl normalizedStep acc).1.PublicationInventory
          (ObjectValueFrom (before ++ more.flatten)) final := by
    induction more generalizing acc before published with
    | nil =>
        exact ⟨
          published,
          values,
          by
            simpa only [List.flatten_nil, List.append_nil, List.foldl_nil] using inventory
        ⟩
    | cons batch rest ih =>
        have firstPrefix : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
          ⟨rest.flatten, by simp [List.append_assoc]⟩
        obtain ⟨added, exactValues, current⟩ := inventory.handleGraphEvents batch
          (valid.prefix firstPrefix)
        have nextInventory : (normalizedStep acc batch).1.PublicationInventory
            (ObjectValueFrom (before ++ batch)) (published ++ added) := by
          rw [normalizedStep_queue]
          exact current
        have nextValues : (published ++ added).map (fun publication => publication.2) =
            (normalizedStep acc batch).2.2.flatten.flatMap normalizedObjectValues := by
          rw [normalizedStep_objectValues, List.map_append, values]
          exact congrArg (acc.2.2.flatten.flatMap normalizedObjectValues ++ ·) exactValues
        obtain ⟨final, finalValues, finalInventory⟩ :=
          ih _ (before ++ batch) (published ++ added) nextInventory nextValues
            (by simpa only [List.flatten_cons, List.append_assoc] using valid)
        exact ⟨
          final,
          finalValues,
          by
            simpa only [List.flatten_cons, List.append_assoc, List.foldl_cons]
              using finalInventory
        ⟩
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have initial : queue.PublicationInventory (ObjectValueFrom []) [] :=
    ⟨by simp, by simp, createWorkQueue_storedValues _ _⟩
  exact loop batches (queue, publisher, []) [] [] initial rfl valid

/-- Normalized object values have a duplicate-free list of source occurrences, each paired
with an exact matched success input. Witness: the runner's publication inventory and the
source derivation. No additional scheduler-state assumption or output filter is used. -/
theorem createWorkQueue_runNormalized_objectSources {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ∃ published : List ObjectPublication,
        (published.map Prod.fst).Nodup
        ∧ published.map (fun publication => publication.2)
          = ((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
              normalizedObjectValues
        ∧ ∀ publication ∈ published,
            ∃ result,
              .taskSuccess publication.1 result ∈ batches.flatten
              ∧ result.value = publication.2
              ∧ (GraphEvent.taskSuccess publication.1 result).MatchesWork work := by
  obtain ⟨published, values, inventory⟩ := createWorkQueue_runNormalized_publications valid
  refine ⟨published, inventory.unique, values, ?_⟩
  intro publication member
  obtain ⟨result, supplied, same⟩ := inventory.provenance publication member
  exact ⟨result, supplied, same, valid.event_matches supplied⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
