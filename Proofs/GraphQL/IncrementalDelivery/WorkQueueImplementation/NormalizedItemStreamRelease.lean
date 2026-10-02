import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemStreamReleaseReplay

/-! Normalization keeps each item-stream carrier's inclusive source-publication prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Publisher normalization retains stream carriers and inclusive item counts
-----------------------------------------------------------------------------------------

/-- A normalized stream-value carrier is the singleton output of a raw stream-value event.
Witness: every other raw constructor has a different tag; item/error mapping keeps the
carrier's owner and child notice lists. The value-list conversion is intentionally existential.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_streamValues
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    {index owner values groups streams}
    (atEvent
      : (publisher.handleWorkQueueEvent event).2[index]?
        = some (.streamValues owner values groups streams))
    : ∃ rawValues, event = .streamValues owner rawValues groups streams ∧ index = 0 := by
  have member := List.mem_of_getElem? atEvent
  cases event with
  | groupValues group entries =>
      obtain ⟨entry, _, impossible⟩ := List.mem_map.mp member
      cases impossible
  | streamValues stream entries newGroups newStreams =>
      have same := List.mem_singleton.mp member
      obtain ⟨rfl, _, rfl, rfl⟩ := Execution.WorkQueueEvent.streamValues.inj same
      refine ⟨entries, rfl, ?_⟩
      cases index with
      | zero => rfl
      | succ index => simp [IncrementalPublisher.handleWorkQueueEvent] at atEvent
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [IncrementalPublisher.handleWorkQueueEvent] at member

/-- A normalized item carrier retains the raw carrier's inclusive item-publication count.
Witness: the carrier stays a singleton; normalization preserves each earlier event's item
projection even when it expands group values into multiple owner-specific events.
-/
theorem IncrementalPublisher.normalizeBatch_streamValues
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    {index owner values groups streams}
    (atEvent
      : (publisher.normalizeBatch events).2[index]?
        = some (.streamValues owner values groups streams))
    : ∃ rawIndex rawValues,
        events[rawIndex]? = some (.streamValues owner rawValues groups streams)
        ∧ (((publisher.normalizeBatch events).2.take (index + 1)).flatMap
            normalizedItemValues).length
          = ((events.take (rawIndex + 1)).flatMap WorkQueueEvent.itemValues).length := by
  induction events generalizing publisher index with
  | nil => simp [IncrementalPublisher.normalizeBatch] at atEvent
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons] at atEvent ⊢
      dsimp only at atEvent ⊢
      let head := publisher.handleWorkQueueEvent event
      let tail := head.1.normalizeBatch rest
      change (head.2 ++ tail.2)[index]? = _ at atEvent
      by_cases earlier : index < head.2.length
      · have atHead := (List.getElem?_append_left earlier).symm.trans atEvent
        obtain ⟨rawValues, rfl, rfl⟩ := publisher.handleWorkQueueEvent_streamValues event atHead
        refine ⟨0, rawValues, rfl, ?_⟩
        simp [IncrementalPublisher.handleWorkQueueEvent, normalizedItemValues,
          WorkQueueEvent.itemValues]
      · have later : head.2.length ≤ index := by omega
        have atTail := (List.getElem?_append_right later).symm.trans atEvent
        obtain ⟨rawIndex, rawValues, rawAt, count⟩ := ih head.1 atTail
        refine ⟨rawIndex + 1, rawValues, rawAt, ?_⟩
        change (((head.2 ++ tail.2).take (index + 1)).flatMap normalizedItemValues).length = _
        rw [List.take_append, List.take_of_length_le (by omega : head.2.length ≤ index + 1),
          show index + 1 - head.2.length = index - head.2.length + 1 by omega,
          List.flatMap_append, List.length_append, count]
        simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
        exact congrArg (· + _) (congrArg List.length
          (publisher.handleWorkQueueEvent_itemValues event))

-----------------------------------------------------------------------------------------
-- The same source item labels justify release after normalization and concatenation
-----------------------------------------------------------------------------------------

/-- A normalized item-stream notice has its producer in the inclusive item-inventory prefix.
The ordered labels come from supplied graph events; no payload-based identity choice occurs.
-/
def NormalizedItemStreamReleasePublications (work : Execution.Work)
    (published : List ItemPublication) (events : List Execution.WorkQueueEvent)
    : Prop :=
  ∀ index owner values groups streams,
    events[index]? = some (.streamValues owner values groups streams)
    → ∀ child ∈ streams,
        ∃ occurrence,
          NodeAt work child .stream [] (some occurrence)
          ∧ occurrence
            ∈ (published.take
                ((events.take (index + 1)).flatMap normalizedItemValues).length).map
                Prod.fst

/-- Normalization retains item release support with its original occurrence labels.
Witness: every normalized carrier has a raw carrier and the same inclusive item count.
-/
theorem ItemStreamReleasePublications.normalizeBatch {work published events}
    (supported : ItemStreamReleasePublications work published events)
    (publisher : IncrementalPublisher)
    : NormalizedItemStreamReleasePublications work published
        (publisher.normalizeBatch events).2 := by
  intro index owner values groups streams atEvent child noticed
  obtain ⟨rawIndex, rawValues, rawAt, count⟩ := publisher.normalizeBatch_streamValues events atEvent
  rw [count]
  exact supported rawIndex owner rawValues groups streams rawAt child noticed

/-- Empty normalized output has no item-stream notice to justify.
Witness: no output index can select a carrier.
-/
theorem NormalizedItemStreamReleasePublications.nil (work : Execution.Work)
    : NormalizedItemStreamReleasePublications work [] [] := by
  intro index owner values groups streams impossible
  simp at impossible

/-- Concatenated normalized histories retain support in the same concatenated item inventory.
Witness: exact earlier item erasure shifts each later carrier's inclusive prefix correctly.
-/
theorem NormalizedItemStreamReleasePublications.append {work first second left right}
    (before : NormalizedItemStreamReleasePublications work first left)
    (after : NormalizedItemStreamReleasePublications work second right)
    (values : first.map Prod.snd = left.flatMap normalizedItemValues)
    : NormalizedItemStreamReleasePublications work (first ++ second) (left ++ right) := by
  have size : first.length = (left.flatMap normalizedItemValues).length := by
    simpa only [List.length_map] using congrArg List.length values
  intro index owner items groups streams atEvent child noticed
  by_cases earlier : index < left.length
  · have atLeft := (List.getElem?_append_left earlier).symm.trans atEvent
    obtain ⟨occurrence, known, source⟩ :=
      before index owner items groups streams atLeft child noticed
    have count : ((left.take (index + 1)).flatMap normalizedItemValues).length ≤ first.length := by
      have split := congrArg (fun events : List Execution.WorkQueueEvent =>
        (events.flatMap normalizedItemValues).length) (List.take_append_drop (index + 1) left)
      simp only [List.flatMap_append, List.length_append] at split
      omega
    refine ⟨occurrence, known, ?_⟩
    rw [List.take_append_of_le_length (by omega : index + 1 ≤ left.length),
      List.take_append_of_le_length count]
    exact source
  · have later : left.length ≤ index := by omega
    have atRight := (List.getElem?_append_right later).symm.trans atEvent
    obtain ⟨occurrence, known, source⟩ :=
      after (index - left.length) owner items groups streams atRight child noticed
    refine ⟨occurrence, known, ?_⟩
    rw [List.take_append (l₁ := left), List.take_of_length_le (by omega : left.length ≤ index + 1),
      show index + 1 - left.length = index - left.length + 1 by omega,
      List.flatMap_append, List.length_append, ← size, List.take_append (l₁ := first)]
    simp only [List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.map_append]
    exact List.mem_append_right _ source

-----------------------------------------------------------------------------------------
-- The real normalized runner supplies release support with the source's exact item list
-----------------------------------------------------------------------------------------

/-- Every actual item-carrier stream notice has a producer already in its inclusive item prefix.
Witness: started batches copy all supplied items in order; matching payloads locate the
producer, and normalization/concatenation retain that same ordered inventory throughout.
Generated-key uniqueness, output admission, and additional source assumptions are unnecessary.
-/
theorem createWorkQueue_runNormalized_itemStreamReleasePublications
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : NormalizedItemStreamReleasePublications work
        (batches.flatten.flatMap GraphEvent.itemPublications)
        ((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (published : List ItemPublication)
      (values : published.map Prod.snd = acc.2.2.flatten.flatMap normalizedItemValues)
      (supported : NormalizedItemStreamReleasePublications work published acc.2.2.flatten)
      (matching : ∀ event ∈ more.flatten, event.MatchesWork work)
      (started : acc.1.batchesStarted more = true)
      : NormalizedItemStreamReleasePublications work
          (published ++ more.flatten.flatMap GraphEvent.itemPublications)
          (more.foldl normalizedStep acc).2.2.flatten := by
    induction more generalizing acc published with
    | nil =>
        simpa only [List.flatten_nil, List.flatMap_nil, List.append_nil, List.foldl_nil]
          using supported
    | cons batch rest ih =>
        obtain ⟨startOpen, accepted, nextStarted⟩ := acc.1.batchesStarted_cons batch rest started
        have rawSupport := acc.1.handleGraphEvents_itemStreamRelease batch
          (fun event member => matching event (List.mem_append_left _ member)) startOpen accepted
        have rawValues := acc.1.handleGraphEvents_itemValues batch startOpen accepted
        have nextValues : (published ++ batch.flatMap GraphEvent.itemPublications).map Prod.snd
            = (normalizedStep acc batch).2.2.flatten.flatMap normalizedItemValues := by
          rw [normalizedStep_itemValues, List.map_append, values, rawValues]
        have nextSupport : NormalizedItemStreamReleasePublications work
            (published ++ batch.flatMap GraphEvent.itemPublications)
            (normalizedStep acc batch).2.2.flatten := by
          rw [normalizedStep_flatten]
          exact supported.append (rawSupport.normalizeBatch acc.2.1) values
        have finished := ih (normalizedStep acc batch) _ nextValues nextSupport
          (fun event member => matching event (List.mem_append_right _ member))
          (by rw [normalizedStep_queue]; exact nextStarted)
        simpa only [List.flatten_cons, List.flatMap_append, List.append_assoc,
          List.foldl_cons]
          using finished
  rw [inputsStarted_eq_batchesStarted] at started
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  exact loop batches (queue, publisher, []) [] rfl (.nil work)
    (fun event member => valid.event_matches member) started

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
