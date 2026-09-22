import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedPublications

/-! Accepted stream-item inputs are published exactly, once, and in source order. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- One supplied item, with its proof-only occurrence and unchanged stream/payload pair. -/
abbrev ItemPublication := Occurrence × Execution.DeliveryNode × Execution.StreamItemValue

/-- Source item publications carried directly by a graph event, in its item-list order. -/
def GraphEvent.itemPublications : GraphEvent → List ItemPublication
  | .streamItems stream items =>
      items.map
        fun item => (item.occurrence, stream, ⟨item.value.item, item.value.errors⟩)
  | _ => []

/-- Stream/payload pairs in raw queue output, retaining the stream's exact descriptor. -/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.itemValues
    : WorkQueueEvent → List (Execution.DeliveryNode × Execution.StreamItemValue)
  | .streamValues stream values _ _ =>
      values.map fun value => (stream, ⟨value.item, value.errors⟩)
  | _ => []

/-- Stream/payload pairs in normalized output, before wire-entry mapping. -/
def normalizedItemValues
    : Execution.WorkQueueEvent → List (Execution.DeliveryNode × Execution.StreamItemValue)
  | .streamValues stream values _ _ => values.map (stream, ·)
  | _ => []

-----------------------------------------------------------------------------------------
-- Only the stream-item handler emits items, without storing or postponing their values
-----------------------------------------------------------------------------------------

/-- Successful group cleanup cannot emit a stream-item payload.
Witness: its exact output consists of object values and a group-completion notice. -/
theorem State.finishGroupSuccess_itemValues (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).2.1.flatMap WorkQueueEvent.itemValues = [] := by
  obtain ⟨selected, _, _, events, _, _⟩ := queue.finishGroupSuccess_publications group
  rw [events]
  split <;> simp [WorkQueueEvent.itemValues]

/-- Recursive group draining emits no stream-item payloads.
Witness: induction on the actual drain budget; successful and cached-failure group
closures contribute only object values and control events.
-/
theorem State.drainReadyGroups_itemValues (queue : State)
    : queue.drainReadyGroups.2.flatMap WorkQueueEvent.itemValues = [] := by
  have loop (fuel : Nat) (current : State)
      : (State.drainReadyGroups.go fuel current).2.flatMap WorkQueueEvent.itemValues
        = [] := by
    induction fuel generalizing current with
    | zero => rfl
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · rfl
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              simp only [List.flatMap_append, State.finishGroupSuccess_itemValues, ih,
                List.nil_append]
          | some errors =>
              simp only [State.finishGroupFailure, List.flatMap_append,
                List.flatMap_singleton, WorkQueueEvent.itemValues, ih, List.nil_append]
  exact loop _ queue

/-- Task success never emits stream-item payloads, even when it releases child streams.
Witness: its contributor fold and final drain append only group-cleanup output. -/
theorem State.taskSuccess_itemValues (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).2.flatMap WorkQueueEvent.itemValues = [] := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      : (groups.foldl successGroupStep acc).2.1.flatMap WorkQueueEvent.itemValues =
        acc.2.1.flatMap WorkQueueEvent.itemValues := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih]
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · rfl
        · split
          · simp only [List.flatMap_append, State.finishGroupSuccess_itemValues, List.append_nil]
          · rfl
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · rfl
      simp only [List.flatMap_append, State.drainReadyGroups_itemValues, List.append_nil]
      exact loop _ (_, [], {})

/-- Task failure emits no item payloads; it can only close groups or cache their errors.
Witness: the owner fold appends group-failure constructors only. -/
theorem State.taskFailure_itemValues (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).2.flatMap WorkQueueEvent.itemValues = [] := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.key with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.key then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      : (groups.foldl step acc).2.flatMap WorkQueueEvent.itemValues =
          acc.2.flatMap WorkQueueEvent.itemValues := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih]
        unfold step
        split
        · rfl
        · split
          · simp [State.finishGroupFailure, List.flatMap_append, WorkQueueEvent.itemValues]
          · rfl
  unfold State.taskFailure
  split
  · rfl
  · split
    · rfl
    exact loop _ (_, [])

/-- An accepted stream-item event emits exactly its supplied items in order.
Witness: the item accumulator appends each unchanged input value exactly once; child-work
integration affects notices/state and the final group drain emits no extra items. -/
theorem State.streamItems_itemValues (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (active : queue.rootStreams.contains stream.key = true)
    : (queue.streamItems stream items).2.flatMap WorkQueueEvent.itemValues
      = (GraphEvent.itemPublications (.streamItems stream items)).map Prod.snd := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      : (more.foldl step acc).2.2.2 = acc.2.2.2 ++ more.map StreamItem.value := by
    induction more generalizing acc with
    | nil => simp
    | cons item rest ih =>
        rw [List.foldl_cons, ih]
        simp [step, List.append_assoc]
  simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ite_false,
    List.flatMap_cons, WorkQueueEvent.itemValues, State.drainReadyGroups_itemValues,
    List.append_nil]
  change (items.foldl step (queue, [], [], [])).2.2.2.map
    (fun value => (stream, Execution.StreamItemValue.mk value.item value.errors)) = _
  rw [loop]
  simp [GraphEvent.itemPublications, List.map_map, Function.comp_def]

/-- Every accepted graph event emits precisely its own input item projection.
Witness: item arrival copies its values; task and closure handlers emit no items. -/
theorem State.handleGraphEvent_itemValues (queue : State) (event : GraphEvent)
    (accepted : queue.acceptsGraphEvent event = true)
    : (queue.handleGraphEvent event).2.flatMap WorkQueueEvent.itemValues
      = event.itemPublications.map Prod.snd := by
  cases event with
  | taskSuccess occurrence result => exact queue.taskSuccess_itemValues occurrence result
  | taskFailure occurrence errors => exact queue.taskFailure_itemValues occurrence errors
  | streamItems stream items => exact queue.streamItems_itemValues stream items accepted
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> rfl
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> rfl

/-- Accepted eventwise replay emits all source items in order, without delay or duplication.
Witness: compose exact per-handler item output while threading the actual queue state. -/
theorem State.rawEventReplay_itemValues (queue : State) (events : List GraphEvent)
    (accepted : queue.acceptsBatch events = true)
    : (queue.rawEventReplay events).2.flatMap WorkQueueEvent.itemValues
      = (events.flatMap GraphEvent.itemPublications).map Prod.snd := by
  induction events generalizing queue with
  | nil => rfl
  | cons event rest ih =>
      have both : queue.acceptsGraphEvent event = true ∧
          (queue.handleGraphEvent event).1.acceptsBatch rest = true := by
        simpa only [State.acceptsBatch, Bool.and_eq_true] using accepted
      rw [State.rawEventReplay_cons]
      simp only [List.flatMap_append, State.handleGraphEvent_itemValues queue event both.1,
        ih _ both.2, List.flatMap_cons, List.map_append]

/-- Before queue termination, a started batch emits exactly its input item values.
Witness: eventwise exactness; appending a terminal control event cannot add an item. -/
theorem State.handleGraphEvents_itemValues (queue : State) (events : List GraphEvent)
    (startOpen : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).2.flatMap WorkQueueEvent.itemValues
      = (events.flatMap GraphEvent.itemPublications).map Prod.snd := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  simp only [startOpen, Bool.false_eq_true, ite_false]
  split
  · simpa only [List.flatMap_append, List.flatMap_singleton, WorkQueueEvent.itemValues,
      List.append_nil] using queue.rawEventReplay_itemValues events accepted
  · exact queue.rawEventReplay_itemValues events accepted

-----------------------------------------------------------------------------------------
-- Publisher normalization and batching preserve item payloads and source order
-----------------------------------------------------------------------------------------

/-- Publisher normalization preserves one raw event's stream descriptor and item sequence.
Witness: the stream constructor copies its item/error pairs; other events contain no items.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_itemValues
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap normalizedItemValues
      = event.itemValues := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, WorkQueueEvent.itemValues,
    List.flatMap_map, normalizedItemValues]

/-- Normalizing an entire raw batch preserves its complete item projection.
Witness: the actual publisher fold composes one-event preservation in order. -/
theorem IncrementalPublisher.normalizeBatch_itemValues (publisher : IncrementalPublisher)
    (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.flatMap normalizedItemValues
      = events.flatMap WorkQueueEvent.itemValues := by
  let step (acc : IncrementalPublisher × List Execution.WorkQueueEvent) (event : WorkQueueEvent) :=
    let (next, output) := acc.1.handleWorkQueueEvent event
    (next, acc.2 ++ output)
  have loop (more : List WorkQueueEvent) (acc : IncrementalPublisher × List Execution.WorkQueueEvent)
      : (more.foldl step acc).2.flatMap normalizedItemValues =
        acc.2.flatMap normalizedItemValues ++ more.flatMap WorkQueueEvent.itemValues := by
    induction more generalizing acc with
    | nil => simp
    | cons event rest ih =>
        rw [List.foldl_cons, ih]
        simp only [step, List.flatMap_append,
          IncrementalPublisher.handleWorkQueueEvent_itemValues,
          List.flatMap_cons, List.append_assoc]
  exact loop events (publisher, [])

/-- One normalized batch step appends exactly the raw batch's item projection.
Witness: payload-preserving publisher normalization and omission of empty raw batches. -/
theorem normalizedStep_itemValues (acc : NormalizedAcc) (batch : List GraphEvent)
    : (normalizedStep acc batch).2.2.flatten.flatMap normalizedItemValues
      = acc.2.2.flatten.flatMap normalizedItemValues
        ++ (acc.1.handleGraphEvents batch).2.flatMap WorkQueueEvent.itemValues := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  dsimp only [normalizedStep]
  split
  · rename_i empty
    rw [List.isEmpty_iff.mp empty]
    simp
  · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.flatMap_append, IncrementalPublisher.normalizeBatch_itemValues]

/-- Every started item input appears exactly in the normalized output, in input order.
Witness: the public start check exposes each batch's open state and accepted events;
the actual runner and publisher preserve their exact item projection through termination.
This concerns received inputs, not eventual arrival of every item in the work tree. -/
theorem createWorkQueue_runNormalized_itemValues {work : Execution.Work}
    {batches : List (List GraphEvent)} (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).2.flatten.flatMap
        normalizedItemValues
      = (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.snd := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (started : acc.1.batchesStarted more = true)
      : (more.foldl normalizedStep acc).2.2.flatten.flatMap normalizedItemValues =
        acc.2.2.flatten.flatMap normalizedItemValues ++
          (more.flatten.flatMap GraphEvent.itemPublications).map Prod.snd := by
    induction more generalizing acc with
    | nil => simp
    | cons batch rest ih =>
        obtain ⟨startOpen, accepted, nextStarted⟩ := acc.1.batchesStarted_cons batch rest started
        have checked : (normalizedStep acc batch).1.batchesStarted rest = true := by
          rw [normalizedStep_queue]
          exact nextStarted
        rw [List.foldl_cons, ih _ checked, normalizedStep_itemValues,
          acc.1.handleGraphEvents_itemValues batch startOpen accepted]
        simp only [List.flatten_cons, List.flatMap_append, List.map_append, List.append_assoc]
  rw [inputsStarted_eq_batchesStarted] at started
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  exact loop batches (queue, publisher, []) started

-----------------------------------------------------------------------------------------
-- Source freshness and fixed outcomes give exact occurrence-unique output witnesses
-----------------------------------------------------------------------------------------

/-- The supplied item occurrences form a sublist of all source settlement identities.
Witness: item events retain their identity list; task settlements and closures are omitted.
-/
theorem GraphEvent.itemPublications_sublist (events : List GraphEvent)
    : ((events.flatMap GraphEvent.itemPublications).map Prod.fst).Sublist
        (events.flatMap (fun event => event.identities.1)) := by
  have single (event : GraphEvent)
      : (event.itemPublications.map Prod.fst).Sublist event.identities.1 := by
    cases event <;> simp [GraphEvent.itemPublications, GraphEvent.identities,
      List.map_map, Function.comp_def]
  induction events with
  | nil => exact List.Sublist.refl _
  | cons event rest ih =>
      simp only [List.flatMap_cons, List.map_append]
      exact (single event).append ih

/-- Every supplied item retains its exact stream descriptor, value, and error count.
Witness: membership in the matched event's item list and its fixed source task descriptor.
-/
theorem GraphEvent.MatchesWork.itemPublications {work : Execution.Work}
    {event : GraphEvent} (matching : event.MatchesWork work)
    {publication : ItemPublication} (member : publication ∈ event.itemPublications)
    : ∃ owners producer,
        TaskAt work publication.1 owners producer
          (.item publication.2.1
            (.ok (publication.2.2.item, publication.2.2.errors))) := by
  cases event with
  | streamItems stream items =>
      obtain ⟨item, inItems, same⟩ := List.mem_map.mp member
      subst publication
      obtain ⟨owners, producer, known, _⟩ := matching item inItems
      exact ⟨owners, producer, known⟩
  | taskSuccess | taskFailure | streamSuccess | streamFailure => cases member

/-- All accepted item inputs have occurrence-unique exact witnesses in normalized output.
Witness: input identity uniqueness, exact batch/publisher copying, and fixed-outcome
matching. No generated-work, output-accounting, or lifecycle premise is added. -/
theorem createWorkQueue_runNormalized_itemSources {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let publications := batches.flatten.flatMap GraphEvent.itemPublications
      (publications.map Prod.fst).Nodup
      ∧ publications.map Prod.snd
        = ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            normalizedItemValues
      ∧ ∀ publication ∈ publications,
          ∃ owners producer,
            TaskAt work publication.1 owners producer
              (.item publication.2.1
                (.ok (publication.2.2.item, publication.2.2.errors))) := by
  refine ⟨(GraphEvent.itemPublications_sublist _).nodup valid.identities_nodup.1,
    (createWorkQueue_runNormalized_itemValues started).symm, ?_⟩
  intro publication member
  obtain ⟨event, eventMember, itemMember⟩ := List.mem_flatMap.mp member
  exact (valid.event_matches eventMember).itemPublications itemMember

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
