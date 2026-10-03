import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OutputAtoms

/-! Actual queue/publisher output has nonempty value events and nonempty batches. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Actual handlers cannot emit empty value events from legal source events
-----------------------------------------------------------------------------------------

/-- A raw value event carries at least one payload; control events are unrestricted. -/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.NonemptyValues
    : WorkQueueEvent → Prop
  | .groupValues _ values | .streamValues _ values _ _ => values ≠ []
  | _ => True

/-- A source item arrival contains an item; other source constructors are unrestricted. -/
def GraphEvent.NonemptyItems : GraphEvent → Prop
  | .streamItems _ items => items ≠ []
  | _ => True

/-- Source readiness already excludes empty item-arrival events.
Witness: the nonempty item-list clause in `GraphEvent.Ready`, lifted through the prefix.
-/
theorem ValidGraphEvents.nonemptyItems {work events}
    (valid : ValidGraphEvents work events)
    : ∀ event ∈ events, event.NonemptyItems := by
  induction valid with
  | nil => simp
  | @append before event valid matching fresh ready ih =>
      intro next member
      rcases List.mem_append.mp member with earlier | latest
      · exact ih next earlier
      · have same := List.mem_singleton.mp latest
        subst next
        cases event <;> try trivial
        obtain ⟨_, _, _, _, _, nonempty, _⟩ := ready
        exact nonempty

/-- A group flush omits its value event when no stored values were selected.
Witness: the exact selected-node output equation and its `isEmpty` branch. -/
theorem State.finishGroupSuccess_nonemptyValues (queue : State) (group : GroupNode)
    : ∀ event ∈ (queue.finishGroupSuccess group).2.1, event.NonemptyValues := by
  obtain ⟨selected, _, _, events, _, _⟩ := queue.finishGroupSuccess_publications group
  rw [events]
  split
  · simp [WorkQueueEvent.NonemptyValues]
  · rename_i nonempty
    simp only [List.isEmpty_iff] at nonempty
    simpa [WorkQueueEvent.NonemptyValues] using nonempty

/-- Every value event emitted during recursive draining is nonempty.
Witness: each successful flush checks its selected values; cached failures contain only
control events, and induction preserves the property through later drain steps.
-/
theorem State.drainReadyGroups_nonemptyValues (queue : State)
    : ∀ event ∈ queue.drainReadyGroups.2, event.NonemptyValues := by
  have loop (fuel : Nat) (current : State)
      : ∀ event ∈ (State.drainReadyGroups.go fuel current).2, event.NonemptyValues := by
    induction fuel generalizing current with
    | zero => simp [State.drainReadyGroups.go]
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · simp
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              intro event member
              rcases List.mem_append.mp member with first | later
              · exact current.finishGroupSuccess_nonemptyValues node event first
              · exact ih _ event later
          | some errors =>
              intro event member
              rcases List.mem_append.mp member with first | later
              · have same := List.mem_singleton.mp first
                subst event
                trivial
              · exact ih _ event later
  exact loop _ queue

/-- Every value event released by task success is nonempty.
Witness: the contributor fold and final recursive drain append only checked group flushes. -/
theorem State.taskSuccess_nonemptyValues (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : ∀ event ∈ (queue.taskSuccess occurrence result).2, event.NonemptyValues := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (prior : ∀ event ∈ acc.2.1, event.NonemptyValues)
      : ∀ event ∈ (groups.foldl successGroupStep acc).2.1, event.NonemptyValues := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact prior
        · split
          · intro event member
            rcases List.mem_append.mp member with earlier | latest
            · exact prior event earlier
            · exact State.finishGroupSuccess_nonemptyValues _ _ event latest
          · exact prior
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · simp
      intro event member
      rcases List.mem_append.mp member with first | later
      · exact loop _ (_, [], {}) (by simp) event first
      · exact State.drainReadyGroups_nonemptyValues _ event later

/-- Task failure emits only control events, so the nonempty-value property is preserved.
Witness: the owner fold either emits group failure or caches an unannounced group's errors.
-/
theorem State.taskFailure_nonemptyValues (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : ∀ event ∈ (queue.taskFailure occurrence errors).2, event.NonemptyValues := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : ∀ event ∈ acc.2, event.NonemptyValues)
      : ∀ event ∈ (groups.foldl step acc).2, event.NonemptyValues := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        unfold step
        split
        · exact prior
        · split
          · intro event member
            rcases List.mem_append.mp member with earlier | latest
            · exact prior event earlier
            · have same := List.mem_singleton.mp latest
              subst event
              trivial
          · exact prior
  unfold State.taskFailure
  split
  · simp
  · split
    · simp
    exact loop _ (_, []) (by simp)

/-- A nonempty item arrival cannot produce an empty stream-value event.
Witness: exact item copying excludes an empty accumulator; the final group drain preserves
nonempty values independently.
-/
theorem State.streamItems_nonemptyValues (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (nonempty : items ≠ [])
    : ∀ event ∈ (queue.streamItems stream items).2, event.NonemptyValues := by
  by_cases active : queue.rootStreams.contains stream.ref = true
  · have exactItems := queue.streamItems_itemValues stream items active
    simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ite_false]
    intro event member
    rcases List.mem_cons.mp member with same | later
    · subst event
      intro empty
      simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ite_false,
        List.flatMap_cons, WorkQueueEvent.itemValues, State.drainReadyGroups_itemValues,
        List.append_nil] at exactItems
      rw [empty] at exactItems
      have lengths := congrArg List.length exactItems
      simp only [List.map_nil, List.length_nil, List.length_map,
        GraphEvent.itemPublications] at lengths
      cases items with
      | nil => exact nonempty rfl
      | cons item rest => simp at lengths
    · exact State.drainReadyGroups_nonemptyValues _ event later
  · have inactive : queue.rootStreams.contains stream.ref = false := Bool.eq_false_iff.mpr active
    simp only [State.streamItems, inactive, Bool.not_false, ite_true, List.not_mem_nil,
      false_implies, implies_true]

/-- Legal item-list shapes suffice for every handler's nonempty-value property.
Witness: task/stream handler lemmas; stream closures contain no value list. -/
theorem State.handleGraphEvent_nonemptyValues (queue : State) (event : GraphEvent)
    (nonempty : event.NonemptyItems)
    : ∀ output ∈ (queue.handleGraphEvent event).2, output.NonemptyValues := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_nonemptyValues occurrence result
  | taskFailure occurrence errors =>
      exact queue.taskFailure_nonemptyValues occurrence errors
  | streamItems stream items =>
      exact queue.streamItems_nonemptyValues stream items nonempty
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [WorkQueueEvent.NonemptyValues]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [WorkQueueEvent.NonemptyValues]

/-- Eventwise replay preserves nonempty raw payloads without any queue-state premise.
Witness: concatenate each handler's shape result through the actual queue fold. -/
theorem State.rawEventReplay_nonemptyValues (queue : State) (events : List GraphEvent)
    (nonempty : ∀ event ∈ events, event.NonemptyItems)
    : ∀ output ∈ (queue.rawEventReplay events).2, output.NonemptyValues := by
  induction events generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      intro output member
      rcases List.mem_append.mp member with first | later
      · exact queue.handleGraphEvent_nonemptyValues event (nonempty _ List.mem_cons_self)
          output first
      · exact ih _ (fun next member => nonempty next (List.mem_cons_of_mem _ member)) output later

/-- Batch termination adds only a control event; earlier termination returns no output.
Witness: the exact batch/eventwise replay equation and the handler shape invariant. -/
theorem State.handleGraphEvents_nonemptyValues (queue : State) (events : List GraphEvent)
    (nonempty : ∀ event ∈ events, event.NonemptyItems)
    : ∀ output ∈ (queue.handleGraphEvents events).2, output.NonemptyValues := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · simp
  · dsimp only
    split
    · intro output member
      rcases List.mem_append.mp member with earlier | latest
      · exact queue.rawEventReplay_nonemptyValues events nonempty output earlier
      · have same := List.mem_singleton.mp latest
        subst output
        trivial
    · exact queue.rawEventReplay_nonemptyValues events nonempty

-----------------------------------------------------------------------------------------
-- Publisher normalization retains nonempty output batches and value lists
-----------------------------------------------------------------------------------------

/-- A raw event with nonempty values normalizes to a nonempty list of well-shaped events.
Witness: object values become singleton events; stream values retain their nonempty map;
control events remain singletons. -/
theorem IncrementalPublisher.handleWorkQueueEvent_nonemptyValues
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    (nonempty : event.NonemptyValues)
    : (publisher.handleWorkQueueEvent event).2 ≠ []
      ∧ ∀ output ∈ (publisher.handleWorkQueueEvent event).2, NonemptyValues output := by
  cases event <;> simp_all [IncrementalPublisher.handleWorkQueueEvent,
    NonemptyValues, WorkQueueEvent.NonemptyValues]

/-- Publisher batch normalization preserves value shape and cannot erase a nonempty batch.
Witness: the actual fold appends a nonempty normalized list for every retained raw event.
-/
theorem IncrementalPublisher.normalizeBatch_nonemptyValues
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    (nonempty : ∀ event ∈ events, event.NonemptyValues)
    : ((publisher.normalizeBatch events).2 = [] ↔ events = [])
      ∧ ∀ output ∈ (publisher.normalizeBatch events).2, NonemptyValues output := by
  let step (acc : IncrementalPublisher × List Execution.WorkQueueEvent) (event : WorkQueueEvent) :=
    let (next, produced) := acc.1.handleWorkQueueEvent event
    (next, acc.2 ++ produced)
  have loop (more : List WorkQueueEvent) (acc : IncrementalPublisher × List Execution.WorkQueueEvent)
      (shape : ∀ event ∈ more, event.NonemptyValues)
      (prior : ∀ event ∈ acc.2, NonemptyValues event)
      : ((more.foldl step acc).2 = [] ↔ acc.2 = [] ∧ more = [])
        ∧ ∀ output ∈ (more.foldl step acc).2, NonemptyValues output := by
    induction more generalizing acc with
    | nil => simpa using prior
    | cons event rest ih =>
        have current := acc.1.handleWorkQueueEvent_nonemptyValues event
          (shape event List.mem_cons_self)
        have checked : ∀ output ∈ (step acc event).2, NonemptyValues output := by
          intro output member
          rcases List.mem_append.mp member with old | latest
          · exact prior output old
          · exact current.2 output latest
        obtain ⟨empty, shaped⟩ := ih (step acc event)
          (fun next member => shape next (List.mem_cons_of_mem _ member)) checked
        refine ⟨?_, shaped⟩
        rw [List.foldl_cons, empty]
        simp [step, current.1]
  unfold IncrementalPublisher.normalizeBatch
  simpa only [true_and] using loop events (publisher, []) nonempty (by simp)

/-- Actual replay has nonempty normalized batches and nonempty payload lists.
Witness: source readiness, handler shape preservation, and the normalized batch fold.
No generated-work metadata, start law, or abstract output-admission premise is needed. -/
theorem createWorkQueue_runNormalized_nonemptyValues {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      (∀ batch ∈ outputs, batch ≠ [])
      ∧ ∀ event ∈ outputs.flatten, NonemptyValues event := by
  have step (acc : NormalizedAcc) (batch : List GraphEvent)
      (shape : ∀ event ∈ batch, event.NonemptyItems)
      (prior : (∀ outputBatch ∈ acc.2.2, outputBatch ≠ [])
        ∧ ∀ event ∈ acc.2.2.flatten, NonemptyValues event)
      : (∀ outputBatch ∈ (normalizedStep acc batch).2.2, outputBatch ≠ [])
        ∧ ∀ event ∈ (normalizedStep acc batch).2.2.flatten, NonemptyValues event := by
    obtain ⟨queue, publisher, outputs⟩ := acc
    have rawShape := queue.handleGraphEvents_nonemptyValues batch shape
    have mapped := publisher.normalizeBatch_nonemptyValues _ rawShape
    dsimp only [normalizedStep]
    split
    · exact prior
    · rename_i rawNonempty
      have retained : (publisher.normalizeBatch (queue.handleGraphEvents batch).2).2 ≠ [] := by
        intro empty
        exact rawNonempty (List.isEmpty_iff.mpr (mapped.1.mp empty))
      constructor
      · intro outputBatch member
        rcases List.mem_append.mp member with earlier | latest
        · exact prior.1 outputBatch earlier
        · exact List.mem_singleton.mp latest ▸ retained
      · intro event member
        simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.mem_append] at member
        rcases member with earlier | latest
        · exact prior.2 event earlier
        · exact mapped.2 event latest
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (shape : ∀ event ∈ more.flatten, event.NonemptyItems)
      (prior : (∀ batch ∈ acc.2.2, batch ≠ [])
        ∧ ∀ event ∈ acc.2.2.flatten, NonemptyValues event)
      : (∀ batch ∈ (more.foldl normalizedStep acc).2.2, batch ≠ [])
        ∧ ∀ event ∈ (more.foldl normalizedStep acc).2.2.flatten, NonemptyValues event := by
    induction more generalizing acc with
    | nil => exact prior
    | cons batch rest ih =>
        have first : ∀ event ∈ batch, event.NonemptyItems := by
          intro event member
          exact shape event (List.mem_flatten.mpr ⟨batch, List.mem_cons_self, member⟩)
        exact ih (normalizedStep acc batch)
          (fun event member =>
            shape event
              (by simp only [List.flatten_cons, List.mem_append]
                  exact Or.inr member))
          (step acc batch first prior)
  exact loop batches (_, _, []) valid.nonemptyItems (by simp)

/-- Actual normalized output has an exact singleton-publication batching witness.
Witness: derived nonempty output shape and the independent value-splitting construction.
This does not yet prove that those atoms satisfy `EventAllowed`. -/
theorem createWorkQueue_runNormalized_atomicBatching {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      WorkBatching (outputs.flatten.flatMap publicationAtoms) outputs := by
  obtain ⟨nonempty, shape⟩ := createWorkQueue_runNormalized_nonemptyValues valid
  exact publicationAtoms_batching _ nonempty shape

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
