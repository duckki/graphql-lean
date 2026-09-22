import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationInventory

/-! Fresh object publication across event handlers and actual queue batches. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Exact input provenance makes source freshness available to the publication ledger
-----------------------------------------------------------------------------------------

/-- The payload was supplied by a task-success input at this exact occurrence.
The input prefix is observed history, not a selected future schedule. -/
def ObjectValueFrom (inputs : List GraphEvent) (occurrence : Occurrence)
    (value : ExecutionGroupValue)
    : Prop :=
  ∃ result, .taskSuccess occurrence result ∈ inputs ∧ result.value = value

/-- An earlier input remains a payload witness after additional inputs arrive.
Witness: membership inclusion retains the same task-success event and exact value. -/
theorem ObjectValueFrom.mono {before after occurrence value}
    (source : ObjectValueFrom before occurrence value) (included : before.Subset after)
    : ObjectValueFrom after occurrence value := by
  obtain ⟨result, member, same⟩ := source
  exact ⟨result, included member, same⟩

/-- A source-witnessed object occurrence is in the input prefix's identity list.
Witness: the supplying task-success event contributes exactly that occurrence. -/
theorem ObjectValueFrom.identity {inputs occurrence value}
    (source : ObjectValueFrom inputs occurrence value)
    : occurrence ∈ inputs.flatMap (fun event => event.identities.1) := by
  obtain ⟨result, member, _⟩ := source
  exact List.mem_flatMap.mpr ⟨_, member, List.mem_cons_self⟩

/-- Every event at an admitted input boundary has the source's exact local laws.
Witness: prefix induction in the append-style source derivation. -/
theorem ValidGraphEvents.atPrefix {work events} (valid : ValidGraphEvents work events)
    {before event} (earlier : (before ++ [event]).IsPrefix events)
    : event.MatchesWork work ∧ event.Fresh before ∧ event.Ready work before := by
  induction valid with
  | nil =>
      have empty := List.eq_nil_of_prefix_nil earlier
      simp at empty
  | @append prior last validPrior matching fresh ready ih =>
      rcases List.prefix_concat_iff.mp earlier with same | shorter
      · obtain ⟨sameBefore, sameLast⟩ := List.append_inj' same rfl
        have sameEvent := List.singleton_inj.mp sameLast
        subst before event
        exact ⟨matching, fresh, ready⟩
      · exact ih shorter

/-- A fresh task-success input has not previously published under another owner's flush.
Witness: every published occurrence has an earlier input witness, excluded by source
freshness. This does not require the old task node to remain absent or unstarted. -/
theorem State.PublicationInventory.fresh_success {queue : State}
    {before published occurrence result}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    : occurrence ∉ published.map Prod.fst := by
  intro member
  obtain ⟨publication, publishedMember, same⟩ := List.mem_map.mp member
  exact fresh.2.2.1 occurrence List.mem_cons_self
    (same ▸ (inventory.provenance publication publishedMember).identity)

-----------------------------------------------------------------------------------------
-- Replay the exact event fold used inside handleGraphEvents, before batch termination
-----------------------------------------------------------------------------------------

/-- Proof notation for `handleGraphEvents`' actual event-fold step, retaining raw output. -/
def rawEventStep (acc : State × List WorkQueueEvent) (event : GraphEvent)
    : State × List WorkQueueEvent :=
  let (next, produced) := acc.1.handleGraphEvent event
  (next, acc.2 ++ produced)

/-- The actual event-processing fold, before the outer batch's termination check.
This proof helper retains output that `replayGraphEvents` intentionally forgets. -/
def State.rawEventReplay (queue : State) (events : List GraphEvent)
    : State × List WorkQueueEvent :=
  events.foldl rawEventStep (queue, [])

/-- Earlier accumulated output is prepended without changing replay state or later output.
Witness: fold induction and associativity of raw-event concatenation. -/
theorem rawEventReplay_accumulator (queue : State) (events : List GraphEvent)
    (output : List WorkQueueEvent)
    : events.foldl rawEventStep (queue, output)
      = ((queue.rawEventReplay events).1, output ++ (queue.rawEventReplay events).2) := by
  induction events generalizing queue output with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      simp only [State.rawEventReplay, List.foldl_cons, rawEventStep, List.nil_append]
      rw [ih _ (output ++ (queue.handleGraphEvent event).2),
        ih _ (queue.handleGraphEvent event).2]
      simp only [List.append_assoc]

/-- Eventwise replay processes the head input, then its continuation in the updated state.
Witness: the exact fold accumulator equation, preserving all raw output order. -/
theorem State.rawEventReplay_cons (queue : State) (event : GraphEvent)
    (rest : List GraphEvent)
    : queue.rawEventReplay (event :: rest)
      = let current := queue.handleGraphEvent event
        let next := current.1.rawEventReplay rest
        (next.1, current.2 ++ next.2) := by
  simp only [State.rawEventReplay, List.foldl_cons, rawEventStep, List.nil_append]
  exact rawEventReplay_accumulator _ _ _

/-- Retaining raw output does not alter eventwise queue state.
Witness: induction through the same executable handlers in both folds. -/
theorem State.rawEventReplay_state (queue : State) (events : List GraphEvent)
    : (queue.rawEventReplay events).1 = queue.replayGraphEvents events := by
  induction events generalizing queue with
  | nil => rfl
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      exact ih _

/-- A legal input continuation extends an exact, occurrence-unique object publication ledger.
Witness: each handler extends the ledger; source freshness prevents installing an already
published occurrence, and prior empty-node reactivation cannot restore a stored value. -/
theorem State.PublicationInventory.rawEventReplay {queue : State} {work before published}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.rawEventReplay events).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.rawEventReplay events).1.PublicationInventory
            (ObjectValueFrom (before ++ events)) (published ++ added) := by
  induction events generalizing queue before published with
  | nil =>
      refine ⟨[], rfl, ?_⟩
      simpa only [List.append_nil, State.rawEventReplay, List.foldl_nil] using inventory
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      have eventLaws := valid.atPrefix earlier
      have current := inventory.mono (fun _ _ source =>
        source.mono (List.subset_append_left before [event]))
      obtain ⟨first, values, after⟩ := current.handleGraphEvent event (by
        intro occurrence result same
        subst event
        exact ⟨⟨result, List.mem_append_right _ List.mem_cons_self, rfl⟩,
          inventory.fresh_success eventLaws.2.1⟩)
      obtain ⟨later, laterValues, final⟩ := ih after (by
        simpa only [List.append_assoc, List.singleton_append] using valid)
      refine ⟨first ++ later, ?_, ?_⟩
      · rw [State.rawEventReplay_cons, List.map_append]
        simp only [List.flatMap_append, ← values, ← laterValues]
      · rw [State.rawEventReplay_cons]
        simpa only [List.append_assoc, List.singleton_append] using final

/-- Actual queue creation followed by legal input replay publishes each object occurrence
at most once. Witness: start with no stored or published values, then apply the general
continuation inventory. No output-admission or generated-work premise is assumed. -/
theorem createWorkQueue_rawEventReplay_publications {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    : ∃ published : List ObjectPublication,
        published.map Prod.snd
          = ((State.initialize (Work.fromExecution work)).rawEventReplay events).2.flatMap
              WorkQueueEvent.objectValues
        ∧ ((State.initialize (Work.fromExecution work)).rawEventReplay
            events).1.PublicationInventory
            (ObjectValueFrom events) published := by
  have initial : (State.initialize (Work.fromExecution work)).PublicationInventory
      (ObjectValueFrom []) [] :=
    ⟨by simp, by simp, createWorkQueue_storedValues _ _⟩
  simpa only [List.nil_append] using initial.rawEventReplay events valid

-----------------------------------------------------------------------------------------
-- The actual batch wrapper preserves the same publication witness
-----------------------------------------------------------------------------------------

/-- The public batch handler is exactly raw replay plus its start/termination branches.
Witness: unfold the proof helper; its fold step is the implementation's original step. -/
theorem State.handleGraphEvents_eq_rawEventReplay (queue : State)
    (events : List GraphEvent)
    : queue.handleGraphEvents events
      = if queue.terminated then
          (queue, [])
        else
          let current := queue.rawEventReplay events
          if current.1.rootGroups.isEmpty && current.1.rootStreams.isEmpty then
            ({ current.1 with terminated := true }, current.2 ++ [.workQueueTermination])
          else
            current := by
  rfl

/-- Batch handling publishes fresh object occurrences even with empty output or termination.
Witness: eventwise freshness; the outer wrapper only suppresses work after termination
or appends a control event. Neither branch fabricates or duplicates an object value. -/
theorem State.PublicationInventory.handleGraphEvents {queue : State}
    {work before published}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.handleGraphEvents events).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.handleGraphEvents events).1.PublicationInventory
            (ObjectValueFrom (before ++ events)) (published ++ added) := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · refine ⟨[], rfl, ?_⟩
    simpa only [List.append_nil] using inventory.mono
      (fun _ _ source => source.mono (List.subset_append_left before events))
  · obtain ⟨added, values, final⟩ := inventory.rawEventReplay events valid
    dsimp only
    split
    · refine ⟨added, ?_, final.unique, final.provenance, final.stored⟩
      simpa only [List.flatMap_append, List.flatMap_singleton, WorkQueueEvent.objectValues,
        List.append_nil] using values
    · exact ⟨added, values, final⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
