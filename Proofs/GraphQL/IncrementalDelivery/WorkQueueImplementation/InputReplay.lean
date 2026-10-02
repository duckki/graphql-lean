import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceObservation

/-! State projections and start checks for executable source-event and batch replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Replay source events through the executable queue while forgetting raw
work-event output. This is proof-side notation for the queue's state fold. -/
def State.replayGraphEvents (queue : State) (events : List GraphEvent) : State :=
  events.foldl (fun current event => (current.handleGraphEvent event).1) queue

/-- Appending one source event performs exactly one further queue handler step.
Witness: the list-fold concatenation equation. -/
theorem State.replayGraphEvents_append (queue : State)
    (before : List GraphEvent) (event : GraphEvent)
    : queue.replayGraphEvents (before ++ [event])
      = ((queue.replayGraphEvents before).handleGraphEvent event).1 := by
  simp [State.replayGraphEvents, List.foldl_append]

/-- A recursive view of the existing `inputsStarted` fold, used only to make
its per-batch conditions available to induction proofs. -/
def State.batchesStarted : State → List (List GraphEvent) → Bool
  | _, [] => true
  | queue, batch :: rest =>
      let next := (queue.handleGraphEvents batch).1
      !queue.terminated
      && !batch.isEmpty
      && queue.acceptsBatch batch
      && next.batchesStarted rest

/-- The recursive view computes exactly the Boolean validity component of
the implementation's batch fold. -/
private theorem State.fold_started_eq
    (queue : State) (valid : Bool) (batches : List (List GraphEvent))
    : (batches.foldl
        (fun (state, good) batch =>
          let next := (state.handleGraphEvents batch).1
          (next, good && !state.terminated && !batch.isEmpty && state.acceptsBatch batch))
        (queue, valid)).2
      = (valid && queue.batchesStarted batches) := by
  induction batches generalizing queue valid with
  | nil => simp [State.batchesStarted]
  | cons batch rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [State.batchesStarted, Bool.and_assoc]

/-- The public start-discipline checker is the recursive predicate at the
generated queue's initial state. -/
theorem inputsStarted_eq_batchesStarted
    (work : Execution.Work) (batches : List (List GraphEvent))
    : inputsStarted work batches
      = (State.initialize (Work.fromExecution work)).batchesStarted batches := by
  unfold inputsStarted
  rw [State.fold_started_eq]
  simp

/-- The work-event accumulator does not affect the executable queue-state
projection of one batch's event fold. -/
theorem State.foldGraphEvents_state
    (queue : State) (outputs : List WorkQueueEvent)
    (events : List GraphEvent)
    : (events.foldl
        (fun (current, accumulated) event =>
          let (next, produced) := current.handleGraphEvent event
          (next, accumulated ++ produced))
        (queue, outputs)).1
      = queue.replayGraphEvents events := by
  induction events generalizing queue outputs with
  | nil => rfl
  | cons event rest ih =>
      simp only [List.foldl_cons, State.replayGraphEvents]
      exact ih (queue.handleGraphEvent event).1
        (outputs ++ (queue.handleGraphEvent event).2)

/-- A true recursive batch check exposes the current batch's start checks
and the remaining batch suffix's check. -/
theorem State.batchesStarted_cons
    (queue : State) (batch : List GraphEvent)
    (rest : List (List GraphEvent))
    (valid : queue.batchesStarted (batch :: rest) = true)
    : queue.terminated = false
      ∧ queue.acceptsBatch batch = true
      ∧ ((queue.handleGraphEvents batch).1).batchesStarted rest = true := by
  simp [State.batchesStarted] at valid
  exact ⟨valid.1.1.1, valid.1.2, valid.2⟩

/-- Publisher normalization never changes the queue-state projection of a
batch replay. Thus state accounting may be proved before wire mapping. -/
theorem State.runNormalized_stateFold (queue : State) (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1
      = batches.foldl (fun current batch => (current.handleGraphEvents batch).1)
          queue := by
  have stepState (acc : NormalizedAcc) (batch : List GraphEvent)
      : (normalizedStep acc batch).1 =
          (acc.1.handleGraphEvents batch).1 := by
    obtain ⟨current, publisher, outputs⟩ := acc
    simp only [normalizedStep]
    split <;> rfl
  have foldState (more : List (List GraphEvent)) (acc : NormalizedAcc)
      : (more.foldl normalizedStep acc).1 =
          more.foldl (fun current batch => (current.handleGraphEvents batch).1)
            acc.1 := by
    induction more generalizing acc with
    | nil => rfl
    | cons batch rest ih =>
        simp only [List.foldl_cons]
        rw [ih, stepState]
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  change (batches.foldl normalizedStep (queue, publisher, [])).1 = _
  exact foldState batches (queue, publisher, [])

-----------------------------------------------------------------------------------------
-- Started batches agree with event replay, except for the final control flag
-----------------------------------------------------------------------------------------

/-- A sequential trace records only the start check that the executable
queue performs immediately before each graph event. -/
private inductive AcceptedTrace : State → List GraphEvent → Prop where
  | nil (queue : State) : AcceptedTrace queue []
  | cons {queue : State} {event : GraphEvent} {rest : List GraphEvent}
    (accepted : queue.acceptsGraphEvent event = true)
    (tail : AcceptedTrace (queue.handleGraphEvent event).1 rest)
    : AcceptedTrace queue (event :: rest)

/-- The executable batch-start checker is equivalent to an eventwise accepted
trace in its forward direction. -/
private theorem State.acceptsBatch_trace
    (queue : State) (events : List GraphEvent)
    (accepted : queue.acceptsBatch events = true)
    : AcceptedTrace queue events := by
  induction events generalizing queue with
  | nil => exact .nil queue
  | cons event rest ih =>
      have both : queue.acceptsGraphEvent event = true
          ∧ ((queue.handleGraphEvent event).1).acceptsBatch rest = true := by
        simpa [State.acceptsBatch] using accepted
      exact .cons both.1 (ih (queue.handleGraphEvent event).1 both.2)

/-- Accepted traces concatenate when the second trace starts at the first
trace's executable final queue state. -/
theorem AcceptedTrace.append
    {queue : State} {first second : List GraphEvent}
    (left : AcceptedTrace queue first)
    (right : AcceptedTrace (queue.replayGraphEvents first) second)
    : AcceptedTrace queue (first ++ second) := by
  induction left generalizing second with
  | nil queue =>
      simpa [State.replayGraphEvents] using right
  | @cons queue event rest accepted tail ih =>
      simpa [State.replayGraphEvents] using AcceptedTrace.cons accepted (ih right)

/-- Accepted-event traces are prefix closed. -/
theorem AcceptedTrace.prefix
    {queue : State} {events before : List GraphEvent}
    (trace : AcceptedTrace queue events) (earlier : before.IsPrefix events)
    : AcceptedTrace queue before := by
  induction trace generalizing before with
  | nil queue =>
      have empty : before = [] := by
        have length := earlier.length_le
        simp at length
        exact length
      subst before
      exact .nil queue
  | @cons queue event rest accepted tail ih =>
      cases before with
      | nil => exact .nil queue
      | cons first remaining =>
          obtain ⟨suffix, same⟩ := earlier
          have parts : first = event ∧ remaining ++ suffix = rest := by
            simpa using List.cons.inj same
          rcases parts with ⟨rfl, tailEq⟩
          exact .cons accepted (ih ⟨suffix, tailEq⟩)

/-- In an accepted trace, the last event is accepted after replaying exactly
the events before it. -/
private theorem AcceptedTrace.lastAccepted
    {queue : State} {before : List GraphEvent} {event : GraphEvent}
    (trace : AcceptedTrace queue (before ++ [event]))
    : (queue.replayGraphEvents before).acceptsGraphEvent event = true := by
  induction before generalizing queue with
  | nil =>
      cases trace with
      | cons accepted tail => simpa [State.replayGraphEvents] using accepted
  | cons first rest ih =>
      cases trace with
      | cons accepted tail =>
          simpa [State.replayGraphEvents] using ih tail

/-- Prefix closure and the last-event lemma expose the acceptance fact at
any event position in a complete accepted trace. -/
private theorem AcceptedTrace.acceptedAt
    {queue : State} {events before : List GraphEvent} {event : GraphEvent}
    (trace : AcceptedTrace queue events)
    (earlier : (before ++ [event]).IsPrefix events)
    : (queue.replayGraphEvents before).acceptsGraphEvent event = true :=
  (trace.prefix earlier).lastAccepted

/-- One open batch changes exactly the sequentially replayed queue state,
apart from the final termination flag. The raw-event accumulator has no
effect on any task, group, or stream bookkeeping. -/
theorem State.handleGraphEvents_stateCore
    (queue : State) (events : List GraphEvent)
    (startOpen : queue.terminated = false)
    : ∃ terminal : Bool,
        (queue.handleGraphEvents events).1
        = { queue.replayGraphEvents events with terminated := terminal } := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have folded : (events.foldl step (queue, [])).1 =
      queue.replayGraphEvents events := queue.foldGraphEvents_state [] events
  cases outcome : events.foldl step (queue, []) with
  | mk current outputs =>
      rw [outcome] at folded
      dsimp only at folded
      cases empty : current.rootGroups.isEmpty && current.rootStreams.isEmpty with
      | true =>
          refine ⟨true, ?_⟩
          change (if queue.terminated then (queue, []) else
              match events.foldl step (queue, []) with
              | (current, outputs) =>
                  if current.rootGroups.isEmpty && current.rootStreams.isEmpty then
                    ({ current with terminated := true },
                      outputs ++ [.workQueueTermination])
                  else (current, outputs)).1 =
            { queue.replayGraphEvents events with terminated := true }
          simp only [startOpen, Bool.false_eq_true, ite_false, outcome]
          rw [← folded]
          simp [empty]
      | false =>
          refine ⟨current.terminated, ?_⟩
          change (if queue.terminated then (queue, []) else
              match events.foldl step (queue, []) with
              | (current, outputs) =>
                  if current.rootGroups.isEmpty && current.rootStreams.isEmpty then
                    ({ current with terminated := true },
                      outputs ++ [.workQueueTermination])
                  else (current, outputs)).1 =
            { queue.replayGraphEvents events with terminated := current.terminated }
          simp only [startOpen, Bool.false_eq_true, ite_false, outcome]
          rw [← folded]
          simp [empty]

/-- Before termination, a batch handler has exactly the state obtained by
sequentially replaying its graph events. Termination only toggles its flag. -/
theorem State.handleGraphEvents_nonterminalState
    (queue : State) (events : List GraphEvent)
    (startOpen : queue.terminated = false)
    (endOpen : (queue.handleGraphEvents events).1.terminated = false)
    : (queue.handleGraphEvents events).1 = queue.replayGraphEvents events := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have folded : (events.foldl step (queue, [])).1 =
      queue.replayGraphEvents events :=
    queue.foldGraphEvents_state [] events
  change (if queue.terminated then (queue, []) else
      match events.foldl step (queue, []) with
      | (current, outputs) =>
          if current.rootGroups.isEmpty && current.rootStreams.isEmpty then
            ({ current with terminated := true },
              outputs ++ [.workQueueTermination])
          else (current, outputs)).1.terminated = false at endOpen
  change (if queue.terminated then (queue, []) else
      match events.foldl step (queue, []) with
      | (current, outputs) =>
          if current.rootGroups.isEmpty && current.rootStreams.isEmpty then
            ({ current with terminated := true },
              outputs ++ [.workQueueTermination])
          else (current, outputs)).1 = queue.replayGraphEvents events
  cases outcome : events.foldl step (queue, []) with
  | mk current outputs =>
      rw [outcome] at folded
      dsimp only at folded
      simp only [startOpen, Bool.false_eq_true, ite_false]
      cases empty : current.rootGroups.isEmpty && current.rootStreams.isEmpty with
      | true => simp [startOpen, outcome, empty] at endOpen
      | false => simpa [empty] using folded

/-- For host batches accepted by the start checker, the queue state used by
the public adapter is sequential graph-event replay with only its terminal
flag possibly changed. A terminal batch cannot have a later accepted batch. -/
theorem State.runNormalized_stateCore (queue : State)
    (batches : List (List GraphEvent))
    (started : queue.batchesStarted batches = true)
    : ∃ terminal : Bool,
        (queue.runNormalized batches).1
        = { queue.replayGraphEvents batches.flatten with terminated := terminal } := by
  induction batches generalizing queue with
  | nil =>
      refine ⟨queue.terminated, ?_⟩
      simp [State.runNormalized_stateFold, State.replayGraphEvents]
  | cons batch rest ih =>
      obtain ⟨startOpen, _, restStarted⟩ :=
        queue.batchesStarted_cons batch rest started
      let next := (queue.handleGraphEvents batch).1
      cases rest with
      | nil =>
          obtain ⟨terminal, same⟩ :=
            queue.handleGraphEvents_stateCore batch startOpen
          refine ⟨terminal, ?_⟩
          rw [queue.runNormalized_stateFold]
          simpa [State.replayGraphEvents, next] using same
      | cons later tail =>
          have nextOpen : next.terminated = false :=
            (next.batchesStarted_cons later tail restStarted).1
          have same : next = queue.replayGraphEvents batch :=
            queue.handleGraphEvents_nonterminalState batch startOpen nextOpen
          obtain ⟨terminal, restSame⟩ :=
            ih next restStarted
          refine ⟨terminal, ?_⟩
          rw [queue.runNormalized_stateFold]
          simpa [next, same, State.runNormalized_stateFold,
            State.replayGraphEvents, List.foldl_append] using restSame

/-- Every input admitted by the public start-discipline checker forms one
sequentially accepted graph-event trace after flattening its batches. -/
private theorem State.batchesStarted_trace
    (queue : State) (batches : List (List GraphEvent))
    (valid : queue.batchesStarted batches = true)
    : AcceptedTrace queue batches.flatten := by
  induction batches generalizing queue with
  | nil => exact .nil queue
  | cons batch rest ih =>
      obtain ⟨startOpen, batchAccepted, restStarted⟩ :=
        queue.batchesStarted_cons batch rest valid
      have firstTrace : AcceptedTrace queue batch :=
        queue.acceptsBatch_trace batch batchAccepted
      cases rest with
      | nil =>
          simpa using firstTrace
      | cons nextBatch later =>
          let next := (queue.handleGraphEvents batch).1
          have nextOpen : next.terminated = false :=
            (next.batchesStarted_cons nextBatch later restStarted).1
          have same : next = queue.replayGraphEvents batch :=
            queue.handleGraphEvents_nonterminalState batch startOpen nextOpen
          have tailTrace : AcceptedTrace next (nextBatch :: later).flatten :=
            ih next restStarted
          rw [same] at tailTrace
          simpa using firstTrace.append tailTrace

/-- Started batches license every flattened input at its actual sequential state.
Witness: the accepted-trace bridge and the recursive batch acceptance equation.
This does not require a batch to remain nonterminal after its final event.
-/
theorem State.batchesStarted_acceptsBatch (queue : State)
    (batches : List (List GraphEvent)) (started : queue.batchesStarted batches = true)
    : queue.acceptsBatch batches.flatten = true := by
  have all {current events} (trace : AcceptedTrace current events)
      : current.acceptsBatch events = true := by
    induction trace with
    | nil => rfl
    | cons accepted _ ih =>
        simpa only [State.acceptsBatch, Bool.and_eq_true] using And.intro accepted ih
  exact all (queue.batchesStarted_trace batches started)

/-- The public source start-discipline clause supplies the precise
event-by-event acceptance premise of the replay accounting theorem. -/
theorem inputsStarted_eachAccepted
    (work : Execution.Work) (batches : List (List GraphEvent))
    (started : inputsStarted work batches = true)
    (before : List GraphEvent) (event : GraphEvent)
    (earlier : (before ++ [event]).IsPrefix batches.flatten)
    : (((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).acceptsGraphEvent
        event)
      = true := by
  have recursive : (State.initialize (Work.fromExecution work)).batchesStarted batches = true := by
    rw [← inputsStarted_eq_batchesStarted]
    exact started
  have trace := (State.initialize (Work.fromExecution work)).batchesStarted_trace
    batches recursive
  exact trace.acceptedAt earlier

/-- Accepted normalized replay agrees with eventwise replay except for termination.
Witness: the recursive start-checker bridge and the normalized queue-state equation. -/
theorem createWorkQueue_runNormalized_stateCore
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (started : inputsStarted work batches = true)
    : ∃ terminal : Bool,
        ((State.initialize (Work.fromExecution work)).runNormalized batches).1
        = {
          (State.initialize (Work.fromExecution work)).replayGraphEvents
              batches.flatten with
            terminated := terminal
        } := by
  rw [inputsStarted_eq_batchesStarted] at started
  exact State.runNormalized_stateCore _ batches started

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
