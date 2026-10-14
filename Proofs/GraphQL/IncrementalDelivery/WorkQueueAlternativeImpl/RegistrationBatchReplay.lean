import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationDispatch
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape

/-! Generated batched dispatch, including the terminal accounting projection. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- Accepted prefixes supply the single-event bridge inside a batch
-----------------------------------------------------------------------------------------

/-- Sequential acceptance concatenates at the actual state reached by the first trace. -/
theorem reference_acceptsBatch_append (queue : ReferenceWorkQueue.State)
    (before after : List GraphEvent)
    : queue.acceptsBatch (before ++ after)
      = (queue.acceptsBatch before
          && (queue.replayGraphEvents before).acceptsBatch after) := by
  induction before generalizing queue with
  | nil => simp [ReferenceWorkQueue.State.acceptsBatch,
      ReferenceWorkQueue.State.replayGraphEvents]
  | cons event rest ih =>
      simp only [List.cons_append, ReferenceWorkQueue.State.acceptsBatch,
        ReferenceWorkQueue.State.replayGraphEvents, List.foldl_cons]
      rw [← ReferenceWorkQueue.State.replayGraphEvents, ih]
      exact (Bool.and_assoc _ _ _).symm

private abbrev rawStep (acc : ReferenceWorkQueue.State × List WorkQueueEvent)
    (event : GraphEvent)
    : ReferenceWorkQueue.State × List WorkQueueEvent :=
  ((acc.1.handleGraphEvent event).1, acc.2 ++ (acc.1.handleGraphEvent event).2)

private theorem graphFold_stopped (batch : List GraphEvent) (result : GraphBatchResult)
    : (batch.foldl GraphBatchResult.handleGraphEvent result).state.stopped
      = result.state.stopped := by
  induction batch generalizing result with
  | nil => rfl
  | cons event rest ih =>
      rw [List.foldl_cons, ih]
      exact State.handleGraphEvent_stopped _ _

private theorem rawFold_terminated (batch : List GraphEvent)
    (acc : ReferenceWorkQueue.State × List WorkQueueEvent)
    : (batch.foldl rawStep acc).1.terminated = acc.1.terminated := by
  induction batch generalizing acc with
  | nil => rfl
  | cons event rest ih =>
      rw [List.foldl_cons, ih]
      exact ReferenceWorkQueue.State.handleGraphEvent_terminated _ _

private theorem state_eq_live {state : State} {queue : ReferenceWorkQueue.State}
    (same : state.queue = queue) (running : state.stopped = false)
    : state = ({ queue } : State) := by
  cases state
  simp_all

private theorem graphFold_core {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (before batch : List GraphEvent)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ batch))
    (accepted
      : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          (before ++ batch)
        = true)
    (result : GraphBatchResult)
    (same
      : result.state
        = ({
              queue :=
                (ReferenceWorkQueue.State.initialize
                  (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
                  before
            }
            : State))
    : batch.foldl rawStep (result.state.queue, result.workQueueEvents)
      = (
        (batch.foldl GraphBatchResult.handleGraphEvent result).state.queue,
        (batch.foldl GraphBatchResult.handleGraphEvent result).workQueueEvents
      ) := by
  induction batch generalizing before result with
  | nil => rfl
  | cons event rest ih =>
      have part : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      have acceptedPart : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch (before ++ [event]) = true := by
        have joined : before ++ event :: rest = (before ++ [event]) ++ rest := by
          simp [List.append_assoc]
        rw [joined, reference_acceptsBatch_append, Bool.and_eq_true] at accepted
        exact accepted.1
      have acceptedBefore : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch before = true := by
        rw [reference_acceptsBatch_append] at acceptedPart
        simp only [Bool.and_eq_true] at acceptedPart
        exact acceptedPart.1
      have bridge := referencePrefix_handleGraphEvent generated before event
        (valid.prefix part) acceptedBefore
      have queueStep : (GraphBatchResult.handleGraphEvent result event).state.queue
          = (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents (before ++ [event]) := by
        rw [ReferenceWorkQueue.State.replayGraphEvents_append]
        simpa only [GraphBatchResult.handleGraphEvent, same] using congrArg Prod.fst bridge
      have stoppedStep : (GraphBatchResult.handleGraphEvent result event).state.stopped = false := by
        change (result.state.handleGraphEvent event).1.stopped = false
        rw [State.handleGraphEvent_stopped, same]
      have nextSame := state_eq_live queueStep stoppedStep
      have nextValid : ReferenceWorkQueue.ValidGraphEvents work ((before ++ [event]) ++ rest) := by
        simpa [List.append_assoc] using valid
      have nextAccepted : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch ((before ++ [event]) ++ rest)
          = true := by
        simpa [List.append_assoc] using accepted
      have next := ih (before ++ [event]) nextValid nextAccepted
        (GraphBatchResult.handleGraphEvent result event) nextSame
      have step : rawStep (result.state.queue, result.workQueueEvents) event
          = ((GraphBatchResult.handleGraphEvent result event).state.queue,
            (GraphBatchResult.handleGraphEvent result event).workQueueEvents) := by
        simp only [rawStep, GraphBatchResult.handleGraphEvent, same]
        rw [← bridge]
      rw [List.foldl_cons, List.foldl_cons, step]
      exact next

-----------------------------------------------------------------------------------------
-- Terminal retirement changes neither notices nor normalized output
-----------------------------------------------------------------------------------------

/-- A generated accepted batch has the reference reducer's exact output and residual projection.
Witness: each dispatch is licensed by its actual accepted prefix; terminal cleanup then erases
only the alternative's retained accounting. Host effects are deliberately not equated.
-/
theorem referencePrefix_handleGraphEvents {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (before batch : List GraphEvent)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ batch))
    (accepted
      : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          (before ++ batch)
        = true)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          before
      let reference := queue.handleGraphEvents batch
      let alternative := (State.fromReference queue).handleGraphEvents batch
      alternative.state = State.fromReference reference.1
      ∧ alternative.workQueueEvents = reference.2 := by
  dsimp only
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents before
  change ((State.fromReference queue).handleGraphEvents batch).state
      = State.fromReference (queue.handleGraphEvents batch).1
    ∧ ((State.fromReference queue).handleGraphEvents batch).workQueueEvents
      = (queue.handleGraphEvents batch).2
  cases done : queue.terminated with
  | true =>
      simp [State.fromReference, State.clearRecords, State.handleGraphEvents,
        ReferenceWorkQueue.State.handleGraphEvents, done]
  | false =>
      have core := graphFold_core generated before batch valid accepted
        ({ state := ⟨queue, false⟩ } : GraphBatchResult) rfl
      have stopped := graphFold_stopped batch ({ state := ⟨queue, false⟩ } : GraphBatchResult)
      have terminal := rawFold_terminated batch (queue, [])
      cases folded
            : batch.foldl GraphBatchResult.handleGraphEvent
                ({ state := ⟨queue, false⟩ } : GraphBatchResult) with
      | mk state events effects =>
          cases state with
          | mk current guard =>
              simp only [folded] at core stopped
              subst guard
              rw [core] at terminal
              simp only [done] at terminal
              simp only [State.fromReference, done, Bool.false_eq_true, ↓reduceIte,
                State.handleGraphEvents, Bool.or_false, folded,
                ReferenceWorkQueue.State.handleGraphEvents]
              rw [core]
              by_cases empty : (current.rootGroups.isEmpty && current.rootStreams.isEmpty) = true
              · simp [empty, State.cancel, State.clearRecords]
              · simp [empty, terminal]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
