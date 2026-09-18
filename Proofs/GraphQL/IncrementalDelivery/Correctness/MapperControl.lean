import Proofs.GraphQL.IncrementalDelivery.Correctness.ResponseReplay
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Termination

/-! The mapper's continuation flag observes termination, not the number of open IDs. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- A proof-only projection identifying the queue's termination marker. -/
def isTermination : WorkEvent → Bool
  | .workQueueTermination => true
  | _ => false

/-- The termination projection detects exactly the termination constructor. -/
theorem any_termination (events : List WorkEvent)
    : events.any isTermination = true ↔ WorkEvent.workQueueTermination ∈ events := by
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨event, member, terminal⟩
    cases event <;> simp_all [isTermination]
  · intro member
    exact ⟨_, member, rfl⟩

/-- Each event retains the previous flag unless it is termination; witness: reduce
the mapper cases and their state-result pairs.
-/
theorem eventLoop_hasNext (event : WorkEvent)
    (initial update : IncrementalStreamUpdateResult) (ids next : IDState)
    (mapped : (eventLoop event initial).run ids = (.yield update, next))
    : update.hasNext = (initial.hasNext && !isTermination event) := by
  cases event <;>
    simp only [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure] at mapped
  all_goals
    repeat first | split at mapped | cases mapped
    simp [isTermination]

/-- Iteration stops the flag exactly when an input termination is present; witness:
event-loop induction with the actual mapper result witnesses.
-/
theorem loop_hasNext (events : List WorkEvent) (initial : IncrementalStreamUpdateResult)
    (ids : IDState)
    : ((forIn events initial eventLoop).run ids).1.hasNext
      = (initial.hasNext && !events.any isTermination) := by
  induction events generalizing initial ids with
  | nil =>
      simp; rfl
  | cons event rest ih =>
      obtain ⟨middle, state, mapped, _⟩ := eventLoop_spec event initial ids
      have flag := eventLoop_hasNext event initial middle ids state mapped
      have tail := ih middle state
      simp only [StateT.run] at mapped tail
      simp [List.forIn_cons, StateT.run, StateT.bind, bind, mapped, tail,
        flag, Bool.not_or, Bool.and_assoc]

/-- Public batch mapping hasNext is false exactly when its supplied inputs terminate. -/
theorem mapWorkEventBatch_hasNext (events : List WorkEvent) (ids : IDState)
    : ((mapWorkEventBatch events).run ids).1.hasNext = !events.any isTermination := by
  rw [mapWorkEventBatch_loop, loop_hasNext]
  rfl

/-- No termination in a batch means another event may follow, by the mapper equation. -/
theorem mapWorkEventBatch_continues {events : List WorkEvent} (ids : IDState)
    (ordinary : WorkEvent.workQueueTermination ∉ events)
    : ((mapWorkEventBatch events).run ids).1.hasNext = true := by
  rw [mapWorkEventBatch_hasNext]
  have absent : events.any isTermination = false := by
    cases h : events.any isTermination
    · rfl
    · exact False.elim (ordinary ((any_termination events).mp h))
  simp [absent]

/-- A terminal batch stops continuation, by termination membership and the mapper equation.
-/
theorem mapWorkEventBatch_stops {events : List WorkEvent} (ids : IDState)
    (terminal : WorkScheduler.Terminates events)
    : ((mapWorkEventBatch events).run ids).1.hasNext = false := by
  rw [mapWorkEventBatch_hasNext, (any_termination events).mpr terminal.member]
  rfl

/-- Terminal work-batch replay is nonempty with accurate continuation flags; witness:
batch-sequence induction and the independent termination marker.
-/
theorem mappedTrace_control {batches} (terminal : WorkScheduler.TerminalBatches batches)
    (ids : IDState)
    : mappedTrace batches ids ≠ []
      ∧ DeliveryTrace.hasNextValid (mappedTrace batches ids) = true := by
  induction terminal generalizing ids with
  | @last batch terminal =>
      have stops := mapWorkEventBatch_stops ids terminal
      cases mapped : (mapWorkEventBatch batch).run ids with
      | mk update next =>
          simp only [mapped] at stops
          simp [mappedTrace, mapped, DeliveryTrace.hasNextValid, stops]
  | @cons batch rest ordinary terminal ih =>
      have continues := mapWorkEventBatch_continues ids ordinary
      obtain ⟨nonempty, flags⟩ := ih ((mapWorkEventBatch batch).run ids).2
      have ne : (mappedTrace rest ((mapWorkEventBatch batch).run ids).2).isEmpty = false := by
        simpa using nonempty
      cases mapped : (mapWorkEventBatch batch).run ids with
      | mk update next =>
          simp only [mapped] at continues ne flags
          simp [mappedTrace, mapped, DeliveryTrace.hasNextValid, continues, ne, flags]

end GraphQL.IncrementalDelivery.Correctness
