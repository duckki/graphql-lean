import Proofs.GraphQL.IncrementalDelivery.Correctness
import Tests.GraphQL.IncrementalDelivery.Sources
import Tests.GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! Input-history correspondence with real source and work-accounting witnesses. -/

namespace GraphQL.IncrementalDelivery.Tests.SourceObservation

open GraphQL.IncrementalDelivery.Execution

/-- A single admitted work-event batch, copied from the explicit terminal work-run
fixture.
-/
def events : List WorkQueueEvent :=
  [
    .groupValues WorkQueueSemantics.node [{ path := [], data := [] }],
    .groupSuccess WorkQueueSemantics.node [] [],
    .workQueueTermination
  ]

def queue : WorkQueue :=
  {
    initialGroups := [WorkQueueSemantics.node],
    initialStreams := [],
    workEventStream := .ofList [events]
  }

/-- The source's empty history is admitted directly by its valid initial notices. -/
theorem emptyHistory
    : GraphQL.IncrementalDelivery.WorkQueueSemantics.AdmissiblePrefix
        WorkQueueSemantics.work
        ((⟨queue.initialGroups, queue.initialStreams, []⟩
          : WorkQueueSemantics.History)) :=
  WorkQueueSemantics.emptyHistory

/-- A terminal run cannot have zero work batches: batching cannot discard its termination
event.
-/
private theorem terminalNonempty {work : Work}
    {history : GraphQL.IncrementalDelivery.WorkQueueSemantics.History}
    (run : GraphQL.IncrementalDelivery.WorkQueueSemantics.AdmissibleRun work history)
    : history.batches ≠ [] := by
  rintro empty
  obtain ⟨events, _, _, _, _, batched⟩ := run
  rw [empty] at batched
  have noEvents {events : List WorkQueueEvent}
      (h : GraphQL.IncrementalDelivery.WorkQueueSemantics.WorkBatching events []) : events = [] := by
    cases h
    rfl
  have impossible := noEvents batched
  simp at impossible

/-- This replay source satisfies every contract clause; its only histories are empty or
terminal.
-/
theorem conforms : queue.Conforms WorkQueueSemantics.work := by
  refine ⟨
    ⟨rfl, List.nil_prefix⟩,
    fun _ _ before admitted => before.trans admitted,
    ?_,
    ?_
  ⟩
  · intro batches admitted
    change batches.IsPrefix [events] at admitted
    cases batches with
    | nil => exact Or.inl emptyHistory
    | cons first rest =>
        obtain ⟨rfl, tail⟩ := List.cons_prefix_cons.mp admitted
        have empty := List.prefix_nil.mp tail
        subst rest
        exact Or.inr WorkQueueSemantics.completedRun
  · intro batches
    change batches = [events] ↔ batches.IsPrefix [events]
      ∧ GraphQL.IncrementalDelivery.WorkQueueSemantics.AdmissibleRun WorkQueueSemantics.work
          ((⟨queue.initialGroups, queue.initialStreams, batches⟩ : WorkQueueSemantics.History))
    constructor
    · rintro rfl
      exact ⟨List.prefix_refl _, WorkQueueSemantics.completedRun⟩
    · rintro ⟨admitted, terminal⟩
      cases batches with
      | nil => exact False.elim (terminalNonempty terminal rfl)
      | cons first rest =>
          obtain ⟨rfl, tail⟩ := List.cons_prefix_cons.mp admitted
          have empty := List.prefix_nil.mp tail
          subst rest
          rfl

def mapped : ResponseEventStream :=
  mapIncrementalWorkEventsToResponseEvent queue.workEventStream
    { ids := [(0, "0")], nextID := 1 }

def batched : ResponseEventStream := batchIncrementalResults mapped

/-- The full replay is admitted by source conformance and the explicit terminal fixture.
-/
theorem allowed : batched.source.Allows [[events]] := by
  apply (EventSource.batch_allows_iff mapped.source [[events]]).mpr
  refine ⟨by simp, ?_⟩
  exact (queue.allows_iff_admissible conforms.1 conforms.2.1 [events]).mpr
    (List.prefix_refl _)

/-- Finite replay witnesses an actual observation through the public next relation. -/
theorem observed
    : batched.Observes (batched.mapInputs [[events]]).1
        (batched.afterInputs [[events]]) :=
  batched.observes_inputs [[events]] allowed

/-- The observed residual source is finished, by its upstream singleton history and
batching law.
-/
theorem finished : (batched.afterInputs [[events]]).source.IsFinished := by
  apply (ResponseEventStream.batch_afterInputs_finished mapped [[events]]).mpr
  exact ⟨(EventSource.batch_allows_iff _ _).mp allowed, rfl⟩

/-- The source-to-work theorem recovers a terminal history for the actual observed wire
update.
-/
example
    : ∃ groups : List (List (List WorkQueueEvent)),
        (∀ group ∈ groups, group ≠ [])
        ∧ GraphQL.IncrementalDelivery.WorkQueueSemantics.AdmissibleRun
            WorkQueueSemantics.work
            ((⟨queue.initialGroups, queue.initialStreams, groups.flatten⟩
              : WorkQueueSemantics.History))
        ∧ (batched.mapInputs [[events]]).1 = (batched.mapInputs groups).1 :=
  queue.observes_complete_workHistory WorkQueueSemantics.work _ conforms observed finished

/-- The witness has the expected wire ID and termination flag, using the actual stateful
mapper.
-/
example
    : (batched.mapInputs [[events]]).1
      = [{
          hasNext := false, incremental := [.object "0" []], completed := [{ id := "0" }]
        }] := by
  rfl

/-- A source with no admitted current state can still be unobserved; extraction needs
initialization.
-/
def impossible : ResponseEventStream :=
  {
    Input := Nat,
    source := { admissible := fun _ => False, finished := fun _ => False },
    ids := {},
    mapEvent := fun _ => pure { hasNext := true }
  }

/-- The empty constructor observes nothing even for this impossible source. -/
example : impossible.Observes [] impossible := .nil _

/-- No admitted input history can witness this vacuous observation; every input has an
empty prefix.
-/
example : ¬∃ inputs : List impossible.Input, impossible.source.Allows inputs := by
  rintro ⟨inputs, admitted⟩
  exact admitted [] List.nil_prefix

/-- Aggregation cannot conceal a disallowed intermediate history, by the flattened-prefix
law.
-/
example : ¬Sources.skipsPrefix.batch.Allows [[1, 2]] := by
  intro admitted
  have allPrefixes := (EventSource.batch_allows_iff _ _).mp admitted |>.2
  have first := allPrefixes [1] ⟨[2], rfl⟩
  simp [Sources.skipsPrefix] at first

/-- Batched observation after prior consumption continues from that history, not from an
empty source.
-/
example : (Sources.branching.advance [1]).batch.Allows [[2]] := by
  apply (EventSource.batch_allows_iff _ _).mpr
  refine ⟨by simp, ?_⟩
  intro initial before
  exact Or.inl ((List.prefix_append_right_inj [1]).mpr before)

/-- Different completion orders remain possible, witnessed by each branch's prefix
relation.
-/
example
    : Sources.branching.batch.Allows [[1], [2]]
      ∧ Sources.branching.batch.Allows [[2], [1]] := by
  constructor
  · apply (EventSource.batch_allows_iff _ _).mpr
    exact ⟨by simp, fun _ before => Or.inl before⟩
  · apply (EventSource.batch_allows_iff _ _).mpr
    exact ⟨by simp, fun _ before => Or.inr before⟩

end GraphQL.IncrementalDelivery.Tests.SourceObservation
