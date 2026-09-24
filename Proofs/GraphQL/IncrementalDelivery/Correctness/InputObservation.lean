import Proofs.GraphQL.IncrementalDelivery.Correctness.Observation

/-! Finite input witnesses for response observations.
These proof-only folds replay supplied observations; they do not choose future inputs.
Witnesses need not be unique: distinct inputs may map to the same response.
-/

namespace GraphQL.IncrementalDelivery.Execution

/-- Empty admission checks the current source state, by the unique prefix of the empty
list.
-/
@[simp]
theorem EventSource.allows_nil_iff (source : EventSource α)
    : source.Allows [] ↔ source.admissible source.history := by
  simp [Allows]

/-- Batched admission is precisely nonempty groups with every flattened prefix admitted.
Witness: take the full grouped prefix, or flatten an arbitrary earlier grouped prefix.
-/
theorem EventSource.batch_allows_iff (source : EventSource α) (groups : List (List α))
    : source.batch.Allows groups
      ↔ (∀ group ∈ groups, group ≠ []) ∧ source.Allows groups.flatten := by
  constructor
  · intro allowed
    exact allowed groups (List.prefix_refl _)
  · rintro ⟨nonempty, allowed⟩ prior ⟨suffix, rfl⟩
    change (∀ group ∈ prior, group ≠ []) ∧ source.Allows prior.flatten
    refine ⟨fun group member => nonempty group (List.mem_append_left _ member), ?_⟩
    apply allowed.prefix
    rw [List.flatten_append]
    exact List.prefix_append _ _

/-- Evaluate only the supplied finite input history, threading the actual mapper's IDs. -/
def ResponseEventStream.mapInputs (stream : ResponseEventStream)
    (inputs : List stream.Input)
    : List IncrementalStreamUpdateResult × IDState :=
  (inputs.mapM stream.mapEvent).run stream.ids

/-- The residual stream after replay, retaining its original opaque source language. -/
def ResponseEventStream.afterInputs (stream : ResponseEventStream)
    (inputs : List stream.Input)
    : ResponseEventStream :=
  {
    stream with
      source := stream.source.advance inputs, ids := (stream.mapInputs inputs).2
  }

/-- Empty replay emits nothing and preserves IDs, by the empty mapM equation. -/
@[simp]
theorem ResponseEventStream.mapInputs_nil (stream : ResponseEventStream)
    : stream.mapInputs [] = ([], stream.ids) := by
  simp [mapInputs]
  rfl

/-- Empty replay leaves the entire stream unchanged, by empty history advancement. -/
@[simp]
theorem ResponseEventStream.afterInputs_nil (stream : ResponseEventStream)
    : stream.afterInputs [] = stream := by
  simp [afterInputs, EventSource.advance]

/-- Mapping a cons agrees with one actual next step followed by the tail, by mapM's
equation.
-/
theorem ResponseEventStream.mapInputs_cons (stream : ResponseEventStream)
    (input : stream.Input) (inputs : List stream.Input) (allowed : stream.Accepts input)
    : stream.mapInputs (input :: inputs)
      = let next := stream.next input allowed
        let rest := next.2.mapInputs inputs
        (next.1 :: rest.1, rest.2) := by
  simp [mapInputs, List.mapM_cons, next, StateT.run_bind]
  rfl

/-- Replay advances exactly the same state as next and tail replay, by source-history
associativity.
-/
theorem ResponseEventStream.afterInputs_cons (stream : ResponseEventStream)
    (input : stream.Input) (inputs : List stream.Input) (allowed : stream.Accepts input)
    : (stream.next input allowed).2.afterInputs inputs
      = stream.afterInputs (input :: inputs) := by
  simp [afterInputs, mapInputs_cons stream input inputs allowed, next,
    EventSource.advance]
  exact List.append_assoc _ _ _

/-- Every admitted finite input list produces its replayed responses, by list induction.
-/
theorem ResponseEventStream.observes_inputs (stream : ResponseEventStream)
    (inputs : List stream.Input) (allowed : stream.source.Allows inputs)
    : stream.Observes (stream.mapInputs inputs).1 (stream.afterInputs inputs) := by
  rcases stream with ⟨Input, source, ids, mapEvent⟩
  change List Input at inputs
  change source.Allows inputs at allowed
  induction inputs generalizing source ids with
  | nil =>
      simpa only [mapInputs_nil ⟨Input, source, ids, mapEvent⟩,
        afterInputs_nil ⟨Input, source, ids, mapEvent⟩]
        using (ResponseEventStream.Observes.nil ⟨Input, source, ids, mapEvent⟩)
  | cons input inputs ih =>
      have parts := (EventSource.allows_append_iff source [input] inputs).mp allowed
      have tail := ih (source := source.advance [input])
        (ids := (mapEvent input).run ids |>.2) parts.2
      have run := ResponseEventStream.Observes.cons
        ⟨Input, source, ids, mapEvent⟩ input parts.1 tail
      rw [mapInputs_cons ⟨Input, source, ids, mapEvent⟩ input inputs parts.1,
        ← afterInputs_cons ⟨Input, source, ids, mapEvent⟩ input inputs parts.1]
      exact run

/-- Every observation exposes its admitted inputs and exact residual state, by run
induction. Initial admission is needed only for the empty observation, which otherwise
tests no source.
-/
theorem ResponseEventStream.Observes.inputs {stream final : ResponseEventStream}
    {updates : List IncrementalStreamUpdateResult}
    (observed : stream.Observes updates final)
    (initial : stream.source.admissible stream.source.history)
    : ∃ inputs : List stream.Input,
        stream.source.Allows inputs
        ∧ updates = (stream.mapInputs inputs).1
        ∧ final = stream.afterInputs inputs := by
  induction observed with
  | nil stream =>
      refine ⟨[], ?_, ?_, ?_⟩
      · intro prior before
        have empty := List.prefix_nil.mp before
        simpa [empty] using initial
      · simp
      · simp
  | cons stream input allowed rest ih =>
      obtain ⟨inputs, admitted, outputs, residual⟩ :=
        ih (allowed [input] (List.prefix_refl _))
      refine ⟨input :: inputs,
        (EventSource.allows_append_iff stream.source [input] inputs).mpr
          ⟨allowed, admitted⟩, ?_, ?_⟩
      · simp only [mapInputs_cons stream input inputs allowed, outputs]
      · exact residual.trans (afterInputs_cons stream input inputs allowed)

/-- Stepwise observation and admitted replay are equivalent, by combining the two
induction witnesses.
-/
theorem ResponseEventStream.observes_iff_inputs (stream final : ResponseEventStream)
    (updates : List IncrementalStreamUpdateResult)
    (initial : stream.source.admissible stream.source.history)
    : stream.Observes updates final
      ↔ ∃ inputs : List stream.Input,
          stream.source.Allows inputs
          ∧ updates = (stream.mapInputs inputs).1
          ∧ final = stream.afterInputs inputs := by
  constructor
  · exact fun observed => observed.inputs initial
  · rintro ⟨inputs, allowed, rfl, rfl⟩
    exact stream.observes_inputs inputs allowed

/-- Batched observations expose nonempty input groups and all admitted intermediate work
prefixes. Witness: generic input replay plus the exact batching-language characterization.
-/
theorem ResponseEventStream.batch_observes_iff_inputs (stream final : ResponseEventStream)
    (updates : List IncrementalStreamUpdateResult)
    (initial : stream.source.admissible stream.source.history)
    : (batchIncrementalResults stream).Observes updates final
      ↔ ∃ groups : List (List stream.Input),
          (∀ group ∈ groups, group ≠ [])
          ∧ stream.source.Allows groups.flatten
          ∧ updates = ((batchIncrementalResults stream).mapInputs groups).1
          ∧ final = (batchIncrementalResults stream).afterInputs groups := by
  have admitted : (batchIncrementalResults stream).source.admissible [] := by
    change (∀ group ∈ ([] : List (List stream.Input)), group ≠ []) ∧ stream.source.Allows []
    exact ⟨by simp, (EventSource.allows_nil_iff _).mpr initial⟩
  rw [observes_iff_inputs _ _ _ admitted]
  simp only [batchIncrementalResults, EventSource.batch_allows_iff, and_assoc]

/-- Batching is finished exactly after admitted groups whose flattened upstream history is
finished. Witness: unfold the batch source's termination predicate; no hasNext premise is
used.
-/
theorem ResponseEventStream.batch_afterInputs_finished (stream : ResponseEventStream)
    (groups : List (List stream.Input))
    : ((batchIncrementalResults stream).afterInputs groups).source.IsFinished
      ↔ ((∀ group ∈ groups, group ≠ []) ∧ stream.source.Allows groups.flatten)
        ∧ (stream.source.advance groups.flatten).IsFinished := by
  rfl

end GraphQL.IncrementalDelivery.Execution
