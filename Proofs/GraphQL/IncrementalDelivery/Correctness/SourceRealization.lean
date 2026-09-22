import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceObservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SpecificationSource

/-! Every independently admitted history is observable through the maximal source. -/

namespace GraphQL.IncrementalDelivery.Execution

/-- Replay admitted batches through this queue's own source and mapper, retaining the
queue constructor rather than selecting a different realization. Witness: prefix closure permits
each input step, and batching preserves the source's finished predicate.
-/
theorem WorkQueue.observes_inputs (queue : WorkQueue) (work : Work) (ids : IDState)
    (groups : List (List (List WorkQueueEvent))) (conforms : queue.Conforms work)
    (nonempty : ∀ group ∈ groups, group ≠ [])
    (admitted : queue.workEventStream.admissible groups.flatten)
    : let stream :=
        batchIncrementalResults
          (mapIncrementalWorkEventsToResponseEvent queue.workEventStream ids)
      stream.Observes (stream.mapInputs groups).1 (stream.afterInputs groups)
      ∧ ((stream.afterInputs groups).source.IsFinished
          ↔ queue.workEventStream.finished groups.flatten) := by
  let mapped := mapIncrementalWorkEventsToResponseEvent queue.workEventStream ids
  let stream := batchIncrementalResults mapped
  have allowed := (queue.allows_iff_admissible conforms.1 conforms.2.1 _).mpr admitted
  have grouped : stream.source.Allows groups :=
    (EventSource.batch_allows_iff mapped.source groups).mpr ⟨nonempty, allowed⟩
  refine ⟨stream.observes_inputs groups grouped, ?_⟩
  change ((∀ group ∈ groups, group ≠ []) ∧ queue.workEventStream.Allows groups.flatten)
    ∧ queue.workEventStream.finished (queue.workEventStream.history ++ groups.flatten) ↔ _
  rw [conforms.1.1, List.nil_append]
  exact ⟨fun h => h.2, fun finished => ⟨⟨nonempty, allowed⟩, finished⟩⟩

end GraphQL.IncrementalDelivery.Execution

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

/-- An admitted history supplies its own valid initial notices, by either admission
witness's explanation.
-/
theorem ValidHistory.initializes {work history} (admitted : ValidHistory work history)
    : Initializes work history.initialGroups history.initialStreams := by
  rcases admitted with ⟨_, _, _, explained, _⟩ | ⟨_, _, _, explained, _, _⟩
  all_goals exact explained.1

/-- Any admitted work history can be replayed through the actual mapper and every
nonempty response grouping. Witness: maximal-source conformance and finite input replay.
-/
theorem specificationSource_observes {work initialGroups initialStreams}
    (ids : IDState) (groups : List (List (List WorkQueueEvent)))
    (nonempty : ∀ group ∈ groups, group ≠ [])
    (admitted : ValidHistory work ⟨initialGroups, initialStreams, groups.flatten⟩)
    : let source := specificationSource work initialGroups initialStreams
      let stream :=
        batchIncrementalResults
          (mapIncrementalWorkEventsToResponseEvent source.workEventStream ids)
      stream.Observes (stream.mapInputs groups).1 (stream.afterInputs groups)
      ∧ ((stream.afterInputs groups).source.IsFinished
          ↔ AdmissibleRun work ⟨initialGroups, initialStreams, groups.flatten⟩) := by
  let source := specificationSource work initialGroups initialStreams
  let mapped := mapIncrementalWorkEventsToResponseEvent source.workEventStream ids
  let stream := batchIncrementalResults mapped
  have conforms : source.Conforms work := specificationSource_conforms admitted.initializes
  have allowed : stream.source.Allows groups := by
    apply (EventSource.batch_allows_iff mapped.source groups).mpr
    exact ⟨nonempty,
      (source.allows_iff_admissible conforms.1 conforms.2.1 groups.flatten).mpr admitted⟩
  refine ⟨stream.observes_inputs groups allowed, ?_⟩
  apply (ResponseEventStream.batch_afterInputs_finished mapped groups).trans
  exact ⟨fun h => h.2, fun run => ⟨⟨nonempty,
    (source.allows_iff_admissible conforms.1 conforms.2.1 groups.flatten).mpr admitted⟩,
    run⟩⟩

end GraphQL.IncrementalDelivery.WorkQueueSemantics
