import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureSettlementPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MixedFailureCuts

/-! Visible mixed cuts align with the actual source prefix at each atomic output. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Inside one handler, visible object cuts are exactly its accepted source inventory
-----------------------------------------------------------------------------------------

/-- Visible object cuts, reversed, equal accepted failures through the current handler.
Witness: selected labels preserve every output length; block visibility retains all prior
settlements and the current contribution, including earlier silent handlers at equal cuts.
The statement concerns actual guard decisions, not failure licensing or output admission.
-/
theorem State.eligibleObjectFailureCuts_visible (queue : State) (offset : Nat)
    (before after : List SourceOutputBlock) (block : SourceOutputBlock) (index : Nat)
    (inside : index < block.2.length)
    : (failedBefore
        (sourceObjectFailureCuts offset
          (queue.eligibleFailureBlocks (before ++ block :: after)))
        (offset + (before.flatMap Prod.snd).length + index)).reverse
      = queue.objectFailureContributions
          (before.filterMap Prod.fst ++ block.1.toList) := by
  rw [queue.eligibleFailureBlocks_append]
  simp only [State.eligibleFailureBlocks]
  rw [← queue.eligibleFailureBlocks_outputs before]
  rw [sourceObjectFailureCuts_visible offset (queue.eligibleFailureBlocks before) _
      (block.1.bind (queue.replayGraphEvents (before.filterMap Prod.fst)).eligibleFailureLabel,
        block.2) index inside,
    List.reverse_append, queue.eligibleObjectFailureCuts_ledger]
  rw [queue.objectFailureContributions_append]
  congr 1
  cases source : block.1 with
  | none => rfl
  | some event =>
      have contribution :=
        (queue.replayGraphEvents (before.filterMap Prod.fst)).eligibleFailureLabel_contribution
          event
      rw [GraphEvent.failureSettlements_eq_objectFailures_reverse] at contribution
      cases label : (queue.replayGraphEvents (before.filterMap Prod.fst)).eligibleFailureLabel
          event <;> simp_all [State.objectFailureContributions, List.filterMap_cons]
      exact contribution

/-- A non-object-failure handler leaves its visible object inventory at the prior prefix.
Witness: the exact alignment theorem and the handler's empty contribution. In particular,
stream item batches need no safety assumption about their own newly received items here.
-/
theorem State.eligibleObjectFailureCuts_visible_before (queue : State) (offset : Nat)
    (before after : List SourceOutputBlock) (block : SourceOutputBlock) (index : Nat)
    (inside : index < block.2.length)
    (silent : ∀ source, block.1 = some source → source.objectFailure? = none)
    : (failedBefore
        (sourceObjectFailureCuts offset
          (queue.eligibleFailureBlocks (before ++ block :: after)))
        (offset + (before.flatMap Prod.snd).length + index)).reverse
      = queue.objectFailureContributions (before.filterMap Prod.fst) := by
  rw [queue.eligibleObjectFailureCuts_visible offset before after block index inside,
    queue.objectFailureContributions_append]
  suffices (queue.replayGraphEvents (before.filterMap Prod.fst)).objectFailureContributions
      block.1.toList = [] by rw [this, List.nil_append]
  cases source : block.1 with
  | none => rfl
  | some event =>
      have nonfailure := silent event source
      cases event <;> simp_all [GraphEvent.objectFailure?, State.objectFailureContributions,
        State.objectFailureContribution]

-----------------------------------------------------------------------------------------
-- Adding stream cuts cannot add an object-task failure
-----------------------------------------------------------------------------------------

/-- A failed object in the mixed inventory belongs to the object-cut partition.
Witness: partition visibility; a stream cut has an item payload, contradicting uniqueness
of the same task's object descriptor. No generated-work or licensed-history premise is used.
-/
theorem StreamFailureCuts.object_mem_iff {work events streams objects failures index}
    (cuts : StreamFailureCuts work events streams)
    (partition : failures.Perm (streams ++ objects))
    {occurrence owners producer path result}
    (known : TaskAt work occurrence owners producer (.object path result))
    : occurrence ∈ failedBefore failures index
      ↔ occurrence ∈ failedBefore objects index := by
  rw [(failedBefore_partition partition index).mem_iff, List.mem_append]
  constructor
  · rintro (member | member)
    · obtain ⟨entry, retained, same⟩ := List.mem_map.mp member
      obtain ⟨stream, errors, parent, _, item⟩ :=
        cuts.2 entry (List.mem_filter.mp retained).1
      rw [same] at item
      cases (known.unique item).2.2
    · exact member
  · exact Or.inr

-----------------------------------------------------------------------------------------
-- The exact source prefix remains available at every actual atomic position
-----------------------------------------------------------------------------------------

/-- Every atomic output retains its source block, prefix, and exact visible failure ledger.
Witness: locate the atom in the real annotated run, then use started-input agreement and
selected-cut visibility. The source prefix includes its handler but no later handler;
batch-termination blocks carry no source input. Silent earlier inputs are not discarded.
-/
theorem createWorkQueue_atomicOutput_sourcePrefix {work : Execution.Work}
    {batches : List (List GraphEvent)} (started : inputsStarted work batches = true)
    {index : Nat} {event : Execution.WorkQueueEvent}
    (selected
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      let objects := sourceObjectFailureCuts 0 (queue.eligibleFailureBlocks blocks)
      ∃ before block after localIndex,
        blocks = before ++ block :: after
        ∧ index = (before.flatMap Prod.snd).length + localIndex
        ∧ block.2[localIndex]? = some event
        ∧ (before.filterMap Prod.fst ++ block.1.toList).IsPrefix batches.flatten
        ∧ (failedBefore objects index).reverse
          = queue.objectFailureContributions
              (before.filterMap Prod.fst ++ block.1.toList) := by
  dsimp only
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  have annotated : ((queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd)[index]?
      = some event := by rwa [(queue.sourceRunBlocks_agrees batches).2]
  obtain ⟨before, block, after, localIndex, split, position, atLocal⟩ :=
    sourceOutputBlocks_at annotated
  have labels := queue.sourceRunBlocks_inputs_of_started publisher
    (by rwa [← inputsStarted_eq_batchesStarted])
  rw [split] at labels
  refine ⟨before, block, after, localIndex, split, position, atLocal, ?_, ?_⟩
  · refine ⟨after.filterMap Prod.fst, ?_⟩
    rw [← labels, List.filterMap_append]
    cases source : block.1 <;> simp [List.append_assoc, source]
  · rw [split, position]
    simpa only [Nat.zero_add] using queue.eligibleObjectFailureCuts_visible 0 before after
      block localIndex (List.getElem?_eq_some_iff.mp atLocal).1

/-- Each actual atom has an aligned source prefix containing exactly its mixed object cuts.
Witness: the concrete source-block certificate above, then exclude the item-only stream
partition. This discharges object-cut inclusion without using the full final source ledger
or assuming admission. Source validity and start checks can restrict to this prefix.
-/
theorem createWorkQueue_mixedFailureCuts_objectPrefix {work : Execution.Work}
    {batches : List (List GraphEvent)} (started : inputsStarted work batches = true)
    {streams failures : FailureCuts}
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) streams)
    (partition
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        failures.Perm
          (streams
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher batches).2.2)))
    {index : Nat} {event : Execution.WorkQueueEvent}
    (selected
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    : ∃ received : List GraphEvent,
        received.IsPrefix batches.flatten
        ∧ ∀ occurrence owners producer path result,
            TaskAt work occurrence owners producer (.object path result)
            → (occurrence ∈ failedBefore failures index
                ↔ occurrence
                  ∈ (State.initialize
                      (Work.fromExecution work)).objectFailureContributions
                      received) := by
  obtain ⟨before, block, after, localIndex, _, _, _, prior, ledger⟩ :=
    createWorkQueue_atomicOutput_sourcePrefix started selected
  refine ⟨before.filterMap Prod.fst ++ block.1.toList, prior, ?_⟩
  intro occurrence owners producer path result known
  rw [cuts.object_mem_iff partition known, ← ledger, List.mem_reverse]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
