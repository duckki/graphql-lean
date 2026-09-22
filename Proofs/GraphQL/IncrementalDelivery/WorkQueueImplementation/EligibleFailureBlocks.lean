import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection

/-! Select contributing failure labels without changing source execution or output blocks. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The actual guard selects proof labels, never source inputs or emitted events
-----------------------------------------------------------------------------------------

/-- Retain an input label exactly when its actual handler accepts an object failure.
`queue` is the pre-handler state. This proof annotation does not filter execution inputs.
-/
def State.eligibleFailureLabel (queue : State) (event : GraphEvent) : Option GraphEvent :=
  if (queue.objectFailureContribution event).isEmpty then none else some event

/-- The retained label records precisely the handler's eligible failure contribution.
Witness: non-failure inputs have no token; task failures use the same owner guard.
-/
theorem State.eligibleFailureLabel_contribution (queue : State) (event : GraphEvent)
    : GraphEvent.failureSettlements (queue.eligibleFailureLabel event).toList
      = queue.objectFailureContribution event := by
  cases event with
  | taskFailure occurrence errors =>
      cases found : queue.taskNode? occurrence with
      | none => simp [eligibleFailureLabel, objectFailureContribution, found,
          GraphEvent.failureSettlements]
      | some node =>
          cases eligible : queue.taskHasHealthyOwner node.task <;>
            simp [eligibleFailureLabel, objectFailureContribution, found, eligible,
              GraphEvent.failureSettlements, GraphEvent.groupFailures]
  | taskSuccess | streamItems | streamSuccess | streamFailure => rfl

/-- Keep every output block, but label only contributing object failures.
`queue` follows all original source labels, including ignored settlements. Output events,
silent blocks, and their unbatched positions are unchanged; labels are proof evidence only.
-/
def State.eligibleFailureBlocks (queue : State)
    : List SourceOutputBlock → List SourceOutputBlock
  | [] => []
  | block :: rest =>
      (block.1.bind queue.eligibleFailureLabel, block.2)
      :: (queue.replayGraphEvents block.1.toList).eligibleFailureBlocks rest

/-- Concatenating annotations preserves the true state at the intermediate source boundary.
Witness: list induction replays original labels, not the selected failure labels.
-/
theorem State.eligibleFailureBlocks_append (queue : State)
    (before after : List SourceOutputBlock)
    : queue.eligibleFailureBlocks (before ++ after)
      = queue.eligibleFailureBlocks before
        ++ (queue.replayGraphEvents (before.filterMap Prod.fst)).eligibleFailureBlocks
            after := by
  induction before generalizing queue with
  | nil => rfl
  | cons block rest ih =>
      simp only [List.cons_append, eligibleFailureBlocks, ih, List.cons_append]
      congr 1
      cases source : block.1 <;>
        simp [source, State.replayGraphEvents, List.foldl_cons]

/-- Selected labels preserve the exact output segments, including empty segments.
Witness: each recursive annotation changes only the optional source label.
-/
theorem State.eligibleFailureBlocks_outputs (queue : State)
    (blocks : List SourceOutputBlock)
    : (queue.eligibleFailureBlocks blocks).flatMap Prod.snd
      = blocks.flatMap Prod.snd := by
  induction blocks generalizing queue with
  | nil => rfl
  | cons block rest ih => simp only [eligibleFailureBlocks, List.flatMap_cons, ih]

/-- Selected failure labels are a subsequence of the original source labels.
Witness: the actual guard either retains an existing label or removes only that label.
-/
theorem State.eligibleFailureBlocks_inputs (queue : State)
    (blocks : List SourceOutputBlock)
    : ((queue.eligibleFailureBlocks blocks).filterMap Prod.fst).Sublist
        (blocks.filterMap Prod.fst) := by
  induction blocks generalizing queue with
  | nil => exact .refl _
  | cons block rest ih =>
      simp only [eligibleFailureBlocks, List.filterMap_cons]
      cases source : block.1 with
      | none => simpa [source, State.replayGraphEvents] using ih queue
      | some event =>
          by_cases empty : (queue.objectFailureContribution event).isEmpty = true
          · simpa [eligibleFailureLabel, empty]
              using (ih (queue.replayGraphEvents [event])).cons event
          · simpa [eligibleFailureLabel, empty]
              using (ih (queue.replayGraphEvents [event])).cons_cons event

/-- The selected labels have exactly the complete guard-filtered failure ledger.
Witness: reverse-order contribution concatenation through all original handler states.
-/
theorem State.eligibleFailureBlocks_contributions (queue : State)
    (blocks : List SourceOutputBlock)
    : GraphEvent.failureSettlements
        ((queue.eligibleFailureBlocks blocks).filterMap Prod.fst)
      = queue.objectFailureContributions (blocks.filterMap Prod.fst) := by
  induction blocks generalizing queue with
  | nil => rfl
  | cons block rest ih =>
      cases source : block.1 with
      | none =>
          simpa [eligibleFailureBlocks, source, State.replayGraphEvents] using ih queue
      | some event =>
          have labels : ((queue.eligibleFailureBlocks (block :: rest)).filterMap Prod.fst)
              = (queue.eligibleFailureLabel event).toList
                ++ ((queue.handleGraphEvent event).1.eligibleFailureBlocks rest).filterMap
                  Prod.fst := by
            simp only [eligibleFailureBlocks, source, Option.bind_some,
              State.replayGraphEvents, List.filterMap_cons]
            cases queue.eligibleFailureLabel event <;> rfl
          rw [labels, GraphEvent.failureSettlements_append_list, ih,
            queue.eligibleFailureLabel_contribution]
          simp [source, State.objectFailureContributions]

-----------------------------------------------------------------------------------------
-- Generated replay inherits candidate uniqueness and source provenance
-----------------------------------------------------------------------------------------

/-- Contributing object cuts retain distinct source occurrences in actual replay.
Witness: selected labels embed in the original inputs, whose task identities are fresh.
-/
theorem createWorkQueue_eligibleObjectFailureCuts_unique {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks :=
        queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2
      ((sourceObjectFailureCuts 0 blocks).map Prod.snd).Nodup := by
  dsimp only
  rw [sourceObjectFailureCuts_occurrences]
  apply List.Nodup.sublist ?_ valid.identities_nodup.1
  exact (((State.eligibleFailureBlocks_inputs _ _).trans
    (State.sourceRunBlocks_inputs _ _ _)).filterMap GraphEvent.objectFailure?).trans
      (GraphEvent.objectFailures_sublist _)

/-- Each contributing candidate is a fixed failed reachable task within actual output.
Witness: selected-label provenance and unchanged output lengths transport the original
source matching, readiness, and candidate bounds. Licensing is not assumed or proved here.
-/
theorem createWorkQueue_eligibleObjectFailureCuts_origin {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks :=
        queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2
      ∀ entry ∈ sourceObjectFailureCuts 0 blocks,
        entry.1
          ≤ ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).length
        ∧ ∃ owners producer path errors,
            TaskAt work entry.2 owners producer (.object path (.error errors))
            ∧ Reachable work entry.2 := by
  dsimp only
  intro entry member
  obtain ⟨errors, source⟩ := sourceObjectFailureCuts_source member
  have received := (State.sourceRunBlocks_inputs _ _ _).subset
    ((State.eligibleFailureBlocks_inputs _ _).subset source)
  obtain ⟨owners, producer, path, known⟩ := valid.eachMatches received
  refine ⟨?_, owners, producer, path, errors, known,
    valid.taskFailure_reachable generated received⟩
  have bound := (sourceObjectFailureCuts_bounds _ _ entry member).2
  simpa only [Nat.zero_add, State.eligibleFailureBlocks_outputs,
    (State.sourceRunBlocks_agrees _ _).2] using bound

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
