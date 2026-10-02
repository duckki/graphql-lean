import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureCuts

/-! Ordered object-failure cuts retain their actual pre-settlement queue and source prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Invert a selected label without forgetting the handler's guard
-----------------------------------------------------------------------------------------

/-- A selected object-failure label comes from a started task with a healthy contributor.
Witness: invert the optional source label, task lookup, and exact executable owner guard.
-/
theorem State.eligibleFailureLabel_objectFailure_iff {queue : State}
    {source : Option GraphEvent} {occurrence : Occurrence}
    : ((source.bind queue.eligibleFailureLabel).bind GraphEvent.objectFailure?)
        = some occurrence
      ↔ ∃ errors node,
          source = some (.taskFailure occurrence errors)
          ∧ queue.taskNode? occurrence = some node
          ∧ queue.taskHasHealthyOwner node.task = true := by
  cases source with
  | none => simp
  | some event =>
      cases event with
      | taskSuccess | streamItems | streamSuccess | streamFailure =>
          simp [State.eligibleFailureLabel, State.objectFailureContribution]
      | taskFailure task errors =>
          cases found : queue.taskNode? task with
          | none =>
              simp [State.eligibleFailureLabel, State.objectFailureContribution, found]
              rintro rfl
              simp [found]
          | some node =>
              cases healthy : queue.taskHasHealthyOwner node.task <;>
                simp [State.eligibleFailureLabel, State.objectFailureContribution,
                  found, healthy, GraphEvent.objectFailure?]
              all_goals rintro rfl; simp_all

/-- Replay through an optional block label reaches the same state as the label prefix.
Witness: absent labels do nothing and present labels perform one ordinary handler step.
-/
private theorem replay_block_cons (queue : State) (block : SourceOutputBlock)
    (before : List SourceOutputBlock)
    : queue.replayGraphEvents ((block :: before).filterMap Prod.fst)
      = (queue.replayGraphEvents block.1.toList).replayGraphEvents
          (before.filterMap Prod.fst) := by
  cases source : block.1 <;> simp [source, State.replayGraphEvents]

-----------------------------------------------------------------------------------------
-- An ordered cut split identifies the exact earlier accepted-settlement inventory
-----------------------------------------------------------------------------------------

/-- Splitting the selected cut list identifies its original handler and all earlier cuts.
Witness: induction over original blocks, retaining ignored labels and zero-width outputs.
In particular, earlier settlements at the same output index stay in `before`, not `after`.
-/
theorem State.eligibleObjectFailureCuts_split {queue : State} {offset : Nat}
    {blocks : List SourceOutputBlock} {before after : FailureCuts}
    {cut : Nat} {occurrence : Occurrence}
    (split
      : sourceObjectFailureCuts offset (queue.eligibleFailureBlocks blocks)
        = before ++ (cut, occurrence) :: after)
    : ∃ earlier outputs errors later node,
        blocks = earlier ++ (some (.taskFailure occurrence errors), outputs) :: later
        ∧ cut = offset + (earlier.flatMap Prod.snd).length
        ∧ before = sourceObjectFailureCuts offset (queue.eligibleFailureBlocks earlier)
        ∧ (queue.replayGraphEvents (earlier.filterMap Prod.fst)).taskNode? occurrence
          = some node
        ∧ (queue.replayGraphEvents (earlier.filterMap Prod.fst)).taskHasHealthyOwner
            node.task
          = true := by
  induction blocks generalizing queue offset before with
  | nil => simp [State.eligibleFailureBlocks, sourceObjectFailureCuts] at split
  | cons block rest ih =>
      let next := queue.replayGraphEvents block.1.toList
      have lift {prior : FailureCuts}
          (tailSplit : sourceObjectFailureCuts (offset + block.2.length)
            (next.eligibleFailureBlocks rest) = prior ++ (cut, occurrence) :: after)
          (prefixEq : ∀ earlier,
            prior = sourceObjectFailureCuts (offset + block.2.length)
              (next.eligibleFailureBlocks earlier)
            → before = sourceObjectFailureCuts offset
                (queue.eligibleFailureBlocks (block :: earlier)))
          : ∃ earlier outputs errors later node,
              block :: rest
                = earlier ++ (some (.taskFailure occurrence errors), outputs) :: later
              ∧ cut = offset + (earlier.flatMap Prod.snd).length
              ∧ before = sourceObjectFailureCuts offset
                  (queue.eligibleFailureBlocks earlier)
              ∧ (queue.replayGraphEvents (earlier.filterMap Prod.fst)).taskNode?
                  occurrence = some node
              ∧ (queue.replayGraphEvents (earlier.filterMap Prod.fst)).taskHasHealthyOwner
                  node.task = true := by
        obtain ⟨earlier, outputs, errors, later, node, blocksEq, boundary, cutsEq,
          found, healthy⟩ := ih tailSplit
        refine ⟨block :: earlier, outputs, errors, later, node,
          by simp [blocksEq], ?_, prefixEq earlier cutsEq, ?_, ?_⟩
        · simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using boundary
        · simpa only [replay_block_cons] using found
        · simpa only [replay_block_cons] using healthy
      cases selected
            : ((block.1.bind queue.eligibleFailureLabel).bind
                GraphEvent.objectFailure?) with
      | none =>
          have tailSplit : sourceObjectFailureCuts (offset + block.2.length)
              (next.eligibleFailureBlocks rest) = before ++ (cut, occurrence) :: after := by
            simpa only [State.eligibleFailureBlocks, sourceObjectFailureCuts, selected]
              using split
          apply lift tailSplit
          intro earlier cutsEq
          simpa only [State.eligibleFailureBlocks, sourceObjectFailureCuts, selected]
            using cutsEq
      | some task =>
          cases before with
          | nil =>
              have same : (offset, task) = (cut, occurrence) := by
                have equality : (offset, task) ::
                    sourceObjectFailureCuts (offset + block.2.length)
                      (next.eligibleFailureBlocks rest) = (cut, occurrence) :: after := by
                  simpa only [State.eligibleFailureBlocks, sourceObjectFailureCuts,
                    selected, List.nil_append]
                    using split
                exact (List.cons.inj equality).1
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
              obtain ⟨errors, node, label, found, healthy⟩ :=
                State.eligibleFailureLabel_objectFailure_iff.mp selected
              exact ⟨
                [],
                block.2,
                errors,
                rest,
                node,
                by simp [← label],
                by simp,
                rfl,
                found,
                healthy
              ⟩
          | cons first prior =>
              have same : (offset, task) = first ∧
                  sourceObjectFailureCuts (offset + block.2.length)
                    (next.eligibleFailureBlocks rest) = prior ++ (cut, occurrence) :: after := by
                simpa only [State.eligibleFailureBlocks, sourceObjectFailureCuts,
                  selected, List.cons_append, List.cons.injEq]
                  using split
              apply lift same.2
              intro earlier cutsEq
              simp only [State.eligibleFailureBlocks, sourceObjectFailureCuts, selected]
              rw [same.1, ← cutsEq]

/-- Earlier selected cuts contain exactly the guard-filtered contribution ledger.
Witness: occurrence projection and selected-label accounting; reversal changes only the
bookkeeping convention, not which settlements preceded the selected cut.
-/
theorem State.eligibleObjectFailureCuts_ledger (queue : State) (offset : Nat)
    (blocks : List SourceOutputBlock)
    : ((sourceObjectFailureCuts offset (queue.eligibleFailureBlocks blocks)).map
        Prod.snd).reverse
      = queue.objectFailureContributions (blocks.filterMap Prod.fst) := by
  rw [sourceObjectFailureCuts_occurrences,
    ← GraphEvent.failureSettlements_eq_objectFailures_reverse]
  exact queue.eligibleFailureBlocks_contributions blocks

-----------------------------------------------------------------------------------------
-- Actual started replay consumes every source label at its original output boundary
-----------------------------------------------------------------------------------------

/-- Started batches retain every input label in their actual source annotations.
Witness: each batch begins open; block agreement gives the next batch's exact queue.
-/
theorem State.sourceRunBlocks_inputs_of_started {queue : State}
    (publisher : IncrementalPublisher) {batches : List (List GraphEvent)}
    (started : queue.batchesStarted batches = true)
    : ((queue.sourceRunBlocks publisher batches).2.2.filterMap Prod.fst)
      = batches.flatten := by
  induction batches generalizing queue publisher with
  | nil => rfl
  | cons batch rest ih =>
      obtain ⟨running, _, restStarted⟩ := queue.batchesStarted_cons batch rest started
      simp only [State.sourceRunBlocks, List.filterMap_append, List.flatten_cons]
      rw [queue.sourceBatchBlocks_inputs_of_open publisher batch running]
      congr 1
      apply ih
      rwa [(queue.sourceBatchBlocks_agrees publisher batch).1]

/-- Every split of actual eligible object cuts retains its precise source prefix and guard.
Witness: the block split above, exact started-input replay, publication-atom agreement,
and the earlier-cut ledger equality. This does not assume output admission or licensing.
-/
theorem createWorkQueue_eligibleObjectFailureCuts_split {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {before after : FailureCuts}
    {cut : Nat} {occurrence : Occurrence}
    (split
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
        = before ++ (cut, occurrence) :: after)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      ∃ earlier outputs errors later node,
        (queue.sourceRunBlocks publisher batches).2.2
          = earlier ++ (some (.taskFailure occurrence errors), outputs) :: later
        ∧ cut = (earlier.flatMap Prod.snd).length
        ∧ earlier.flatMap Prod.snd
          = ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take cut
        ∧ (earlier.filterMap Prod.fst ++ [.taskFailure occurrence errors]).IsPrefix
            batches.flatten
        ∧ ValidGraphEvents work (earlier.filterMap Prod.fst)
        ∧ (GraphEvent.taskFailure occurrence errors).MatchesWork work
        ∧ before = sourceObjectFailureCuts 0 (queue.eligibleFailureBlocks earlier)
        ∧ (before.map Prod.snd).reverse
          = queue.objectFailureContributions (earlier.filterMap Prod.fst)
        ∧ (queue.replayGraphEvents (earlier.filterMap Prod.fst)).taskNode? occurrence
          = some node
        ∧ (queue.replayGraphEvents (earlier.filterMap Prod.fst)).taskHasHealthyOwner
            node.task
          = true := by
  dsimp only at split ⊢
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  obtain ⟨earlier, outputs, errors, later, node, blocksEq, boundary, cutsEq, found, healthy⟩ :=
    State.eligibleObjectFailureCuts_split split
  have boundary : cut = (earlier.flatMap Prod.snd).length := by simpa using boundary
  have labels := queue.sourceRunBlocks_inputs_of_started publisher
    (by rwa [← inputsStarted_eq_batchesStarted])
  have sourceSplit : batches.flatten
      = earlier.filterMap Prod.fst ++ .taskFailure occurrence errors ::
          later.filterMap Prod.fst := by
    rw [blocksEq] at labels
    simpa only [List.filterMap_append, List.filterMap_cons, Option.some.injEq]
      using labels.symm
  have sourcePrefix
      : (earlier.filterMap Prod.fst ++ [GraphEvent.taskFailure occurrence errors]).IsPrefix
          batches.flatten := by
    exact ⟨later.filterMap Prod.fst, by simp [sourceSplit, List.append_assoc]⟩
  have sourceBefore : (earlier.filterMap Prod.fst).IsPrefix batches.flatten :=
    (List.prefix_append _ _).trans sourcePrefix
  refine ⟨earlier, outputs, errors, later, node, blocksEq, boundary, ?_, sourcePrefix,
    valid.prefix sourceBefore, valid.eachMatches ?_, cutsEq, ?_, found, healthy⟩
  · have outputsEq := (queue.sourceRunBlocks_agrees batches).2
    rw [blocksEq] at outputsEq
    rw [← outputsEq, boundary]
    simp [List.flatMap_append]
  · apply sourcePrefix.subset
    simp
  · rw [cutsEq]
    exact queue.eligibleObjectFailureCuts_ledger 0 earlier

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
