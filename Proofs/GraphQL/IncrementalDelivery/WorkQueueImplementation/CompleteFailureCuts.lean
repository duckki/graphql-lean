import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureOutput
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.EligibleFailureBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureErrors

/-! Complete error totals at actual normalized group-failure candidate cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Each failed-group output counts all failure labels through its block.
Actual replay instantiates this certificate with guard-selected labels; original source
inputs and output blocks are unchanged. Earlier silent contributions count, later ones do not.
-/
def SourceBlocksHaveCompleteTotals (work : Execution.Work)
    : List GraphEvent → List SourceOutputBlock → Prop
  | _, [] => True
  | before, block :: rest =>
      (∀ group errors,
        Execution.WorkQueueEvent.groupFailure group errors ∈ block.2
        → NodeErrors work (GraphEvent.failureSettlements (before ++ block.1.toList))
            group.ref errors)
      ∧ SourceBlocksHaveCompleteTotals work (before ++ block.1.toList) rest

/-- Appending certified blocks retains their precise intervening source prefix.
Witness: recurse through the first block list and concatenate its optional source labels.
-/
theorem SourceBlocksHaveCompleteTotals.append {work before left right}
    (first : SourceBlocksHaveCompleteTotals work before left)
    (last : SourceBlocksHaveCompleteTotals work (before ++ left.filterMap Prod.fst) right)
    : SourceBlocksHaveCompleteTotals work before (left ++ right) := by
  induction left generalizing before with
  | nil => simpa using last
  | cons block rest ih =>
      refine ⟨first.1, ih first.2 ?_⟩
      cases source : block.1 <;>
        simpa [List.filterMap_cons, source, List.append_assoc] using last

/-- A selected block counts all source failures through its own handler, and no later one.
Witness: peel the earlier blocks while retaining their labels, including silent handlers.
-/
theorem SourceBlocksHaveCompleteTotals.atBlock {work initial before block after}
    (totals : SourceBlocksHaveCompleteTotals work initial (before ++ block :: after))
    {group errors}
    (emitted : Execution.WorkQueueEvent.groupFailure group errors ∈ block.2)
    : NodeErrors work
        (GraphEvent.failureSettlements
          (initial ++ before.filterMap Prod.fst ++ block.1.toList))
        group.ref errors := by
  induction before generalizing initial with
  | nil => simpa using totals.1 group errors emitted
  | cons head rest ih =>
      have result := ih totals.2
      cases source : head.1 <;>
        simpa [List.filterMap_cons, source, List.append_assoc] using result

-----------------------------------------------------------------------------------------
-- Actual handler and batch annotations inherit complete error accounting
-----------------------------------------------------------------------------------------

/-- Annotated handler replay gives complete totals at each normalized output block.
Witness: the complete raw-output theorem and exact publisher failure copying, while
cache/registration and active-cache invariants follow each actual accepted input.
-/
theorem State.GroupErrorAccounting.sourceOutputBlocks_completeTotals {queue : State}
    {work before selected}
    (counts : queue.GroupErrorAccounting work (GraphEvent.failureSettlements selected))
    (ledger : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (clear : queue.NoActiveCachedFailure) (generated : ExecutedWork work)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (accepted : queue.acceptsBatch events = true)
    : SourceBlocksHaveCompleteTotals work selected
        (queue.eligibleFailureBlocks
          (queue.sourceOutputBlocks publisher events).2.2) := by
  induction events generalizing queue before selected publisher with
  | nil => trivial
  | cons event rest ih =>
      have initialPart : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      have localLaws := valid.atPrefix initialPart
      have accepts : queue.acceptsGraphEvent event = true
          ∧ (queue.handleGraphEvent event).1.acceptsBatch rest = true := by
        simpa only [State.acceptsBatch, Bool.and_eq_true] using accepted
      have nextCounts := counts.handleGraphEvent generated ledger.liveGroups ledger.taskGroups
        ledger.started ledger.matching event localLaws.1 accepts.1
      have selectedCounts : (queue.handleGraphEvent event).1.GroupErrorAccounting work
          (GraphEvent.failureSettlements
            (selected ++ (queue.eligibleFailureLabel event).toList)) := by
        rw [GraphEvent.failureSettlements_append_list,
          queue.eligibleFailureLabel_contribution]
        exact nextCounts
      have nextLedger := ledger.handleGraphEvent generated
        (GraphEvent.taskSettlements_subsetIdentities before) event localLaws.1
        localLaws.2.1 accepts.1
      rw [← GraphEvent.taskSettlements_append] at nextLedger
      refine ⟨
        ?_,
        ih selectedCounts nextLedger (clear.handleGraphEvent ledger.refs event) _
          (by simpa [List.append_assoc] using valid) accepts.2
      ⟩
      intro group errors emitted
      dsimp only [Option.bind_some]
      rw [GraphEvent.failureSettlements_append_list,
        queue.eligibleFailureLabel_contribution]
      exact counts.handleGraphEvent_output clear ledger.started ledger.matching event
        localLaws.1 ((publisher.normalizeBatch_atomicGroupFailure_mem _).mp emitted)

/-- Real batch wrapping preserves complete normalized block totals.
Witness: the terminal marker adds no group failure, and open batches retain every handler.
-/
theorem State.GroupErrorAccounting.sourceBatchBlocks_completeTotals
    {queue : State} {work before selected}
    (counts : queue.GroupErrorAccounting work (GraphEvent.failureSettlements selected))
    (ledger : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (clear : queue.NoActiveCachedFailure) (generated : ExecutedWork work)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : SourceBlocksHaveCompleteTotals work selected
        (queue.eligibleFailureBlocks (queue.sourceBatchBlocks publisher events).2.2) := by
  have handlers := counts.sourceOutputBlocks_completeTotals ledger clear generated publisher
    events valid accepted
  simp only [State.sourceBatchBlocks, running, Bool.false_eq_true, ↓reduceIte]
  split
  · rw [State.eligibleFailureBlocks_append]
    exact handlers.append (by simp [State.eligibleFailureBlocks, SourceBlocksHaveCompleteTotals])
  · exact handlers

/-- Complete counts survive the actual multi-batch annotated replay.
Witness: start checks align processed inputs with source prefixes; the independently proved
state/block agreement transports all invariants without changing output or batching.
-/
theorem State.GroupErrorAccounting.sourceRunBlocks_completeTotals
    {queue : State} {work before selected}
    (counts : queue.GroupErrorAccounting work (GraphEvent.failureSettlements selected))
    (ledger : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (clear : queue.NoActiveCachedFailure) (generated : ExecutedWork work)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : SourceBlocksHaveCompleteTotals work selected
        (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2) := by
  induction batches generalizing queue before selected publisher with
  | nil => trivial
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have firstValid : ValidGraphEvents work (before ++ batch) :=
        valid.prefix ⟨rest.flatten, by simp [List.append_assoc]⟩
      have handlers := counts.sourceBatchBlocks_completeTotals ledger clear generated publisher
        batch firstValid running accepted
      cases rest with
      | nil => simpa [State.sourceRunBlocks] using handlers
      | cons next rest =>
          have nextCounts := counts.handleGraphEvents ledger generated batch firstValid
            running accepted
          have nextLedger := ledger.handleGraphEvents generated batch firstValid running accepted
          have nextClear := clear.handleGraphEvents ledger.refs batch
          have stillOpen := ((queue.handleGraphEvents batch).1.batchesStarted_cons next rest
            restStarted).1
          have unchanged := queue.handleGraphEvents_nonterminalState batch running stillOpen
          have agreement := (queue.sourceBatchBlocks_agrees publisher batch).1
          let labels := (queue.eligibleFailureBlocks
            (queue.sourceBatchBlocks publisher batch).2.2).filterMap Prod.fst
          have selectedCounts : (queue.handleGraphEvents batch).1.GroupErrorAccounting work
              (GraphEvent.failureSettlements (selected ++ labels)) := by
            rw [GraphEvent.failureSettlements_append_list]
            dsimp only [labels]
            rw [queue.eligibleFailureBlocks_contributions,
              queue.sourceBatchBlocks_inputs_of_open publisher batch running]
            exact nextCounts
          rw [← agreement] at selectedCounts nextLedger nextClear restStarted
          have later := ih selectedCounts nextLedger nextClear
            (queue.sourceBatchBlocks publisher batch).2.1
            (by simpa [List.append_assoc] using valid) restStarted
          rw [State.sourceRunBlocks, State.eligibleFailureBlocks_append]
          apply handlers.append
          rw [queue.sourceBatchBlocks_inputs_of_open publisher batch running,
            ← unchanged, ← agreement]
          exact later

/-- Generated started replay derives complete totals for every actual normalized block.
Witness: empty-inventory initialization, active-cache clearing, and multi-batch induction.
Selected labels are derived from handler guards; no contributing subset is supplied.
-/
theorem createWorkQueue_sourceRunBlocks_completeTotals {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      SourceBlocksHaveCompleteTotals work []
        (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2) :=
  (createWorkQueue_groupErrorAccounting _ _).sourceRunBlocks_completeTotals
    (before := [])
    (createWorkQueue_pendingAccounting work)
    (createWorkQueue_runNormalized_noActiveCachedFailure _ []) generated _ batches valid
    (by rwa [inputsStarted_eq_batchesStarted] at started)

-----------------------------------------------------------------------------------------
-- The complete source inventory is exactly the object-cut inventory visible at output
-----------------------------------------------------------------------------------------

/-- The bookkeeping failure list reverses exactly the object-failure source labels.
Witness: each source constructor selects the same occurrence in the two list encodings.
-/
theorem GraphEvent.failureSettlements_eq_objectFailures_reverse (events : List GraphEvent)
    : GraphEvent.failureSettlements events
      = (events.filterMap GraphEvent.objectFailure?).reverse := by
  unfold GraphEvent.failureSettlements
  congr 1
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [GraphEvent.groupFailures, List.filterMap_cons,
        GraphEvent.objectFailure?, ih]

/-- Every certified group completion has its exact total under all visible object candidates.
Witness: locate its source block, equate visible cuts with its complete source prefix,
and reverse only the summation order. No selected contributor subset remains.
Candidate licensing and insertion of stream cuts are separate obligations.
-/
theorem sourceObjectFailureCuts_nodeErrors {work : Execution.Work}
    {blocks : List SourceOutputBlock}
    (totals : SourceBlocksHaveCompleteTotals work [] blocks) (offset : Nat) {index : Nat}
    {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent : (blocks.flatMap Prod.snd)[index]? = some (.groupFailure group errors))
    : NodeErrors work
        (failedBefore (sourceObjectFailureCuts offset blocks) (offset + index)) group.ref
        errors := by
  obtain ⟨before, block, after, localIndex, same, position, atLocal⟩ :=
    sourceOutputBlocks_at atEvent
  subst blocks
  have counted := totals.atBlock (List.mem_of_getElem? atLocal)
  simp only [List.nil_append, GraphEvent.failureSettlements_eq_objectFailures_reverse] at counted
  have reordered := nodeErrors_of_perm counted (List.reverse_perm _)
  have visible := sourceObjectFailureCuts_visible offset before after block localIndex
    (List.getElem?_eq_some_iff.mp atLocal).1
  rw [position, ← Nat.add_assoc, visible, sourceObjectFailureCuts_occurrences]
  cases label : block.1 with
  | none => simpa [List.filterMap_append, label] using reordered
  | some event =>
      cases event <;>
        simpa [List.filterMap_append, List.filterMap_cons, label,
          GraphEvent.objectFailure?] using reordered

/-- Actual group failures count exactly the eligible object candidates visible at their index.
Witness: complete selected-label totals, unchanged output, and source-cut visibility.
This discharges group error accounting under the candidate list, not its FailureWitness
licensing or full scheduler conformance.
-/
theorem createWorkQueue_sourceObjectFailureCuts_nodeErrors {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {index : Nat}
    {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let cuts :=
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
      NodeErrors work (failedBefore cuts index) group.ref errors := by
  dsimp only
  simpa only [Nat.zero_add]
    using sourceObjectFailureCuts_nodeErrors
      (createWorkQueue_sourceRunBlocks_completeTotals generated valid started) 0
      (index := index) (group := group) (errors := errors)
      (by rw [State.eligibleFailureBlocks_outputs, (State.sourceRunBlocks_agrees _ _).2]
          exact atEvent)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
