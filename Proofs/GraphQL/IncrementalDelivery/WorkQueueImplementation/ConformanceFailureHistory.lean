import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformanceBatchShape

/-! Transport the same accepted failure inventory onto the actual nonterminal history. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The optional terminal block carries no source settlement
-----------------------------------------------------------------------------------------

/-- A batch that changes the termination flag ends with the unlabelled terminal block.
Witness: the empty-root branch appends that block; handlers cannot set the flag.
-/
theorem State.sourceBatchBlocks_terminalSuffix (queue : State)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    (running : queue.terminated = false)
    (ended : (queue.sourceBatchBlocks publisher events).1.terminated = true)
    : ∃ before,
        (queue.sourceBatchBlocks publisher events).2.2
        = before ++ [(none, [.workQueueTermination])] := by
  have flag := (queue.sourceOutputBlocks_terminalShape publisher events).1
  simp only [State.sourceBatchBlocks, running, Bool.false_eq_true, ↓reduceIte] at ended ⊢
  split
  · exact ⟨_, rfl⟩
  · simp_all

/-- A completed replay ends with the same terminal block, with no later source labels.
Witness: concatenate batches until the ending one, then use termination absorption.
-/
theorem State.sourceRunBlocks_terminalSuffix (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (running : queue.terminated = false)
    (ended : (queue.sourceRunBlocks publisher batches).1.terminated = true)
    : ∃ before,
        (queue.sourceRunBlocks publisher batches).2.2
        = before ++ [(none, [.workQueueTermination])] := by
  induction batches generalizing queue publisher with
  | nil => simp [State.sourceRunBlocks, running] at ended
  | cons batch rest ih =>
      let next := queue.sourceBatchBlocks publisher batch
      cases done : next.1.terminated with
      | true =>
          obtain ⟨before, shape⟩ :=
            queue.sourceBatchBlocks_terminalSuffix publisher batch running done
          have later := next.1.sourceRunBlocks_after_termination next.2.1 rest done
          refine ⟨before, ?_⟩
          change next.2.2 ++ (next.1.sourceRunBlocks next.2.1 rest).2.2 = _
          rw [later, List.append_nil]
          exact shape
      | false =>
          obtain ⟨before, shape⟩ := ih next.1 next.2.1 done ended
          refine ⟨next.2.2 ++ before, ?_⟩
          change next.2.2 ++ (next.1.sourceRunBlocks next.2.1 rest).2.2 = _
          rw [shape, List.append_assoc]

/-- Removing only the terminal annotation yields blocks for the canonical history.
Witness: terminal-suffix and exact-output equations, cancelling the identical suffix.
Silent source blocks are retained, including failures at the last nonterminal boundary.
-/
theorem State.sourceRunBlocks_nonterminalBlocks (queue : State)
    (inputs : List (List GraphEvent)) (running : queue.terminated = false)
    : let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      ∃ before,
        (queue.sourceRunBlocks publisher inputs).2.2
          = before
            ++ (if (queue.runNormalized inputs).1.terminated then
                  [(none, [.workQueueTermination])]
                else
                  [])
        ∧ before.flatMap Prod.snd = queue.nonterminalAtoms inputs := by
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  obtain ⟨state, output⟩ := queue.sourceRunBlocks_agrees inputs
  have shape := queue.runNormalized_terminalShape inputs running
  cases ended : (queue.runNormalized inputs).1.terminated with
  | false =>
      refine ⟨(queue.sourceRunBlocks publisher inputs).2.2, by simp [publisher], ?_⟩
      rw [output, shape]
      simp [ended]
  | true =>
      obtain ⟨before, blocks⟩ := queue.sourceRunBlocks_terminalSuffix publisher inputs
        running (by rw [state]; exact ended)
      refine ⟨before, by simpa [ended] using blocks, ?_⟩
      rw [blocks] at output
      rw [shape, ended] at output
      simpa using output

/-- Actual accepted object cuts are bounded by the nonterminal history itself.
Witness: the optional final block has no source label and contributes no failure cut;
the unchanged earlier blocks give the sharper bound without moving or deleting cuts.
-/
theorem State.eligibleObjectFailureCuts_nonterminalBound (queue : State)
    (inputs : List (List GraphEvent)) (running : queue.terminated = false)
    : let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      ∀ entry ∈
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2),
        entry.1 ≤ (queue.nonterminalAtoms inputs).length := by
  obtain ⟨before, blocks, output⟩ := queue.sourceRunBlocks_nonterminalBlocks inputs running
  dsimp only
  rw [blocks, State.eligibleFailureBlocks_append, sourceObjectFailureCuts_append]
  have suffix (current : State) (offset : Nat) (done : Bool)
      : sourceObjectFailureCuts offset
          (current.eligibleFailureBlocks
            (if done then [(none, [.workQueueTermination])] else [])) = [] := by
    cases done <;> rfl
  rw [suffix, List.append_nil]
  intro entry member
  have bound := (sourceObjectFailureCuts_bounds 0 (queue.eligibleFailureBlocks before)
    entry member).2
  simpa only [State.eligibleFailureBlocks_outputs, output, Nat.zero_add] using bound

-----------------------------------------------------------------------------------------
-- Keep identical cuts, error counts, and announcement prefixes
-----------------------------------------------------------------------------------------

/-- A complete inventory restricts to a prefix when every cut already lies in it.
Witness: reuse ordering, uniqueness, and source provenance; prefix indexing preserves
the exact error equations without dropping or reordering a failure.
-/
theorem CompleteFailureInventory.prefix {work before after failures}
    (inventory : CompleteFailureInventory work (before ++ after) failures)
    (bounded : ∀ entry ∈ failures, entry.1 ≤ before.length)
    : CompleteFailureInventory work before failures := by
  refine ⟨inventory.1, inventory.2.1, ?_, ?_, ?_⟩
  · intro entry member
    exact ⟨bounded entry member, (inventory.2.2.1 entry member).2⟩
  · intro index group errors atEvent
    apply inventory.2.2.2.1 index group errors
    rwa [List.getElem?_append_left (List.getElem?_eq_some_iff.mp atEvent).1]
  · intro index stream errors atEvent
    apply inventory.2.2.2.2 index stream errors
    rwa [List.getElem?_append_left (List.getElem?_eq_some_iff.mp atEvent).1]

/-- Prefix observations at any retained cut are identical before and after removing
the final marker. Witness: the exact suffix equation and a cut inside the prefix.
-/
theorem State.nonterminalAtoms_take (queue : State) (inputs : List (List GraphEvent))
    (running : queue.terminated = false) {cut : Nat}
    (bounded : cut ≤ (queue.nonterminalAtoms inputs).length)
    : ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms).take cut
      = (queue.nonterminalAtoms inputs).take cut := by
  rw [queue.runNormalized_terminalShape inputs running,
    List.take_append_of_le_length bounded]

/-- Actual stream-failure cuts also lie within the nonterminal history.
Witness: the strict full-history index bound loses at most one terminal atom.
-/
theorem StreamFailureCuts.nonterminalBound {work : Execution.Work} {queue : State}
    {inputs : List (List GraphEvent)} {failures : FailureCuts}
    (cuts
      : StreamFailureCuts work
          ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms) failures)
    (running : queue.terminated = false)
    : ∀ entry ∈ failures, entry.1 ≤ (queue.nonterminalAtoms inputs).length := by
  intro entry member
  have bound := cuts.bound member
  rw [queue.runNormalized_terminalShape inputs running] at bound
  cases done : (queue.runNormalized inputs).1.terminated <;> simp [done] at bound <;> omega

namespace ConformancePlan

/-- Retain the actual cut partitions while constructing one complete announced inventory.
Witness: merge eligible object cuts and stream-failure cuts, prove their nonterminal
bounds, and transport unchanged counts and prior notices. Exposing the partitions lets
later safety proofs use these same cuts instead of choosing an incompatible inventory.
-/
theorem announcedFailures_with_cuts_exists {work : Execution.Work}
    {inputs : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true) (matching : PublicationMatching)
    : let queue := initialQueue work
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let objects :=
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
      ∃ streams,
        StreamFailureCuts work
          ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms) streams
        ∧ AnnouncedFailures work
            {
              events := queue.nonterminalAtoms inputs,
              matching,
              failures := mergeFailureCuts objects streams
            } := by
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let atoms := (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
  have running : queue.terminated = false := createWorkQueue_terminated _
  obtain ⟨producerMatching, _, values, _, covered⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage generated valid started
  obtain ⟨streams, cuts, _, supported⟩ := createWorkQueue_runNormalized_streamFailureCuts
    generated valid producerMatching (fun index event atEvent value =>
      (values index event atEvent value).1) covered
  let failures := mergeFailureCuts objects streams
  have bounded : ∀ entry ∈ failures,
      entry.1 ≤ (queue.nonterminalAtoms inputs).length := by
    intro entry member
    rcases List.mem_append.mp ((mergeFailureCuts_partition objects streams).mem_iff.mp member)
        with fromStream | fromObject
    · exact cuts.nonterminalBound running entry fromStream
    · exact queue.eligibleObjectFailureCuts_nonterminalBound inputs running entry fromObject
  have inventory := createWorkQueue_completeFailureInventory generated valid started cuts
    (fun entry member => (supported entry member).1)
  change CompleteFailureInventory work atoms failures at inventory
  rw [show atoms = queue.nonterminalAtoms inputs ++
    (if (queue.runNormalized inputs).1.terminated then [.workQueueTermination] else [])
      from queue.runNormalized_terminalShape inputs running] at inventory
  refine ⟨streams, cuts, inventory.prefix bounded, ?_⟩
  intro entry member
  have same := queue.nonterminalAtoms_take inputs running (bounded entry member)
  rw [← same]
  rcases List.mem_append.mp ((mergeFailureCuts_partition objects streams).mem_iff.mp member)
      with fromStream | fromObject
  · obtain ⟨ref, owners, opened⟩ := (supported entry fromStream).2.2
    exact ⟨[ref], owners, ref, List.mem_cons_self, opened.1⟩
  · obtain ⟨before, after, split⟩ := List.mem_iff_append.mp fromObject
    obtain ⟨owners, ref, structural, contributes, announced⟩ :=
      createWorkQueue_eligibleObjectFailureCuts_announcedOwner valid started split
    exact ⟨owners, structural, ref, contributes, announced⟩

/-- One complete announced inventory exists on the same history as the batching leaf.
Witness: forget only the cut-partition certificate from the stronger construction.
Earlier-cancellation exclusion remains a separate obligation.
-/
theorem announcedFailures_exists {work : Execution.Work} {inputs : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true) (matching : PublicationMatching)
    : ∃ failures,
        AnnouncedFailures work
          {
            events := (initialQueue work).nonterminalAtoms inputs, matching, failures
          } := by
  obtain ⟨streams, _, announced⟩ :=
    announcedFailures_with_cuts_exists generated valid started matching
  exact ⟨_, announced⟩

/-- Batching and announced error inventory share one actual history and one cut list.
Witness: construct the announced inventory, then instantiate the cut-independent batching
leaf. The chosen matching remains available to the outstanding causal/admission proofs.
-/
theorem batchShape_and_announcedFailures {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true) (matching : PublicationMatching)
    : ∃ failures,
        let witness : Witness :=
          { events := (initialQueue work).nonterminalAtoms inputs, matching, failures }
        BatchShape work inputs witness ∧ AnnouncedFailures work witness := by
  obtain ⟨failures, announced⟩ := announcedFailures_exists generated valid started matching
  exact ⟨failures, batchShape_holds valid matching failures, announced⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
