import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNonterminalCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformanceBatchShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InformativeFailureInventory

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
  exact queue.sourceBatchBlocks_startup_terminalSuffix publisher events running ended

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
  exact queue.sourceRunBlocks_startup_terminalSuffix publisher batches running ended

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
  exact queue.sourceRunBlocks_startup_nonterminalBlocks inputs running

/-- Source reporting cuts lie within the nonterminal history, including silent inputs.
Witness: the optional final block has no source label and contributes no failure cut.
-/
theorem State.sourceObjectFailureCuts_nonterminalBound (queue : State)
    (inputs : List (List GraphEvent)) (running : queue.terminated = false)
    : let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      ∀ entry ∈ sourceObjectFailureCuts 0 (queue.sourceRunBlocks publisher inputs).2.2,
        entry.1 ≤ (queue.nonterminalAtoms inputs).length := by
  exact queue.sourceObjectFailureCuts_startup_nonterminalBound inputs running

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

/-- A causal inventory restricts to a prefix when every cut already lies in it.
Witness: reuse ordering, uniqueness, and source provenance; prefix indexing preserves
the exact error equations without dropping or reordering a failure.
-/
theorem CausalFailureInventory.prefix {work before after failures}
    (inventory : CausalFailureInventory work (before ++ after) failures)
    (bounded : ∀ entry ∈ failures, entry.1 ≤ before.length)
    : CausalFailureInventory work before failures := by
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
  exact queue.nonterminalAtoms_startup_take inputs running bounded

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
  exact cuts.startup_nonterminalBound running

namespace ConformancePlan

/-- Actual replay supplies causal and reporting cuts on one nonterminal history.
Witness: select causal object cuts while retaining all reporting availability, merge
both with the same stream cuts, and remove only the optional final marker. Every causal
occurrence remains available at its original cut; no report count is reconstructed from
the selected causal subset.
-/
theorem announcedFailures_with_cuts_exists {work : Execution.Work}
    {inputs : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true) (matching : PublicationMatching)
    : let queue := initialQueue work
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let raw :=
        availableObjectFailureCuts work 0 (queue.sourceRunBlocks publisher inputs).2.2
      let objects :=
        informativeObjectFailureCuts work (queue.sourceRunBlocks publisher inputs).2.2
      ∃ streams,
        StreamFailureCuts work
          ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms) streams
        ∧ AnnouncedFailures work
            {
              events := queue.nonterminalAtoms inputs,
              matching,
              failures := mergeFailureCuts objects streams,
              reported := mergeFailureCuts raw streams
            } := by
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let blocks := (queue.sourceRunBlocks publisher inputs).2.2
  let atoms := (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms
  let raw := availableObjectFailureCuts work 0 blocks
  let objects := informativeObjectFailureCuts work blocks
  have running : queue.terminated = false := createWorkQueue_terminated _
  obtain ⟨producerMatching, _, values, _, covered⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage generated valid started
  obtain ⟨streams, cuts, _, supported⟩ := createWorkQueue_runNormalized_streamFailureCuts
    generated valid producerMatching (fun index event atEvent value =>
      (values index event atEvent value).1) covered
  let failures := mergeFailureCuts objects streams
  let reported := mergeFailureCuts raw streams
  have included : failures.Subset reported := by
    intro entry member
    apply (mergeFailureCuts_partition raw streams).mem_iff.mpr
    rcases List.mem_append.mp ((mergeFailureCuts_partition objects streams).mem_iff.mp member)
        with fromStream | fromObject
    · exact List.mem_append_left _ fromStream
    · exact List.mem_append_right _
        ((informativeObjectFailureCuts_sublist work blocks).subset fromObject)
  have reportingBound : ∀ entry ∈ reported,
      entry.1 ≤ (queue.nonterminalAtoms inputs).length := by
    intro entry member
    rcases List.mem_append.mp ((mergeFailureCuts_partition raw streams).mem_iff.mp member)
        with fromStream | fromObject
    · exact cuts.nonterminalBound running entry fromStream
    · exact queue.availableObjectFailureCuts_nonterminalBound work inputs running entry fromObject
  have causalBound : ∀ entry ∈ failures,
      entry.1 ≤ (queue.nonterminalAtoms inputs).length :=
    fun entry member => reportingBound entry (included member)
  have inventory := createWorkQueue_completeInformativeFailureInventory generated valid cuts
    (fun entry member => (supported entry member).1)
  have reportingInventory := createWorkQueue_completeFailureInventory generated valid cuts
    (fun entry member => (supported entry member).1)
  have reportedOwners : ∀ entry ∈ reported,
      ∃ owners, TaskHasOwners work entry.2 owners
        ∧ ∃ ref ∈ owners, ref ∈ announcedRefs (initialRefs work) (atoms.take entry.1) := by
    intro entry member
    rcases List.mem_append.mp ((mergeFailureCuts_partition raw streams).mem_iff.mp member)
        with fromStream | fromObject
    · obtain ⟨ref, owners, opened⟩ := (supported entry fromStream).2.2
      exact ⟨[ref], owners, ref, List.mem_cons_self, opened.1⟩
    · obtain ⟨owners, ref, structural, contributes, announced⟩ :=
        createWorkQueue_availableObjectFailureCuts_announcedOwner generated valid started fromObject
      exact ⟨owners, structural, ref, contributes, announced⟩
  have reporting := reportingInventory.failureReportingWitness reportedOwners
  have shape : atoms = queue.nonterminalAtoms inputs ++
      (if (queue.runNormalized inputs).1.terminated then [.workQueueTermination] else []) :=
    queue.runNormalized_terminalShape inputs running
  change CausalFailureInventory work atoms failures at inventory
  change FailureReportingWitness work (initialRefs work) atoms reported at reporting
  change CompleteFailureInventory work atoms reported at reportingInventory
  rw [shape] at inventory reporting reportingInventory
  have restricted := reporting.prefix
  have unchanged : reported.filter (fun entry => decide
      (entry.1 ≤ (queue.nonterminalAtoms inputs).length)) = reported := by
    apply List.filter_eq_self.mpr
    intro entry member
    exact of_decide_eq_true (by simpa using reportingBound entry member)
  rw [unchanged] at restricted
  refine ⟨streams, cuts, inventory.prefix causalBound, ?_, restricted, ?_,
    reportingInventory.prefix reportingBound⟩
  · intro entry member
    have same := queue.nonterminalAtoms_take inputs running (causalBound entry member)
    rw [← same]
    exact reportedOwners entry (included member)
  · intro cut occurrence member
    exact ⟨cut, included member, Nat.le_refl _⟩

/-- The joint inventories exist on the same history as the batching certificate. -/
theorem announcedFailures_exists {work : Execution.Work} {inputs : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true) (matching : PublicationMatching)
    : ∃ failures reported,
        AnnouncedFailures work
          {
            events := (initialQueue work).nonterminalAtoms inputs,
            matching,
            failures,
            reported
          } := by
  obtain ⟨streams, _, announced⟩ :=
    announcedFailures_with_cuts_exists generated valid started matching
  exact ⟨_, _, announced⟩

/-- Exact batching and both announced failure inventories share one witness. -/
theorem batchShape_and_announcedFailures {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true) (matching : PublicationMatching)
    : ∃ failures reported,
        let witness : Witness :=
          {
            events := (initialQueue work).nonterminalAtoms inputs,
            matching,
            failures,
            reported
          }
        BatchShape work inputs witness ∧ AnnouncedFailures work witness := by
  obtain ⟨failures, reported, announced⟩ :=
    announcedFailures_exists generated valid started matching
  exact ⟨failures, reported, batchShape_holds valid matching failures, announced⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
