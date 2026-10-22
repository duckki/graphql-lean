import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformanceBatchShape

/-! Startup failure cuts keep their exact indices when removing only the final terminal block. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A seeded batch that terminates ends with an unlabelled terminal block. -/
theorem State.sourceBatchBlocks_startup_terminalSuffix (queue : State)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    (running : queue.terminated = false)
    (ended : (queue.sourceBatchBlocks publisher events).1.terminated = true)
    : ∃ before,
        (queue.sourceBatchBlocks publisher events).2.2
        = before ++ [(none, [.workQueueTermination])] := by
  have flag := (queue.sourceOutputBlocks_terminalShape publisher events
    (GraphEvent.availableFailures events)).1
  simp only [State.sourceBatchBlocks, running, Bool.false_eq_true, ↓reduceIte] at ended ⊢
  split
  · exact ⟨_, rfl⟩
  · simp_all

/-- Completed seeded replay ends with that same terminal block and no later source labels. -/
theorem State.sourceRunBlocks_startup_terminalSuffix (queue : State)
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
            queue.sourceBatchBlocks_startup_terminalSuffix publisher batch running done
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

/-- Removing only the final terminal block retains every source and startup report block. -/
theorem State.sourceRunBlocks_startup_nonterminalBlocks (queue : State)
    (inputs : List (List GraphEvent))
    (running : queue.terminated = false)
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
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  obtain ⟨state, _, output⟩ := queue.sourceRunBlocks_withPublisher_agrees publisher inputs
  change (queue.sourceRunBlocks publisher inputs).1
    = (queue.runNormalized inputs).1 at state
  change (queue.sourceRunBlocks publisher inputs).2.2.flatMap Prod.snd
    = (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms at output
  have shape := queue.runNormalized_terminalShape inputs running
  cases ended : (queue.runNormalized inputs).1.terminated with
  | false =>
      refine ⟨(queue.sourceRunBlocks publisher inputs).2.2, by simp [publisher], ?_⟩
      rw [output, shape]
      simp [ended]
  | true =>
      obtain ⟨before, blocks⟩ := queue.sourceRunBlocks_startup_terminalSuffix publisher inputs
        running (by rw [state]; exact ended)
      refine ⟨before, by simpa [ended] using blocks, ?_⟩
      rw [blocks] at output
      rw [shape, ended] at output
      simpa using output

/-- Actual startup source-reporting cuts remain within the unchanged nonterminal history. -/
theorem State.sourceObjectFailureCuts_startup_nonterminalBound (queue : State)
    (inputs : List (List GraphEvent))
    (running : queue.terminated = false)
    : let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      ∀ entry ∈ sourceObjectFailureCuts 0 (queue.sourceRunBlocks publisher inputs).2.2,
        entry.1 ≤ (queue.nonterminalAtoms inputs).length := by
  obtain ⟨before, blocks, output⟩ := queue.sourceRunBlocks_startup_nonterminalBlocks inputs
    running
  dsimp only
  rw [blocks, sourceObjectFailureCuts_append]
  have suffix (offset : Nat) (done : Bool) : sourceObjectFailureCuts offset
      (if done then [(none, [.workQueueTermination])] else []) = [] := by
    cases done <;> rfl
  rw [suffix, List.append_nil]
  intro entry member
  have bound := (sourceObjectFailureCuts_bounds 0 before entry member).2
  simpa only [output, Nat.zero_add] using bound

/-- Source and cached-report availability cuts remain inside the same nonterminal history. -/
theorem State.availableObjectFailureCuts_nonterminalBound (queue : State)
    (work : Execution.Work) (inputs : List (List GraphEvent))
    (running : queue.terminated = false)
    : let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      ∀ entry ∈
        availableObjectFailureCuts work 0 (queue.sourceRunBlocks publisher inputs).2.2,
        entry.1 ≤ (queue.nonterminalAtoms inputs).length := by
  dsimp only
  intro entry member
  rcases availableObjectFailureCuts_origin member with source | report
  · exact queue.sourceObjectFailureCuts_startup_nonterminalBound inputs running entry source
  · obtain ⟨index, group, errors, _, selected, cut, _⟩ := groupReportCandidateCuts_origin report
    rw [(queue.sourceRunBlocks_agrees inputs).2,
      queue.runNormalized_terminalShape inputs running] at selected
    have bound : index < (queue.nonterminalAtoms inputs).length := by
      by_cases inside : index < (queue.nonterminalAtoms inputs).length
      · exact inside
      · rw [List.getElem?_append_right (Nat.le_of_not_gt inside)] at selected
        cases done : (queue.runNormalized inputs).1.terminated <;> simp [done] at selected
        have impossible := List.mem_singleton.mp (List.mem_of_getElem? selected)
        cases impossible
    simpa only [cut, Nat.zero_add] using Nat.le_of_lt bound

/-- Startup failure cuts retain identical atomic prefixes after removing final termination. -/
theorem State.nonterminalAtoms_startup_take (queue : State)
    (inputs : List (List GraphEvent))
    (running : queue.terminated = false) {cut : Nat}
    (bounded : cut ≤ (queue.nonterminalAtoms inputs).length)
    : ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms).take cut
      = (queue.nonterminalAtoms inputs).take cut := by
  rw [queue.runNormalized_terminalShape inputs running,
    List.take_append_of_le_length bounded]

/-- Stream-failure positions also lie inside the exact startup nonterminal projection. -/
theorem StreamFailureCuts.startup_nonterminalBound {work : Execution.Work} {queue : State}
    {inputs : List (List GraphEvent)} {failures : FailureCuts}
    (cuts
      : StreamFailureCuts work
          ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms) failures)
    (running : queue.terminated = false)
    : ∀ entry ∈ failures, entry.1 ≤ (queue.nonterminalAtoms inputs).length := by
  intro entry member
  have bound := cuts.bound member
  rw [queue.runNormalized_terminalShape inputs running] at bound
  cases done : (queue.runNormalized inputs).1.terminated <;>
    simp [done] at bound <;> omega

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
