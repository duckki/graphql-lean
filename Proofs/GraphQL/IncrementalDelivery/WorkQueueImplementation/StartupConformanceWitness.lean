import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupAnnouncedFailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNonterminalCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupBatchShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformanceFailureHistory

/-! Actual startup histories instantiate the existing conformance witness and failure clauses. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial and later object availability cuts stay inside the exact nonterminal history. -/
theorem InitialStartup.objectReportingCuts_nonterminalBound {work : Execution.Work}
    (startup : InitialStartup) (inputs : List (List GraphEvent))
    : let initial := State.initialize (Work.fromExecution work) startup
      ∀ entry ∈ startup.objectReportingCuts work inputs,
        entry.1 ≤ (initial.nonterminalAtoms inputs).length := by
  dsimp only
  let initial := State.initialize (Work.fromExecution work) startup
  intro entry member
  change entry ∈ prependInitialReporting _ _ at member
  rcases List.mem_append.mp member with early | later
  · obtain ⟨occurrence, _, same⟩ := List.mem_map.mp early
    rw [← same]
    exact Nat.zero_le _
  · have retained := (List.mem_filter.mp later).1
    have candidate := (firstReportingCuts_sublist [] _).subset retained
    let refs := (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
    let publisher : IncrementalPublisher :=
      { active := initial.initialGroups ++ initial.initialStreams }
    let blocks := (initial.sourceRunBlocks publisher inputs).2.2
    let observations := startup.reportingObservations work refs ++ blocks.filterMap Prod.fst
    have partition := interleaveFailureCuts_partition (sourceObjectFailureCuts 0 blocks)
      (groupReportCandidateCuts work observations 0 (blocks.flatMap Prod.snd))
    rcases List.mem_append.mp (partition.mem_iff.mp candidate) with report | source
    · obtain ⟨index, group, errors, _, selected, cut, _⟩ := groupReportCandidateCuts_origin report
      rw [(initial.sourceRunBlocks_agrees inputs).2,
        initial.runNormalized_terminalShape inputs (State.initializeWithStartup_terminated _ startup)]
        at selected
      have within : index < (initial.nonterminalAtoms inputs).length := by
        by_cases inside : index < (initial.nonterminalAtoms inputs).length
        · exact inside
        · rw [List.getElem?_append_right (Nat.le_of_not_gt inside)] at selected
          cases done : (initial.runNormalized inputs).1.terminated <;> simp [done] at selected
          have impossible := List.mem_singleton.mp (List.mem_of_getElem? selected)
          cases impossible
      simpa only [cut, Nat.zero_add] using Nat.le_of_lt within
    · exact initial.sourceObjectFailureCuts_startup_nonterminalBound inputs
        (State.initializeWithStartup_terminated _ startup) entry source

/-- One existing conformance witness retains actual startup batching and announced failures.
Every cut, error count and source position is unchanged when removing the sole terminal
block. The public admission and terminal propositions are not assumed or weakened.
-/
theorem ExecutedWork.startup_batchShape_and_announcedFailures {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {inputs : List (List GraphEvent)}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true) (matching : PublicationMatching)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∃ w : ConformancePlan.Witness,
        w.events = initial.nonterminalAtoms inputs
        ∧ w.matching = matching
        ∧ WorkBatching
            (w.events
              ++ if (initial.runNormalized inputs).1.terminated then
                    [.workQueueTermination]
                  else
                    [])
            (initial.runNormalized inputs).2
        ∧ ConformancePlan.AnnouncedFailures work w
        ∧ ∃ streams,
            StreamFailureCuts work
              ((initial.runNormalized inputs).2.flatten.flatMap publicationAtoms) streams
            ∧ w.failures
              = mergeFailureCuts (startup.informativeObjectFailureCuts work inputs)
                  streams
            ∧ w.reported
              = mergeFailureCuts (startup.objectReportingCuts work inputs) streams := by
  let initial := State.initialize (Work.fromExecution work) startup
  let queue := initial
  let atoms := (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms
  obtain ⟨streams, failures, reported, cuts, causalEq, reportEq, inventory, reportingInventory,
    reporting, available, announced⟩ :=
    generated.startup_announcedFailureInventories startup matched valid started
  have running : queue.terminated = false := State.initializeWithStartup_terminated _ startup
  have reportingBound : ∀ entry ∈ reported,
      entry.1 ≤ (queue.nonterminalAtoms inputs).length := by
    intro entry member
    rw [reportEq] at member
    rcases List.mem_append.mp ((mergeFailureCuts_partition _ streams).mem_iff.mp member)
      with stream | object
    · exact cuts.startup_nonterminalBound running entry stream
    · exact startup.objectReportingCuts_nonterminalBound inputs entry object
  have causalBound : ∀ entry ∈ failures,
      entry.1 ≤ (queue.nonterminalAtoms inputs).length := by
    intro entry member
    rw [causalEq] at member
    rcases List.mem_append.mp ((mergeFailureCuts_partition _ streams).mem_iff.mp member)
      with stream | object
    · exact cuts.startup_nonterminalBound running entry stream
    · exact startup.objectReportingCuts_nonterminalBound inputs entry
        ((selectObjectFailureCuts_sublist work [] _).subset object)
  have noticeEq : ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
      = ConformancePlan.initialRefs work := by
    simp only [queue, initial, State.initializeWithStartup_initialGroups,
      State.initializeWithStartup_initialStreams, ConformancePlan.initialRefs,
      ConformancePlan.initialQueue]
  change CausalFailureInventory work atoms failures at inventory
  change CompleteFailureInventory work atoms reported at reportingInventory
  change FailureReportingWitness work
    ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref) atoms reported
      at reporting
  rw [noticeEq] at reporting
  have shape := queue.runNormalized_terminalShape inputs running
  change atoms = _ at shape
  rw [shape] at inventory reportingInventory reporting
  have restricted := reporting.prefix
  have unchanged : reported.filter (fun entry => decide
      (entry.1 ≤ (queue.nonterminalAtoms inputs).length)) = reported := by
    apply List.filter_eq_self.mpr
    intro entry member
    simpa using reportingBound entry member
  rw [unchanged] at restricted
  refine ⟨
    { events := queue.nonterminalAtoms inputs, matching, failures, reported },
    rfl,
    rfl,
    queue.runNormalized_batchShape inputs running valid.nonemptyItems,
    ⟨
      inventory.prefix causalBound,
      ?_,
      ⟨restricted, available, reportingInventory.prefix reportingBound⟩
    ⟩,
    streams,
    cuts,
    causalEq,
    reportEq
  ⟩
  intro entry member
  obtain ⟨owners, known, ref, owns, seen⟩ := announced entry member
  change ref ∈ announcedRefs
    ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
    (atoms.take entry.1) at seen
  rw [noticeEq, queue.nonterminalAtoms_startup_take inputs running
    (causalBound entry member)] at seen
  exact ⟨owners, known, ref, owns, seen⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
