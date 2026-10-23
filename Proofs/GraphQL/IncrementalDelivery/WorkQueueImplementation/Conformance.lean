import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalGeneratedTasks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConstructorInitialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalObjectReporting

/-! The executable reference queue satisfies the public WorkQueue contract. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- All task accounting plus concrete notice tracking supplies the final node clause
-----------------------------------------------------------------------------------------

/-- Terminal task accounting supplies every unannounced node's accounting alternative.
Witness: all its contributing tasks are accounted; concrete tracking closes every announced
ref. Empty nodes satisfy the contributing-task condition vacuously, as the contract allows.
-/
theorem terminal_nodes_of_tasks {work inputs w}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (tasks : TaskAccounting work w)
    : NodeAccounting work w := by
  intro node kind dependencies producer known
  classical
  by_cases announced : node.ref ∈ announcedRefs (initialRefs work) w.events
  · exact .inl (announced_terminalCompleted generated valid started history ended announced)
  · refine .inr ⟨announced, .inr ?_⟩
    intro occurrence owners descriptor contributes
    obtain ⟨parent, payload, task⟩ := descriptor
    exact tasks occurrence owners parent payload task

-----------------------------------------------------------------------------------------
-- One canonical witness discharges every construction leaf jointly
-----------------------------------------------------------------------------------------

/-- Every generated valid started replay has all eight compatible conformance certificates.
Witness: retain the full admission construction's exact history, matching, ledger, and cuts.
Producer-rank induction supplies terminal task accounting; actual tracking and contributor
coverage supply terminal node accounting. Actual failure origins, stream closure, and
producer inheritance supply cancellation reports. No construction leaf remains an assumption.
-/
theorem replayWitnessExists_holds : ReplayWitnessExists := by
  intro work inputs premises
  obtain ⟨w, history, shape, announced, uncancelled, publications, controls, _, _, _, _, _,
    ledger, _, _, _, _, _, streams, _, exactCuts⟩ :=
    mixed_admissionCertificates premises.generated premises.valid premises.started
  have explained := explains premises.initialized announced uncancelled publications controls
  have partition := exactCuts ▸ mergeFailureCuts_partition _ streams
  have visible := objectFailureContributions_visible premises.started announced.1 partition
  have tasks := fun ended => terminal_generatedTasks_accounted premises.generated premises.valid
    premises.started history publications ledger explained visible ended
  exact ⟨w, shape, announced, uncancelled, publications, controls, tasks,
    fun ended => terminal_nodes_of_tasks premises.generated premises.valid premises.started
      history ended (tasks ended),
    fun ended => terminal_cancellationReporting premises.generated premises.valid
      premises.started history publications ledger explained ended⟩

end ConformancePlan

-----------------------------------------------------------------------------------------
-- Public conformance witness
-----------------------------------------------------------------------------------------

/-- The executable reference queue satisfies conformance with asynchronous initial activation.
Witness: `ExecutedWork.initializes` derives the constructor's initial-notice law;
`ConformancePlan.replayWitnessExists_holds` constructs every actual replay's shared
explanation and terminal certificates. The checked adapter then proves all four contract
clauses using only the work and event-source assumptions in `createWorkQueueForScheduleConforms`.
-/
theorem createWorkQueueForScheduleConforms_holds
    : createWorkQueueForScheduleConforms {} := by
  intro work schedule generated nonempty valid
  have nonempty := (Execution.Work.isEmpty_eq_false work).mp nonempty
  exact ConformancePlan.conforms_of_replayWitnessExists
    ConformancePlan.replayWitnessExists_holds generated nonempty
    (generated.initializes nonempty) valid

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
