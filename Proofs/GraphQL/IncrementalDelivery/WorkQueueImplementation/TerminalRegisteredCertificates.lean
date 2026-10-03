import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRegisteredTasks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FullControlAdmission

/-! Registered terminal accounting shares the already constructed complete admission witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The common admission witness also accounts for every registered task at termination.
Witness: retain its exact publication ledger and cut partition, derive failure visibility
and explanation, then apply the generated replay-to-retirement bridge. Registration is a
concrete premise only for the selected task; never-registered tasks remain a separate case.
-/
theorem mixed_registeredTerminalCertificates {work inputs}
    (premises : ReplayPremises work inputs)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ PublicationAdmission work w
        ∧ ControlAdmission work w
        ∧ Explains work (initialQueue work).initialGroups
            (initialQueue work).initialStreams w.events w.matching w.failures
        ∧ (((initialQueue work).runNormalized inputs).1.terminated = true
            → ∀ task ∈ ((initialQueue work).replayGraphEvents inputs.flatten).tasks,
                TaskAccounted work w.matching w.events w.failures task.occurrence)
        ∧ (((initialQueue work).runNormalized inputs).1.terminated = true
            → ∀ group dependencies,
                NodeAt work group .group dependencies none
                → NodeFailed work w.matching w.events w.failures group.ref
                  ∨ NodeAccounted work w.matching w.events w.failures group.ref) := by
  obtain ⟨w, history, shape, announced, uncancelled, publications, controls, _, _, _, _, _,
    ledger, _, _, _, _, _, streams, _, exactCuts⟩ :=
    mixed_admissionCertificates premises.generated premises.valid premises.started
  have explained := explains premises.initialized announced uncancelled publications controls
  have partition := exactCuts ▸ mergeFailureCuts_partition _ streams
  have visible := objectFailureContributions_visible premises.started announced.1 partition
  exact ⟨w, history, shape, announced, uncancelled, publications, controls, explained,
    fun ended task member => terminal_registeredTask_accounted premises.generated premises.valid
      premises.started history ledger explained visible ended member,
    fun ended group dependencies known => terminal_rootGroup_accounted premises.generated
      premises.valid premises.started history ledger explained visible ended known⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
