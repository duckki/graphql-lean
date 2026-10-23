import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupFullAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupTerminalReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupTerminalNodes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConstructorInitialization
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! One actual startup replay supplies compatible explanation and terminal certificates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Actual startup replay satisfies every history obligation on one witness.
The full admission construction supplies the exact history, matching and separate causal
and reporting cuts. Structural terminal proofs reuse that same explanation and ledger.
Initial notices are transported by their proved equality, including removed root groups.
No output property or terminal accounting is added to the source premises.
-/
theorem startup_replayCertificates {work inputs} (generated : ExecutedWork work)
    (nonempty : work.size ≠ 0) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∃ w : Witness,
        WorkBatching
          (w.events
            ++ if (initial.runNormalized inputs).1.terminated then
                  [.workQueueTermination]
                else
                  [])
          (initial.runNormalized inputs).2
        ∧ Explains work initial.initialGroups initial.initialStreams
            w.events w.matching w.failures
        ∧ ((initial.runNormalized inputs).1.terminated = true
            → Terminal work
                ((initial.initialGroups ++ initial.initialStreams).map
                  Execution.DeliveryNode.ref)
                w.matching w.events w.failures) := by
  obtain ⟨w, history, shape, announced, uncancelled, publications, controls, _, _, _, _, _,
    _, _, _, _, ledger, _⟩ :=
    startup_admissionCertificates generated startup matched valid started
  have explained := explains (generated.initializes nonempty) announced uncancelled
    publications controls
  have tasks := fun ended => startup_terminal_generatedTasks_accounted generated startup
    matched valid started history publications ledger explained ended
  refine ⟨w, shape, ?_, ?_⟩
  · simpa only [State.initializeWithStartup_initialGroups,
      State.initializeWithStartup_initialStreams] using explained
  · intro ended
    have accounted := terminal (tasks ended)
      (startup_terminal_nodes_of_tasks generated startup valid history ended (tasks ended))
      (startup_terminal_cancellationReporting generated startup matched valid started history
        publications ledger explained ended)
    simpa only [State.initializeWithStartup_initialGroups,
      State.initializeWithStartup_initialStreams, initialRefs, initialQueue] using accounted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
