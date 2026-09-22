import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRegisteredCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducedStreamNoticeCoverage

/-! Producer-free nodes and successful-item streams share the complete admission witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Root nodes need no recursive producer-classification premise
-----------------------------------------------------------------------------------------

/-- The existing mixed witness satisfies terminal node accounting for every root node.
Witness: registered contributors account for root groups; every root stream is initially
announced and concretely completed. Successful source items' child streams also complete
on this same witness. No alternate matching, cut inventory, or admission premise is used.
-/
theorem mixed_rootTerminalCertificates {work inputs}
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
            → ∀ node kind dependencies,
                NodeAt work node kind dependencies none
                → node.key ∈ completedKeys w.events
                  ∨ node.key ∉ announcedKeys (initialKeys work) w.events
                    ∧ (NodeFailed work w.matching w.events w.failures node.key
                        ∨ NodeAccounted work w.matching w.events w.failures node.key))
        ∧ (((initialQueue work).runNormalized inputs).1.terminated = true
            → ∀ node dependencies address index,
                NodeAt work node .stream dependencies (some (.item address index))
                → Occurrence.item address index
                  ∈ inputs.flatten.flatMap GraphEvent.successes
                → node.key ∈ completedKeys w.events) := by
  obtain ⟨w, history, shape, announced, uncancelled, publications, controls, explained,
    registered, roots⟩ := mixed_registeredTerminalCertificates premises
  refine ⟨w, history, shape, announced, uncancelled, publications, controls, explained,
    registered, ?_, ?_⟩
  · intro ended node kind dependencies known
    cases kind with
    | stream => exact .inl (terminal_rootStream_completed premises.valid premises.started
        history ended known)
    | group =>
        classical
        by_cases noticed : node.key ∈ announcedKeys (initialKeys work) w.events
        · exact .inl (announced_terminalCompleted premises.generated premises.valid
            premises.started history ended noticed)
        · exact .inr ⟨noticed, roots ended node dependencies known⟩
  · intro ended node dependencies address index known success
    exact terminal_itemProducedStream_completed premises.generated premises.valid
      premises.started history ended known success

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
