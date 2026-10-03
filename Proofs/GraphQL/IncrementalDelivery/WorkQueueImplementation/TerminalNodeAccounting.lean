import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalReduction
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalStreamCompletion

/-! The remaining terminal construction concerns only unannounced structural nodes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Isolate the still-open latent-node branch without strengthening the public contract
-----------------------------------------------------------------------------------------

/-- Every structural node omitted from the witness's notices is failed or fully accounted.
The work and witness are the same as `NodeAccounting`; this is a proof-only remaining
construction target, not an assumed property of the event source or emitted outputs.
-/
def UnannouncedNodeAccounting (work : Execution.Work) (w : Witness) : Prop :=
  ∀ node kind dependencies producer,
    NodeAt work node kind dependencies producer
    → node.ref ∉ announcedRefs (initialRefs work) w.events
    → NodeFailed work w.matching w.events w.failures node.ref
      ∨ NodeAccounted work w.matching w.events w.failures node.ref

/-- Actual terminal node accounting reduces to the unannounced-node construction.
Witness: canonical replay already completes every announced ref; the remaining branch
supplies precisely the failed/accounted alternative at the same matching and failure cuts.
-/
theorem nodeAccounting_of_unannounced {work inputs} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (latent : UnannouncedNodeAccounting work w)
    : NodeAccounting work w := by
  intro node kind dependencies producer known
  classical
  by_cases announced : node.ref ∈ announcedRefs (initialRefs work) w.events
  · exact .inl (announced_terminalCompleted generated valid started history ended announced)
  · exact .inr ⟨announced, latent node kind dependencies producer known announced⟩

/-- The unchanged conformance certificate needs only the latent branch at termination.
Witness: derive announced-node completion from concrete replay, then derive task accounting
from explained node accounting. Admission leaves remain explicit, still-open constructions.
-/
theorem obligations_of_unannouncedNodeAccounting {work inputs w}
    (premises : ReplayPremises work inputs)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (batching : BatchShape work inputs w) (announced : AnnouncedFailures work w)
    (uncancelled : UncancelledFailures work w)
    (publications : PublicationAdmission work w) (controls : ControlAdmission work w)
    (latent
      : ((initialQueue work).runNormalized inputs).1.terminated = true
        → UnannouncedNodeAccounting work w)
    : Obligations work inputs w :=
  obligations_of_nodeAccounting premises batching announced uncancelled publications
    controls
    (fun ended =>
      nodeAccounting_of_unannounced premises.generated premises.valid
        premises.started history ended (latent ended))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
