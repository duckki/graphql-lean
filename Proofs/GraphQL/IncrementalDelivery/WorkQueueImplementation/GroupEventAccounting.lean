import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicCarrierCoverage

/-! Successful group admission now leaves only carried-notice eligibility. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful group accounting shares the licensed mixed witness
-----------------------------------------------------------------------------------------

/-- Every successful group carrier accounts for all contributors at its strict prefix.
`work` supplies the structural tasks; `w` supplies the same output matching and failure
cuts used by the other conformance leaves. No internal registry premise is retained.
-/
def GroupSuccessesAccounted (work : Execution.Work) (w : Witness) : Prop :=
  ∀ (index : Nat) (group : Execution.DeliveryNode)
    (groups streams : List Execution.DeliveryNode),
    w.events[index]? = some (Execution.WorkQueueEvent.groupSuccess group groups streams)
    → NodeAccounted work w.matching (w.events.take index) w.failures group.ref

/-- A generated successful group carrier satisfies admission exactly when its notices do.
Witness: derive strict-prefix task accounting from the retained ledger, then reuse the
proven open-reference and historical-health reduction. Failure cuts remain frozen at the
carrier's start for announcement eligibility, as in the unchanged scheduler contract.
-/
theorem groupSuccessAllowed_iff_announcements
    {work inputs w index group groups streams}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (healthy : GroupSuccessesHealthy work w)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
        (.groupSuccess group groups streams)
      ↔ Announcements work (initialRefs work) w.matching
          (w.events.take index ++ [.groupSuccess group [] []])
          (w.failures.filter (fun entry => entry.1 ≤ index)) groups streams := by
  rw [groupSuccessAllowed_iff_accounting_and_announcements generated valid history healthy
    selected]
  exact and_iff_right (groupSuccess_nodeAccounted generated valid started history ledger selected)

/-- A successful group without carried notices satisfies its entire local admission rule.
Witness: every contributor publishes before closure and the empty notice list is valid.
The same canonical witness supplies open references, health, matching, and failure cuts.
-/
theorem groupSuccess_withoutNotices_allowed
    {work inputs w index group}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (healthy : GroupSuccessesHealthy work w)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupSuccess group [] []))
    : EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
        (.groupSuccess group [] []) := by
  apply (groupSuccessAllowed_iff_announcements generated valid started history healthy ledger
    selected).mpr
  simp [Announcements]

/-- The shared mixed witness now accounts for every successful group's structural tasks.
Witness: keep the existing matching, cuts, health, and ledger; derive all successful-group
accounting from that ledger rather than introducing another existential explanation.
Carried notices, group value admission, and terminal accounting remain separate targets.
-/
theorem mixed_groupAccountingCertificates {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ FailureAdmission work w
        ∧ StreamSuccessAdmission work w
        ∧ StreamPublicationReady work w
        ∧ GroupSuccessesHealthy work w
        ∧ GroupSuccessesAccounted work w
        ∧ BufferedClosureLedger work inputs w := by
  obtain ⟨w, history, shape, announced, uncancelled, failures, streams, ready, healthy,
    ledger⟩ := mixed_groupHealthCertificates_with_closureLedger generated valid started
  exact ⟨w, history, shape, announced, uncancelled, failures, streams, ready, healthy,
    fun _ _ _ _ selected => groupSuccess_nodeAccounted generated valid started history ledger
      selected, ledger⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
