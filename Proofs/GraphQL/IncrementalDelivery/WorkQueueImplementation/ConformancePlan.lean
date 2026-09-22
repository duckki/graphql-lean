import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceObservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureAnnouncementCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Termination

/-! Proof-only conformance obligations and checked dependency edges, not assumed laws. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent DeliveryNode)

-----------------------------------------------------------------------------------------
-- One replay and one shared explanation witness
-----------------------------------------------------------------------------------------

/-- The concrete initial state underlying the observable work queue. -/
abbrev initialQueue (work : Execution.Work) : State :=
  State.initialize (Work.fromExecution work)

/-- Initial notice keys used by every branch of the explanation. -/
def initialKeys (work : Execution.Work) : Keys :=
  ((initialQueue work).initialGroups ++ (initialQueue work).initialStreams).map
    DeliveryNode.key

/-- Public work premises and host laws specialized to one admitted input, together with
the constructor's derived initialization fact. No resulting-output property is assumed.
-/
structure ReplayPremises (work : Execution.Work) (inputs : List (List GraphEvent))
    : Prop where
  nonempty : work.size ≠ 0
  generated : ExecutedWork work
  initialized
    : Initializes work (initialQueue work).initialGroups
        (initialQueue work).initialStreams
  valid : ValidGraphEvents work inputs.flatten
  started : inputsStarted work inputs = true

/-- One proposed nontermination history, matching, and ordered failure inventory.
All obligations below use this same witness; independent existential choices do not
compose. These are proof data, not additional runtime state or source assumptions.
-/
structure Witness where
  events : List WorkQueueEvent
  matching : PublicationMatching
  failures : FailureCuts

-----------------------------------------------------------------------------------------
-- Shared-witness obligations, with no placeholder proofs
-----------------------------------------------------------------------------------------

/-- The witness regroups into the exact concrete outputs, including a final marker
exactly when the concrete replay has terminated. No output may be discarded.
Witness for the actual nonterminal history: `ConformanceBatchShape`'s `batchShape_holds`.
-/
def BatchShape (work : Execution.Work) (inputs : List (List GraphEvent)) (w : Witness)
    : Prop :=
  WorkBatching
    (w.events
      ++ if ((initialQueue work).runNormalized inputs).1.terminated then
            [.workQueueTermination]
          else
            [])
    ((initialQueue work).runNormalized inputs).2

/-- The shared cuts have exact error totals and previously announced contributing owners.
Witness on the actual nonterminal history: `ConformanceFailureHistory`'s
`announcedFailures_exists`, sharing the batching leaf's history without changing cut indices.
-/
def AnnouncedFailures (work : Execution.Work) (w : Witness) : Prop :=
  CompleteFailureInventory work w.events w.failures
  ∧ ∀ entry ∈ w.failures,
      ∃ owners,
        TaskHasOwners work entry.2 owners
        ∧ ∃ key ∈ owners, key ∈ announcedKeys (initialKeys work) (w.events.take entry.1)

/-- No accepted failure was cancelled by its ordered predecessors, using the same
publication matching as every output-admission and terminal obligation.
Witness on generated valid started replay: `MixedFailureWitness`'s
`mixed_failureCertificates`, together with batching and announced-failure accounting.
-/
def UncancelledFailures (work : Execution.Work) (w : Witness) : Prop :=
  ∀ before cut occurrence after,
    w.failures = before ++ (cut, occurrence) :: after
    → ¬TaskCancelled work w.matching (w.events.take cut) before occurrence

/-- Each actual value atom has the required payload, freshness, causal support, owner,
and any carried notices at its own output prefix.
-/
def PublicationAdmission (work : Execution.Work) (w : Witness) : Prop :=
  ∀ index event,
    w.events[index]? = some event
    → IsValue event
    → EventAllowed work (initialKeys work) w.matching (w.events.take index) w.failures
        event

/-- Every nonvalue atom satisfies the closure/error/notice rules. Since termination is
not allowed here, this also excludes stray termination markers from the witness.
-/
def ControlAdmission (work : Execution.Work) (w : Witness) : Prop :=
  ∀ index event,
    w.events[index]? = some event
    → ¬IsValue event
    → EventAllowed work (initialKeys work) w.matching (w.events.take index) w.failures
        event

/-- All structural tasks are published or justifiably cancelled (including failure)
at the end of this witness. Required only when concrete replay terminates.
-/
def TaskAccounting (work : Execution.Work) (w : Witness) : Prop :=
  ∀ occurrence owners producer payload,
    TaskAt work occurrence owners producer payload
    → TaskAccounted work w.matching w.events w.failures occurrence

/-- Every structural node is closed, or unannounced and failed/accounted for. Required
only when concrete replay terminates, including latent nodes and empty streams.
-/
def NodeAccounting (work : Execution.Work) (w : Witness) : Prop :=
  ∀ node kind dependencies producer,
    NodeAt work node kind dependencies producer
    → node.key ∈ completedKeys w.events
      ∨ node.key ∉ announcedKeys (initialKeys work) w.events
        ∧ (NodeFailed work w.matching w.events w.failures node.key
            ∨ NodeAccounted work w.matching w.events w.failures node.key)

/-- Seven obligations under one witness. This is an internal proof target, not
a premise added to the public conformance statement or the host event-source contract.
-/
structure Obligations (work : Execution.Work) (inputs : List (List GraphEvent))
    (w : Witness)
    : Prop where
  batching : BatchShape work inputs w
  announced : AnnouncedFailures work w
  uncancelled : UncancelledFailures work w
  publications : PublicationAdmission work w
  controls : ControlAdmission work w
  tasks
    : ((initialQueue work).runNormalized inputs).1.terminated = true
      → TaskAccounting work w
  nodes
    : ((initialQueue work).runNormalized inputs).1.terminated = true
      → NodeAccounting work w

/-- Construct compatible witnesses from actual replay and the existing premises.
Witness: `replayWitnessExists_holds` in the implementation proof's `Conformance` module.
-/
def ReplayWitnessExists : Prop :=
  ∀ work inputs, ReplayPremises work inputs → ∃ w, Obligations work inputs w

-----------------------------------------------------------------------------------------
-- Checked edges: licensing, event admission, and terminal accounting
-----------------------------------------------------------------------------------------

/-- Announced inventory plus earlier-cancellation exclusion licenses all failure cuts.
Witness: the existing complete-inventory equivalence, with no new failure premise.
-/
theorem failureWitness {work w} (announced : AnnouncedFailures work w)
    (uncancelled : UncancelledFailures work w)
    : FailureWitness work (initialKeys work) w.matching w.events w.failures :=
  (announced.1.failureWitness_iff_uncancelled announced.2).mpr uncancelled

/-- The two event classes exhaust the output history under the same licensed cuts.
Witness: split on value membership and assemble the exact public explanation.
-/
theorem explains {work w}
    (initialized
      : Initializes work (initialQueue work).initialGroups
          (initialQueue work).initialStreams)
    (announced : AnnouncedFailures work w) (uncancelled : UncancelledFailures work w)
    (publications : PublicationAdmission work w) (controls : ControlAdmission work w)
    : Explains work (initialQueue work).initialGroups (initialQueue work).initialStreams
        w.events w.matching w.failures := by
  refine ⟨initialized, failureWitness announced uncancelled, ?_⟩
  intro index event atIndex
  classical
  by_cases value : IsValue event
  · exact publications index event atIndex value
  · exact controls index event atIndex value

/-- Task and node coverage are exactly the two terminal-accounting clauses.
Witness: pair the coverage proofs without changing their matching or cuts.
-/
theorem terminal {work w} (tasks : TaskAccounting work w) (nodes : NodeAccounting work w)
    : Terminal work (initialKeys work) w.matching w.events w.failures :=
  ⟨tasks, nodes⟩

private theorem batching_termination_mem {events batches}
    (batching : WorkBatching events batches)
    : WorkQueueEvent.workQueueTermination ∈ batches.flatten
      ↔ WorkQueueEvent.workQueueTermination ∈ events := by
  induction batching with
  | nil => simp
  | cons nonempty values subsequent ih =>
      simp only [List.flatten_cons, List.mem_append, values.termination_mem, ih]

/-- A shared certificate gives a complete run precisely when concrete replay ended.
The reverse edge needs no new conjecture: an abstract run contains a termination
marker, batching preserves it, and explained nontermination events cannot contain it.
-/
theorem run_iff_terminated {work inputs w}
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (batching : BatchShape work inputs w)
    (accounted
      : ((initialQueue work).runNormalized inputs).1.terminated = true
        → Terminal work (initialKeys work) w.matching w.events w.failures)
    : AdmissibleRun work ((initialQueue work).normalizedHistory inputs)
      ↔ ((initialQueue work).runNormalized inputs).1.terminated = true := by
  constructor
  · rintro ⟨events, matching, failures, _, _, grouped⟩
    have marker := (batching_termination_mem grouped).mpr
      (by simp : WorkQueueEvent.workQueueTermination ∈ events ++ [.workQueueTermination])
    have actual := (batching_termination_mem batching).mp marker
    cases done : ((initialQueue work).runNormalized inputs).1.terminated with
    | false =>
        simp only [done, Bool.false_eq_true, ↓reduceIte, List.append_nil] at actual
        exact False.elim (explained.noTermination actual)
    | true => rfl
  · intro done
    refine ⟨w.events, w.matching, w.failures, explained, accounted done, ?_⟩
    simpa only [BatchShape, State.normalizedHistory, done, ↓reduceIte] using batching

/-- Every certified replay gives either an interrupted prefix or a complete run.
Witness: reuse the exact batching and branch only on the implementation's final flag.
-/
theorem validHistory {work inputs w}
    (initialized
      : Initializes work (initialQueue work).initialGroups
          (initialQueue work).initialStreams)
    (obligations : Obligations work inputs w)
    : ValidHistory work ((initialQueue work).normalizedHistory inputs) := by
  have explained := explains initialized obligations.announced
    obligations.uncancelled obligations.publications obligations.controls
  cases done : ((initialQueue work).runNormalized inputs).1.terminated with
  | false =>
      left
      refine ⟨w.events, w.matching, w.failures, explained, ?_⟩
      simpa only [BatchShape, State.normalizedHistory, done, Bool.false_eq_true,
        ↓reduceIte, List.append_nil]
        using obligations.batching
  | true =>
      right
      exact (run_iff_terminated explained obligations.batching
        (fun ended => terminal (obligations.tasks ended) (obligations.nodes ended))).mpr done

-----------------------------------------------------------------------------------------
-- Checked adapter edges: account for outputs and reflect termination
-----------------------------------------------------------------------------------------

/-- Restrict witness construction to inputs actually admitted by one host source.
This is a proof target derived below from the general replay conjecture.
-/
def AdmittedReplayWitnesses (work : Execution.Work)
    (source : EventSource (List GraphEvent))
    : Prop :=
  ∀ inputs, source.admissible inputs → ∃ w, Obligations work inputs w

/-- Shared certificates for source-admitted inputs account for every admitted output.
Witness: recover an actual replay from the source adapter and use its valid history.
-/
theorem accountsForWork {work source}
    (initialized
      : Initializes work (initialQueue work).initialGroups
          (initialQueue work).initialStreams)
    (witnesses : AdmittedReplayWitnesses work source)
    : (createWorkQueueForSchedule work source).AccountsForWork work := by
  intro outputs admitted
  obtain ⟨inputs, accepted, rfl⟩ := admitted
  obtain ⟨w, obligations⟩ := witnesses inputs accepted
  exact validHistory initialized obligations

/-- The adapter's finished predicate agrees with admitted complete abstract runs.
Witness: use the same actual replay in both directions and reflect its final marker.
-/
theorem terminationMatchesWork {work source}
    (initialized
      : Initializes work (initialQueue work).initialGroups
          (initialQueue work).initialStreams)
    (witnesses : AdmittedReplayWitnesses work source)
    : (createWorkQueueForSchedule work source).TerminationMatchesWork work := by
  intro outputs
  constructor
  · rintro ⟨inputs, accepted, same, done⟩
    obtain ⟨w, obligations⟩ := witnesses inputs accepted
    refine ⟨⟨inputs, accepted, same⟩, ?_⟩
    have explained := explains initialized obligations.announced obligations.uncancelled
      obligations.publications obligations.controls
    have run := (run_iff_terminated explained obligations.batching
      (fun ended => terminal (obligations.tasks ended) (obligations.nodes ended))).mpr done
    cases same
    exact run
  · rintro ⟨⟨inputs, accepted, same⟩, run⟩
    obtain ⟨w, obligations⟩ := witnesses inputs accepted
    refine ⟨inputs, accepted, same, ?_⟩
    have explained := explains initialized obligations.announced obligations.uncancelled
      obligations.publications obligations.controls
    apply (run_iff_terminated explained obligations.batching
      (fun ended => terminal (obligations.tasks ended) (obligations.nodes ended))).mp
    cases same
    exact run

-----------------------------------------------------------------------------------------
-- Checked adapter: replay certificates establish one observable queue's conformance
-----------------------------------------------------------------------------------------

/-- Constructed replay witnesses establish conformance for a supplied initialized queue.
Witness: specialize to admitted inputs, apply both adapter edges, and reuse output-prefix
realization. The final `Conformance` module constructs the witnesses and derives the
initialization fact. This lower-level adapter adds no source law.
-/
theorem conforms_of_replayWitnessExists (witnesses : ReplayWitnessExists)
    {work : Execution.Work} {schedule : EventSource (List GraphEvent)}
    (generated : ExecutedWork work) (nonempty : work.size ≠ 0)
    (initialized
      : Initializes work (initialQueue work).initialGroups
          (initialQueue work).initialStreams)
    (source : schedule.ValidFor work)
    : (createWorkQueueForSchedule work schedule).Conforms work := by
  have admitted : AdmittedReplayWitnesses work schedule := by
    intro inputs accepted
    obtain ⟨valid, started⟩ := source.2.2.2 inputs accepted
    exact witnesses work inputs
      ⟨nonempty, generated, initialized, valid, started⟩
  exact ⟨createWorkQueueForSchedule_initialized work schedule source.2.1,
    createWorkQueueForSchedule_prefixClosed work schedule source.2.2.1,
    accountsForWork initialized admitted, terminationMatchesWork initialized admitted⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
