import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalReduction
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalGroupCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalNodeAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.EndpointFailureAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FullPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FullControlAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRegisteredCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalGeneratedRoots
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalItemProducedNodes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalObjectProducedGroups
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectProducedStreamNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Conformance

/-! Exact-target and shared-certificate checks for the proof-only conformance graph. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerConformancePlan
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The public target holds for every executed work and valid event source.
Witness: `createWorkQueueForScheduleConforms_holds`, without any internal construction hypothesis.
-/
example : createWorkQueueForScheduleConforms := createWorkQueueForScheduleConforms_holds

/-- All seven construction leaves are proved together on one replay witness.
Witness: `replayWitnessExists_holds`, not seven independent existential certificates.
-/
example : ReplayWitnessExists := replayWitnessExists_holds

/-- The first five construction leaves hold jointly for every generated valid started run.
Witness: all event admission retains the same batching, matching, and licensed cuts,
including every group/item-carried notice. No admission premise is supplied.
-/
example {work inputs} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ PublicationAdmission work w
        ∧ ControlAdmission work w := by
  obtain ⟨w, history, batching, announced, uncancelled, publications, controls, _⟩ :=
    mixed_admissionCertificates generated valid started
  exact ⟨w, history, batching, announced, uncancelled, publications, controls⟩

/-- The actual nonterminal history has a complete abstract explanation under public premises.
Witness: the constructed common matching/cuts, including all value and control admission;
no simulated queue invariant or event-admission callback is supplied by the caller.
-/
example {work inputs} (premises : ReplayPremises work inputs)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ Explains work (initialQueue work).initialGroups
            (initialQueue work).initialStreams w.events w.matching w.failures :=
  mixed_explanation premises

/-- Terminal registered-task accounting shares the existing admission witness.
Witness: the constructive mixed certificate retains one matching and failure inventory;
the terminal premise supplies no task, node, publication, or root-coverage hypothesis.
-/
example {work inputs} (premises : ReplayPremises work inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    : ∃ w : Witness,
        BatchShape work inputs w
        ∧ PublicationAdmission work w
        ∧ ControlAdmission work w
        ∧ ∀ task ∈ ((initialQueue work).replayGraphEvents inputs.flatten).tasks,
            TaskAccounted work w.matching w.events w.failures task.occurrence := by
  obtain ⟨w, _, batching, _, _, publications, controls, _, registered, _⟩ :=
    mixed_registeredTerminalCertificates premises
  exact ⟨w, batching, publications, controls, registered ended⟩

/-- Root-node accounting is now constructed on the full admission witness.
Witness: the shared certificate covers both root groups and streams without supplying
per-node registry, notice, publication, or cancellation hypotheses.
-/
example {work inputs} (premises : ReplayPremises work inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    : ∃ w : Witness,
        BatchShape work inputs w
        ∧ PublicationAdmission work w
        ∧ ControlAdmission work w
        ∧ ∀ node kind dependencies,
            NodeAt work node kind dependencies none
            → node.key ∈ completedKeys w.events
              ∨ node.key ∉ announcedKeys (initialKeys work) w.events
                ∧ (NodeFailed work w.matching w.events w.failures node.key
                    ∨ NodeAccounted work w.matching w.events w.failures node.key) := by
  obtain ⟨w, _, batching, _, _, publications, controls, _, _, roots, _⟩ :=
    mixed_rootTerminalCertificates premises
  exact ⟨w, batching, publications, controls, roots ended⟩

/-- Published item producers expose all their child nodes to terminal accounting.
Witness: the common admission certificate, with no supplied registration, child notice,
or source-success premise. The unchanged matching determines producer publication.
-/
example {work inputs} (premises : ReplayPremises work inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    : ∃ w : Witness,
        BatchShape work inputs w
        ∧ PublicationAdmission work w
        ∧ ControlAdmission work w
        ∧ ∀ node kind dependencies address index,
            NodeAt work node kind dependencies (some (.item address index))
            → Published w.matching w.events (.item address index)
            → node.key ∈ completedKeys w.events
              ∨ node.key ∉ announcedKeys (initialKeys work) w.events
                ∧ (NodeFailed work w.matching w.events w.failures node.key
                    ∨ NodeAccounted work w.matching w.events w.failures node.key) := by
  obtain ⟨w, _, batching, _, _, publications, controls, _, children⟩ :=
    mixed_itemTerminalCertificates premises
  exact ⟨w, batching, publications, controls, children ended⟩

/-- Root groups and all groups generated by published producers are accounted jointly.
Witness: the unchanged mixed admission certificate supplies concrete registration and
accepted storing boundaries; neither is imposed on the event source as an assumption.
-/
example {work inputs} (premises : ReplayPremises work inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    : ∃ w : Witness,
        BatchShape work inputs w
        ∧ PublicationAdmission work w
        ∧ ControlAdmission work w
        ∧ ∀ group dependencies producer,
            NodeAt work group .group dependencies producer
            → (∀ occurrence,
                producer = some occurrence → Published w.matching w.events occurrence)
            → NodeFailed work w.matching w.events w.failures group.key
              ∨ NodeAccounted work w.matching w.events w.failures group.key := by
  obtain ⟨w, _, batching, _, _, publications, controls, _, groups⟩ :=
    mixed_producedGroupTerminalCertificates premises
  exact ⟨w, batching, publications, controls, groups ended⟩

/-- Every published object's structural child streams complete on the shared witness.
Witness: complete concrete release and terminal tracking, with no assumed notice, flush,
or registration premise for the child stream.
-/
example {work inputs} (premises : ReplayPremises work inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    : ∃ w : Witness,
        BatchShape work inputs w
        ∧ PublicationAdmission work w
        ∧ ControlAdmission work w
        ∧ ∀ stream dependencies address,
            NodeAt work stream .stream dependencies (some (.executionGroup address))
            → Published w.matching w.events (.executionGroup address)
            → stream.key ∈ completedKeys w.events := by
  obtain ⟨w, history, batching, _, _, publications, controls, _, _, _, _, _, ledger, _⟩ :=
    mixed_admissionCertificates premises.generated premises.valid premises.started
  exact ⟨w, batching, publications, controls, fun _ _ _ known published =>
    terminal_objectProducedStream_completed premises.generated premises.valid premises.started
      history publications ledger ended known published⟩

/-- The exact target needs only the node clause as an independent terminal construction.
Witness: all other leaves retain their original shared witness and public premises.
-/
example {work inputs w} (premises : ReplayPremises work inputs)
    (batching : BatchShape work inputs w) (announced : AnnouncedFailures work w)
    (uncancelled : UncancelledFailures work w)
    (publications : PublicationAdmission work w) (controls : ControlAdmission work w)
    (nodes
      : ((initialQueue work).runNormalized inputs).1.terminated = true
        → NodeAccounting work w)
    : Obligations work inputs w :=
  obligations_of_nodeAccounting premises batching announced uncancelled publications
    controls nodes

/-- The announced-group branch of the terminal node leaf needs no admitted-output premise.
Witness: concrete protected-root accounting on the canonical history, with unchanged
generated-work and source assumptions.
-/
example {work inputs node dependencies producer} {w : Witness}
    (premises : ReplayPremises work inputs)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : NodeAt work node .group dependencies producer)
    (announced : node.key ∈ announcedKeys (initialKeys work) w.events)
    : node.key ∈ completedKeys w.events :=
  groupNode_terminalCompleted premises.generated premises.valid premises.started history
    ended known announced

/-- The remaining terminal construction may focus solely on unannounced nodes.
Witness: the checked reduction fills both original terminal fields with the same canonical
history, matching, and cuts, without changing the public target or source premises.
-/
example {work inputs w} (premises : ReplayPremises work inputs)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (batching : BatchShape work inputs w) (announced : AnnouncedFailures work w)
    (uncancelled : UncancelledFailures work w)
    (publications : PublicationAdmission work w) (controls : ControlAdmission work w)
    (latent
      : ((initialQueue work).runNormalized inputs).1.terminated = true
        → UnannouncedNodeAccounting work w)
    : Obligations work inputs w :=
  obligations_of_unannouncedNodeAccounting premises history batching announced uncancelled
    publications controls latent

/-- Retired-node accounting uses the already constructed witness, not another matching.
Witness: the joint publication/failure construction supplies every premise of the new
retirement bridge, including endpoint failure visibility. No output admission is assumed.
-/
theorem retired_groups_accounted_on_shared_witness {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ ∀ node dependencies producer,
            NodeAt work node .group dependencies producer
            → ((initialQueue work).replayGraphEvents inputs.flatten).RetiredGroup node.key
            → NodeFailed work w.matching w.events w.failures node.key
              ∨ NodeAccounted work w.matching w.events w.failures node.key := by
  obtain ⟨w, history, batching, announced, uncancelled, _, _, _, _, _, ledger, _,
    support, _, _, _, streams, _, exactCuts⟩ :=
    mixed_groupPublicationCertificates_with_noticeSafety generated valid started
  refine ⟨w, history, batching, announced, uncancelled, ?_⟩
  have partition := exactCuts ▸ mergeFailureCuts_partition _ streams
  have visible := objectFailureContributions_visible started announced.1 partition
  intro node dependencies producer known retired
  exact retiredGroup_failed_or_accounted generated valid started history ledger
    announced.1 support visible known retired

private def stream : Execution.DeliveryNode := { key := 0, path := [] }
private def work : Execution.Work := .stream stream []
private def emptyWitness : Witness := ⟨[], fun _ => .executionGroup [], []⟩

/-- Even an exhausted stream retains its root until its concrete completion input.
Witness: after that input, the generic termination theorem empties both root lists.
-/
example
    : let final :=
        ((State.initialize (Work.fromExecution work)).runNormalized
          [[.streamSuccess stream]]).1
      final.rootGroups = [] ∧ final.rootStreams = [] :=
  createWorkQueue_terminalRoots (Work.fromExecution work) [[.streamSuccess stream]]
    (by decide)

/-- A genuine unobserved empty stream satisfies all seven local obligations without
requiring it to be finished. Witness: empty batching, inventory, and event history;
terminal coverage is required only after the runtime flag becomes true.
-/
theorem initial_obligations : Obligations work [] emptyWitness := by
  constructor
  · exact WorkBatching.nil
  · simp [AnnouncedFailures, CompleteFailureInventory, emptyWitness]
  · intro before cut occurrence after impossible
    cases before <;> cases impossible
  · intro index event impossible
    cases impossible
  · intro index event impossible
    cases impossible
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible

/-- An exhausted stream's notice is not silently removed at termination.
Witness: the general raw-stream completion theorem after the concrete stream-success input.
-/
example
    : stream.key
      ∈ ((initialQueue work).rawEventReplay [.streamSuccess stream]).2.flatMap
          rawStreamClosureKeys :=
  createWorkQueue_terminalStreamCompleted (inputs := [[.streamSuccess stream]])
    (by decide) (by decide) (by decide)

/-- Batching cannot certify invented output, even if all its other fields are empty.
Witness: empty concrete output forces the entire proposed atomic history to be empty.
-/
theorem invented_termination_rejected
    : ¬BatchShape work [] { emptyWitness with events := [.workQueueTermination] } := by
  intro batching
  have empty := batching.nil_iff.mpr rfl
  contradiction

/-- The two-way bridge handles any independently chosen abstract-run witnesses; they
need not be the witnesses used to certify concrete replay.
-/
example {work inputs w}
    (initialized
      : Initializes work (initialQueue work).initialGroups
          (initialQueue work).initialStreams)
    (obligations : Obligations work inputs w)
    (run : AdmissibleRun work ((initialQueue work).normalizedHistory inputs))
    : ((initialQueue work).runNormalized inputs).1.terminated = true :=
  (run_iff_terminated
    (explains initialized obligations.announced obligations.uncancelled
      obligations.publications obligations.controls)
    obligations.batching
    (fun done => terminal (obligations.tasks done) (obligations.nodes done))).mp
    run

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerConformancePlan
