import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupCarrierOutputCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventAccounting

/-! Startup group task-accounting retains one actual publication matching and ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every object contributor is already published on the exact strict carrier prefix.
The actual seeded publisher's prefix count is interpreted by the same raw source ledger;
no alternate occurrence matching or publisher-state equality is introduced.
-/
theorem startup_groupSuccess_objectContributorsPublished
    {work inputs w index group groups streams address owners producer payload}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : group.ref ∈ owners)
    : Published w.matching (w.events.take index) (.executionGroup address) := by
  obtain ⟨published, batched, _, interpret, _⟩ := ledger
  obtain ⟨atFull, beforeEq⟩ := Witness.startup_event startup history selected
  obtain ⟨position, atRaw, count⟩ :=
    State.startup_runNormalized_groupSuccess_rawPrefix startup atFull
  obtain ⟨value, delivered⟩ :=
    generated.startup_rawBatches_groupContributor_covered startup matched valid started
      batched atRaw known contributes
  have within : index ≤ w.events.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1
  apply interpret index within (.executionGroup address)
  rw [← beforeEq, count, ← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), delivered, rfl⟩

/-- Every contributing structural task has published before the actual startup group
success. Generated group/stream roles exclude item tasks from that group's contributor set.
-/
theorem startup_groupSuccess_nodeAccounted
    {work inputs w index group groups streams}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : NodeAccounted work w.matching (w.events.take index) w.failures group.ref := by
  intro occurrence owners ⟨producer, payload, known⟩ contributes
  cases occurrence with
  | executionGroup address =>
      exact Or.inr (startup_groupSuccess_objectContributorsPublished generated startup matched valid
        started history
        ledger selected known contributes)
  | item address ordinal =>
      obtain ⟨atFull, _⟩ := Witness.startup_event startup history selected
      obtain ⟨dependencies, parent, groupKnown⟩ :=
        generated.startup_runNormalized_atomicGroupClosuresLocated startup valid _
          (List.mem_of_getElem? atFull)
      obtain ⟨stream, entries, enclosing, result, children, located, entry, sameOwners,
        samePayload⟩ := known
      rw [sameOwners] at contributes
      exact False.elim (generated.groupStreamRefsDisjoint groupKnown (.stream located)
        (List.mem_singleton.mp contributes))

/-- Actual startup replay retains successful group health and full contributor accounting
on the same witness as failure licensing, stream admission, publication provenance and
buffered closure coverage. Group/stream carried-notice eligibility, full value admission
and terminal task/node/report accounting remain separate.
-/
theorem startup_groupAccountingCertificates {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {inputs : List (List GraphEvent)}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∃ w : Witness,
        w.events = initial.nonterminalAtoms inputs
        ∧ WorkBatching
            (w.events
              ++ if (initial.runNormalized inputs).1.terminated then
                    [.workQueueTermination]
                  else
                    [])
            (initial.runNormalized inputs).2
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ FailureAdmission work w
        ∧ StreamSuccessAdmission work w
        ∧ StreamPublicationReady work w
        ∧ GroupSuccessesHealthy work w
        ∧ GroupSuccessesAccounted work w
        ∧ (∀ index event,
            w.events[index]? = some event
            → IsValue event
            → PublicationAt work (w.matching index) event
              ∧ ¬Published w.matching (w.events.take index) (w.matching index)
              ∧ ∀ address first second,
                  w.matching index = .item address second
                  → first < second
                  → Published w.matching (w.events.take index) (.item address first))
        ∧ BufferedClosureLedger work inputs w initial
        ∧ StreamNoticeProducers work w
        ∧ SuccessfulItemsSafe work inputs.flatten w
        ∧ StreamValuesReady work w
        ∧ StreamSuccessesAccounted work w
        ∧ (∃ streams,
            StreamFailureCuts work
              ((initial.runNormalized inputs).2.flatten.flatMap publicationAtoms) streams
            ∧ w.failures
              = mergeFailureCuts
                  (startup.informativeObjectFailureCuts work inputs) streams
            ∧ w.reported
              = mergeFailureCuts (startup.objectReportingCuts work inputs) streams) := by
  obtain ⟨w, history, shape, announced, uncancelled, failures, successes, streamReady, values,
    ledger, producers, safe, ready, accounted, streams, cuts, causalEq, reportingEq⟩ :=
    startup_eventCertificates generated startup matched valid started
  have healthy := startup_groupSuccessesHealthy_of_successfulItems generated startup matched
    valid started history announced safe cuts causalEq
  exact ⟨w, history, shape, announced, uncancelled, failures, successes, streamReady, healthy,
    (fun _ _ _ _ selected => startup_groupSuccess_nodeAccounted generated startup matched
      valid started history ledger selected),
    values, ledger, producers, safe, ready, accounted, streams, cuts, causalEq, reportingEq⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
