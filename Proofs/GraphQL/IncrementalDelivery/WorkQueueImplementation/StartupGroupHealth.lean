import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupEventCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupSuccessfulRetirements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventHealth

/-! Successful startup group carriers remain healthy under the shared mixed failure cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An object cause in the mixed startup inventory is an initial observation or an
actual retained source failure. This does not identify reporting availability with causal
licensing, or insert initial observations into the consumed history.
-/
theorem InitialStartup.mixedFailureCuts_objectsRecorded {work : Execution.Work}
    (startup : InitialStartup) {inputs : List (List GraphEvent)}
    {streams failures : FailureCuts}
    (cuts
      : let initial := State.initialize (Work.fromExecution work) startup
        StreamFailureCuts work
          ((initial.runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streams)
    (partition
      : failures.Perm (streams ++ startup.informativeObjectFailureCuts work inputs))
    {count occurrence owners producer path result}
    (known : TaskAt work occurrence owners producer (.object path result))
    (recorded : occurrence ∈ failedBefore failures count)
    : occurrence
      ∈ startup.failures.map Prod.fst
        ++ GraphEvent.failureSettlements inputs.flatten := by
  exact startup.informativeObjectFailureCuts_source_subset work inputs count
    ((cuts.object_mem_iff partition known).mp recorded)

namespace ConformancePlan

/-- Successful actual startup groups stay healthy even after later failure settlements.
Permanent uncancelled retirement excludes the initial and consumed failure inventory;
fixed task provenance and successful-item safety translate historical cancellation into
that same record inventory. Every premise is derived from the actual startup replay.
-/
theorem startup_groupSuccessesHealthy_of_successfulItems {work inputs w streams}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (cuts
      : let initial := State.initialize (Work.fromExecution work) startup
        StreamFailureCuts work
          ((initial.runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streams)
    (exactCuts
      : w.failures
        = mergeFailureCuts (startup.informativeObjectFailureCuts work inputs) streams)
    : GroupSuccessesHealthy work w := by
  let initial := State.initialize (Work.fromExecution work) startup
  have partition : w.failures.Perm (streams ++ startup.informativeObjectFailureCuts work inputs) :=
    exactCuts ▸ mergeFailureCuts_partition _ _
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := generated.startup_runNormalized_frame canonical startup matched inputs valid started
  have retirementHealth := frame.retiredHealth_withInitialFailures generated canonical matched valid
  intro index group groups children selected
  obtain ⟨atFull, _⟩ := Witness.startup_event startup history selected
  obtain ⟨sourceIndex, atSource, _⟩ := publicationAtoms_groupSuccess_prefix _ atFull
  have carrier := List.mem_of_getElem? atSource
  obtain ⟨dependencies, producer, known⟩ :=
    generated.startup_runNormalized_groupClosuresLocated startup valid _ carrier
  obtain ⟨_, _, retired⟩ :=
    generated.startup_runNormalized_successfulGroupRetirements startup matched valid started carrier
  intro failure
  have exposed := frame.regions.registered_exposed retired.retired.1
  have invalid := generated.exposed_groupFailure_invalidated valid known exposed
    (fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2)
    safe failure
  have recorded := invalid.toRecordInvalidated.restrict_objectFailures generated
    (groupRecordAt_of_nodeAt known)
    (fun occurrence owners producer path result descriptor member =>
      startup.mixedFailureCuts_objectsRecorded cuts partition descriptor member)
  exact retirementHealth.1 group dependencies (groupRecordAt_of_nodeAt known)
    retired.retired retired.uncancelled recorded

/-- For a healthy startup group, successful closure admission has exactly the remaining
task-accounting and carried-announcement obligations at the original event-start cut.
-/
theorem startup_groupSuccessAllowed_iff_accounting_and_announcements
    {work inputs w index group groups streams}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (healthy : GroupSuccessesHealthy work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
        (.groupSuccess group groups streams)
      ↔ NodeAccounted work w.matching (w.events.take index) w.failures group.ref
        ∧ Announcements work (initialRefs work) w.matching
            (w.events.take index ++ [.groupSuccess group [] []])
            (w.failures.filter (fun entry => entry.1 ≤ index)) groups streams := by
  obtain ⟨atFull, beforeEq⟩ := Witness.startup_event startup history selected
  obtain ⟨dependencies, producer, known⟩ :=
    generated.startup_runNormalized_atomicGroupClosuresLocated startup valid _
      (List.mem_of_getElem? atFull)
  have opened := generated.startup_runNormalized_groupClosureOpenAt startup valid started atFull
    List.mem_cons_self
  dsimp only at opened
  simp only [State.initializeWithStartup_initialGroups,
    State.initializeWithStartup_initialStreams] at opened
  rw [beforeEq] at opened
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  simp only [EventAllowed, length]
  constructor
  · rintro ⟨_, _, _, accounted, announcements⟩
    exact ⟨(nodeAccounted_filter (Nat.le_of_eq length)).mp accounted, announcements⟩
  · rintro ⟨accounted, announcements⟩
    exact ⟨⟨dependencies, producer, known⟩, opened,
      (by rw [nodeFailed_filter (Nat.le_of_eq length)]; exact healthy.atPrefix selected index),
      (nodeAccounted_filter (Nat.le_of_eq length)).mpr accounted, announcements⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
