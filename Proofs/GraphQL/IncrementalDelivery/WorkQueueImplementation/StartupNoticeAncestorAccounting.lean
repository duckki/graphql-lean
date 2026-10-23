import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeAncestorCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupCarrierOutputCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeAncestorAccounting

/-! Startup group-notice ancestry is accounted on the original shared publication ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Normalization and atomic splitting retain the exact strict publication prefix
-----------------------------------------------------------------------------------------

/-- Every object contributor to a noticed defer ancestor is published on the same matching.
Witness: invert the canonical group carrier, preserve its raw object count, and interpret
the retained ledger's strict prefix. No notice admission or ancestor completion is assumed.
-/
theorem startup_groupNoticeAncestor_objectContributor_published
    {work inputs w index group groups streams child dependencies ref address owners
      producer payload}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : Published w.matching (w.events.take index) (.executionGroup address) := by
  obtain ⟨published, batched, _, interpret, _⟩ := ledger
  obtain ⟨atFull, beforeEq⟩ := Witness.startup_event startup history selected
  obtain ⟨position, atRaw, count⟩ :=
    State.startup_runNormalized_groupSuccess_rawPrefix startup atFull
  obtain ⟨value, delivered⟩ := generated.startup_rawBatches_groupNoticeAncestor_covered startup
    matched valid
    started batched atRaw noticed known ancestor task contributes
  apply interpret index (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    (.executionGroup address)
  rw [← beforeEq, count, ← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), delivered, rfl⟩

/-- A successful group notice accounts for every structural task of each defer ancestor.
Witness: all object contributors publish before the carrier; generated chain roles exclude
stream-item contributors. The arbitrary failure cuts are unused because no cancellation
alternative is needed. Health and announced/completed status remain separate obligations.
-/
theorem startup_groupNoticeAncestor_nodeAccounted
    {work inputs w index group groups streams child dependencies ref}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies) (failures : FailureCuts)
    : NodeAccounted work w.matching (w.events.take index) failures ref := by
  intro occurrence owners ⟨producer, payload, task⟩ contributes
  cases occurrence with
  | executionGroup address =>
      exact Or.inr (startup_groupNoticeAncestor_objectContributor_published generated startup
        matched valid started
        history ledger selected noticed known ancestor task contributes)
  | item address ordinal =>
      obtain ⟨stream, items, enclosing, result, children, located, _, sameOwners, _⟩ := task
      rw [sameOwners] at contributes
      exact False.elim (generated.groupRecord_ancestor_ne_stream known ancestor (.stream located)
        (List.mem_singleton.mp contributes))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
