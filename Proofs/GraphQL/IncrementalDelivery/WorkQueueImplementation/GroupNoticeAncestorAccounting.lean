import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeAncestorPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicCarrierCoverage

/-! Carried group notices account for their full defer ancestry on the canonical witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Taskless ancestor records still have defer roles, never stream roles
-----------------------------------------------------------------------------------------

/-- A recorded defer ancestor cannot be a stream key, even without its own contributing task.
Witness: execution assigns false to every descriptor in a defer chain and true to stream
nodes. The registration suffix retains the ancestor's original role certificate.
-/
theorem ExecutedWork.groupRecord_ancestor_ne_stream
    {work child dependencies key stream enclosing producer}
    (generated : ExecutedWork work) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    (streamKnown : NodeAt work stream .stream enclosing producer)
    : key ≠ stream.key := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source, selections,
    equal⟩ := generated
  obtain ⟨roles, rootRoles⟩ := Semantics.KeyRoles.executeRoot_roles schema resolvers variables
    fuel parentType source selections 0
  rw [equal] at rootRoles
  obtain ⟨address, groups, path, result, children, birth, owners, fragment, ancestors,
    located, member, suffix, dependenciesEq⟩ := known
  have localRoles := generatedWorkRoles_located rootRoles
    (StructuralEquivalence.located_of_current located)
  simp only [Semantics.KeyRoles.WorkRoles] at localRoles
  have fragmentRoles := localRoles.1 fragment member
  rw [dependenciesEq] at ancestor
  obtain ⟨node, included, same⟩ := List.mem_map.mp ancestor
  have chain := suffix.subset (List.mem_cons_of_mem child included)
  have groupRole : roles key = false := by
    rcases List.mem_cons.mp chain with head | tail
    · exact same ▸ head.symm ▸ fragmentRoles.1
    · exact same ▸ fragmentRoles.2 node tail
  obtain ⟨streamAddress, items, streamLocated⟩ := streamKnown
  have streamRoles := generatedWorkRoles_located rootRoles
    (StructuralEquivalence.located_of_current streamLocated)
  simp only [Semantics.KeyRoles.WorkRoles] at streamRoles
  intro sameKey
  rw [sameKey] at groupRole
  exact Bool.false_ne_true (groupRole.symm.trans streamRoles.1)

-----------------------------------------------------------------------------------------
-- Recover the actual source handler without changing the publication labels
-----------------------------------------------------------------------------------------

/-- Raw replay publishes every object contributor of a group's noticed ancestor first.
Witness: locate the exact source handler and restrict the original ledger to its source
prefix. The checked handler theorem retains its strict object count through that split.
-/
theorem ExecutedWork.rawEventReplay_groupNoticeAncestor_covered
    {work events published index group groups streams child dependencies key address
      owners producer payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered events
          published)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawEventReplay events).2[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : key ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawEventReplay events).2.take
                index).flatMap
              WorkQueueEvent.objectValues).length := by
  obtain ⟨before, event, after, position, same, carrier, count⟩ :=
    (State.initialize (Work.fromExecution work)).rawEventReplay_output_at events selected
  have prior : (before ++ [event]).IsPrefix events :=
    ⟨after, by simp [same, List.append_assoc]⟩
  have accepted : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
      = true := by
    apply State.acceptsBatch_prefix (after := after)
    simpa only [same, List.append_assoc, List.singleton_append] using started
  have ledger : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
      (before ++ [event]) published := by
    apply State.ReplayClosuresCovered.prefix (after := after)
    simpa only [same, List.append_assoc, List.singleton_append] using covered
  rw [count]
  exact generated.handleGraphEvent_groupNoticeAncestor_contributor_before
    (valid.prefix prior) accepted ledger carrier noticed known ancestor task contributes

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Normalization and atomic splitting retain the exact strict publication prefix
-----------------------------------------------------------------------------------------

/-- Every object contributor to a noticed defer ancestor is published on the same matching.
Witness: invert the canonical group carrier, preserve its raw object count, and interpret
the retained ledger's strict prefix. No notice admission or ancestor completion is assumed.
-/
theorem groupNoticeAncestor_objectContributor_published
    {work inputs w index group groups streams child dependencies key address owners
      producer payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : key ∈ owners)
    : Published w.matching (w.events.take index) (.executionGroup address) := by
  obtain ⟨published, batched, _, interpret, _⟩ := ledger
  have accepted : (initialQueue work).batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  have covered := batched.flatten accepted
  obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
  obtain ⟨position, atRaw, count⟩ :=
    createWorkQueue_runNormalized_groupSuccess_rawPrefix started atFull
  obtain ⟨value, delivered⟩ := generated.rawEventReplay_groupNoticeAncestor_covered valid
    ((initialQueue work).batchesStarted_acceptsBatch inputs accepted) covered atRaw
      noticed known ancestor task contributes
  apply interpret index (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    (.executionGroup address)
  rw [← beforeEq, count, ← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), delivered, rfl⟩

/-- A successful group notice accounts for every structural task of each defer ancestor.
Witness: all object contributors publish before the carrier; generated chain roles exclude
stream-item contributors. The arbitrary failure cuts are unused because no cancellation
alternative is needed. Health and announced/completed status remain separate obligations.
-/
theorem groupNoticeAncestor_nodeAccounted
    {work inputs w index group groups streams child dependencies key}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies) (failures : FailureCuts)
    : NodeAccounted work w.matching (w.events.take index) failures key := by
  intro occurrence owners ⟨producer, payload, task⟩ contributes
  cases occurrence with
  | executionGroup address =>
      exact Or.inr (groupNoticeAncestor_objectContributor_published generated valid started
        history ledger selected noticed known ancestor task contributes)
  | item address ordinal =>
      obtain ⟨stream, items, enclosing, result, children, located, _, sameOwners, _⟩ := task
      rw [sameOwners] at contributes
      exact False.elim (generated.groupRecord_ancestor_ne_stream known ancestor (.stream located)
        (List.mem_singleton.mp contributes))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
