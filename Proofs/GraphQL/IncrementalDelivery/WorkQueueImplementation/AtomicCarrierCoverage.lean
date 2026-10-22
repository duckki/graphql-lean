import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchedCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedOutputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventHealth

/-! Structural successful-group coverage on the shared normalized atomic witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Batching and owner normalization preserve each successful carrier's strict count
-----------------------------------------------------------------------------------------

/-- An actual atomic success retains its raw batched position and strict object count.
Publisher normalization and atomic expansion preserve the preceding object sequence;
the underlying queue retains every original host-batch cache boundary. -/
theorem createWorkQueue_runNormalized_groupSuccess_rawPrefix
    {work : Execution.Work} {inputs index group groups streams}
    (_started : inputsStarted work inputs = true)
    (selected
      : (((State.initialize (Work.fromExecution work)).runNormalized
            inputs).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupSuccess group groups streams))
    : ∃ position,
        ((State.initialize (Work.fromExecution work)).rawBatches inputs).2[position]?
          = some (.groupSuccess group groups streams)
        ∧ (((((State.initialize (Work.fromExecution work)).runNormalized
                inputs).2.flatten.flatMap
              publicationAtoms).take
              index).flatMap
            normalizedObjectValues).length
          = ((((State.initialize (Work.fromExecution work)).rawBatches inputs).2.take
                position).flatMap
              WorkQueueEvent.objectValues).length := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  rw [createWorkQueue_runNormalized_rawBatches] at selected ⊢
  obtain ⟨normalizedIndex, normalizedEvent, atomCount⟩ :=
    publicationAtoms_groupSuccess_prefix _ selected
  obtain ⟨position, rawEvent, rawCount⟩ :=
    publisher.normalizeBatch_groupSuccess (queue.rawBatches inputs).2 normalizedEvent
  exact ⟨position, rawEvent, atomCount.trans rawCount⟩

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Interpret the original ledger instead of selecting a fresh publication matching
-----------------------------------------------------------------------------------------

/-- Every object contributor has published before its successful group on the same witness.
Witness: retain the original batch ledger, derive structural raw-carrier coverage, and
use its exact atomic object-prefix interpretation. This includes roots, object-produced
tasks, and item-produced tasks without assuming their registration or prior publication.
-/
theorem groupSuccess_objectContributorsPublished
    {work inputs w index group groups streams address owners producer payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : group.ref ∈ owners)
    : Published w.matching (w.events.take index) (.executionGroup address) := by
  obtain ⟨published, batched, _, interpret, _⟩ := ledger
  obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
  obtain ⟨position, atRaw, count⟩ :=
    createWorkQueue_runNormalized_groupSuccess_rawPrefix started atFull
  obtain ⟨value, delivered⟩ :=
    generated.rawBatches_groupContributor_covered valid started batched atRaw known contributes
  have within : index ≤ w.events.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1
  apply interpret index within (.executionGroup address)
  rw [← beforeEq, count, ← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), delivered, rfl⟩

/-- Every structural task of a successfully closing group is accounted for before closure.
Witness: all object contributors are published under the retained matching. A stream item
cannot contribute to the group because generated group and stream refs are disjoint.
No cancellation alternative is needed at a healthy successful carrier.
-/
theorem groupSuccess_nodeAccounted
    {work inputs w index group groups streams}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : NodeAccounted work w.matching (w.events.take index) w.failures group.ref := by
  intro occurrence owners ⟨producer, payload, known⟩ contributes
  cases occurrence with
  | executionGroup address =>
      exact Or.inr (groupSuccess_objectContributorsPublished generated valid started history
        ledger selected known contributes)
  | item address ordinal =>
      obtain ⟨atFull, _⟩ := Witness.canonical_event history selected
      obtain ⟨dependencies, parent, groupKnown⟩ :=
        createWorkQueue_runNormalized_atomicGroupClosuresLocated generated valid _
          (List.mem_of_getElem? atFull)
      obtain ⟨stream, entries, enclosing, result, children, located, entry, sameOwners,
        samePayload⟩ := known
      rw [sameOwners] at contributes
      exact False.elim (generated.groupStreamRefsDisjoint groupKnown (.stream located)
        (List.mem_singleton.mp contributes))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
