import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedOutputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventHealth

/-! Structural successful-group coverage on the shared normalized atomic witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Batching and owner normalization preserve each successful carrier's strict count
-----------------------------------------------------------------------------------------

/-- An actual atomic success carrier retains its raw replay position and object count.
Witness: flatten started batches, exclude the optional terminal suffix, and invert atomic
expansion and publisher normalization. Neither step changes preceding object-value counts.
-/
theorem createWorkQueue_runNormalized_groupSuccess_rawPrefix
    {work : Execution.Work} {inputs index group groups streams}
    (started : inputsStarted work inputs = true)
    (selected
      : (((State.initialize (Work.fromExecution work)).runNormalized
            inputs).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupSuccess group groups streams))
    : ∃ position,
        ((State.initialize (Work.fromExecution work)).rawEventReplay
            inputs.flatten).2[position]?
          = some (.groupSuccess group groups streams)
        ∧ (((((State.initialize (Work.fromExecution work)).runNormalized
                inputs).2.flatten.flatMap
              publicationAtoms).take
              index).flatMap
            normalizedObjectValues).length
          = ((((State.initialize (Work.fromExecution work)).rawEventReplay
                inputs.flatten).2.take
                position).flatMap
              WorkQueueEvent.objectValues).length := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  let atoms := (publisher.normalizeBatch (queue.rawEventReplay inputs.flatten).2).2.flatMap
    publicationAtoms
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_flattened inputs started
  change (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms
    = atoms ++ (if terminal then [.workQueueTermination] else []) at same
  rw [same] at selected ⊢
  have inside : index < atoms.length := by
    by_cases inside : index < atoms.length
    · exact inside
    have later : atoms.length ≤ index := by omega
    rw [List.getElem?_append_right later] at selected
    have member := List.mem_of_getElem? selected
    cases terminal <;> simp at member
  have atAtoms := (List.getElem?_append_left inside).symm.trans selected
  obtain ⟨normalizedIndex, normalizedEvent, atomCount⟩ :=
    publicationAtoms_groupSuccess_prefix _ atAtoms
  obtain ⟨position, rawEvent, rawCount⟩ :=
    publisher.normalizeBatch_groupSuccess _ normalizedEvent
  refine ⟨position, rawEvent, ?_⟩
  rw [List.take_append_of_le_length (Nat.le_of_lt inside)]
  exact atomCount.trans rawCount

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Interpret the original ledger instead of selecting a fresh publication matching
-----------------------------------------------------------------------------------------

/-- Every object contributor has published before its successful group on the same witness.
Witness: flatten the retained batch ledger, derive structural raw-carrier coverage, and
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
    (contributes : group.key ∈ owners)
    : Published w.matching (w.events.take index) (.executionGroup address) := by
  obtain ⟨published, batched, _, interpret, _⟩ := ledger
  have accepted : (initialQueue work).batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  have covered := batched.flatten accepted
  obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
  obtain ⟨position, atRaw, count⟩ :=
    createWorkQueue_runNormalized_groupSuccess_rawPrefix started atFull
  obtain ⟨value, delivered⟩ :=
    generated.rawEventReplay_groupContributor_covered valid
      ((initialQueue work).batchesStarted_acceptsBatch inputs accepted) covered atRaw known
      contributes
  have within : index ≤ w.events.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1
  apply interpret index within (.executionGroup address)
  rw [← beforeEq, count, ← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), delivered, rfl⟩

/-- Every structural task of a successfully closing group is accounted for before closure.
Witness: all object contributors are published under the retained matching. A stream item
cannot contribute to the group because generated group and stream keys are disjoint.
No cancellation alternative is needed at a healthy successful carrier.
-/
theorem groupSuccess_nodeAccounted
    {work inputs w index group groups streams}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : NodeAccounted work w.matching (w.events.take index) w.failures group.key := by
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
      exact False.elim (generated.groupStreamKeysDisjoint groupKnown (.stream located)
        (List.mem_singleton.mp contributes))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
