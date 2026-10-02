import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredContributorPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicHandlerBoundaries

/-! Healthy retired groups are accounted on the canonical publication matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Silent retirement has the same publication evidence as an observable closure
-----------------------------------------------------------------------------------------

/-- Every contributor of a healthy retired group has an actual canonical publication.
Witness: structural retirement supplies a value in the raw source ledger; exact payload
counts transport that entry through normalization and atomization to the shared matching.
No completion notice, output admission, or separately chosen publication witness is needed.
-/
theorem retiredGroup_contributorPublished
    {work inputs address owners producer payload key} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : key ∈ owners)
    (retired : ((initialQueue work).replayGraphEvents inputs.flatten).RetiredGroup key)
    (healthy
      : ¬GroupRecordInvalidated work
          ((initialQueue work).objectFailureContributions inputs.flatten) key)
    : Published w.matching w.events (.executionGroup address) := by
  obtain ⟨published, covered, _, interpret, _⟩ := ledger
  have accepted : (initialQueue work).batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  obtain ⟨value, delivered⟩ := generated.retired_structuralContributor_published valid
    ((initialQueue work).batchesStarted_acceptsBatch inputs accepted)
    (covered.flatten accepted) known contributes retired healthy
  have exactHistory := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  have count
      : (w.events.flatMap normalizedObjectValues).length
        = (((initialQueue work).rawEventReplay inputs.flatten).2.flatMap
            WorkQueueEvent.objectValues).length := by
    rw [exactHistory, IncrementalPublisher.normalizeBatch_atomicObjectValues]
  have atEnd := interpret w.events.length (Nat.le_refl _) (.executionGroup address)
  rw [List.take_length] at atEnd
  apply atEnd
  rw [count, ← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), delivered, rfl⟩

/-- A healthy retired structural group is fully accounted, even if it was never announced.
Witness: every object contributor is published under the canonical matching. Generated
group/stream key separation excludes item contributors, so no cancellation premise is used.
-/
theorem retiredGroup_nodeAccounted
    {work inputs group dependencies producer} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (known : NodeAt work group .group dependencies producer)
    (retired
      : ((initialQueue work).replayGraphEvents inputs.flatten).RetiredGroup group.key)
    (healthy
      : ¬GroupRecordInvalidated work
          ((initialQueue work).objectFailureContributions inputs.flatten) group.key)
    : NodeAccounted work w.matching w.events w.failures group.key := by
  intro occurrence owners ⟨taskProducer, payload, task⟩ contributes
  cases occurrence with
  | executionGroup address =>
      exact Or.inr (retiredGroup_contributorPublished generated valid started history ledger
        task contributes retired healthy)
  | item address ordinal =>
      obtain ⟨stream, entries, enclosing, result, children, located, entry, sameOwners,
        samePayload⟩ := task
      rw [sameOwners] at contributes
      exact False.elim (generated.groupStreamKeysDisjoint known (.stream located)
        (List.mem_singleton.mp contributes))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
