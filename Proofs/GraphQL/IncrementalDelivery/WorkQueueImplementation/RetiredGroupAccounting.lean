import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulOwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicHandlerBoundaries

/-! Healthy retired groups are accounted on the canonical publication matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Silent retirement has the same publication evidence as an observable closure
-----------------------------------------------------------------------------------------

/-- Every contributor of a healthy retired group has an actual canonical publication.
Witness: structural retirement supplies a value in the actual batch ledger; exact payload
counts transport that entry through normalization and atomization to the shared matching.
No completion notice, output admission, or separately chosen publication witness is needed.
-/
theorem retiredGroup_contributorPublished
    {work inputs address owners producer payload ref} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    (retired : ((initialQueue work).runNormalized inputs).1.RetiredGroup ref)
    (healthy
      : ¬GroupRecordInvalidated work
          ((initialQueue work).admittedObjectFailureContributionsForBatches inputs) ref)
    : Published w.matching w.events (.executionGroup address) := by
  obtain ⟨published, covered, _, interpret, _⟩ := ledger
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := (initial_ownerPublicationFrame generated canonical).rawBatches generated
    canonical inputs valid (by rwa [← inputsStarted_eq_batchesStarted]) covered
  rw [State.rawBatches_state, ← State.runNormalized_replayBatches] at frame
  simp only [List.nil_append] at frame
  have healthySource := healthy
  rw [State.admittedObjectFailureContributionsForBatches_eq_of_started _ inputs
    (by rwa [← inputsStarted_eq_batchesStarted])] at healthySource
  have uncancelled := (generated.runNormalized_cancelledRecordsSupported inputs valid started)
    |>.healthy_not_mem healthySource
  obtain ⟨value, delivered⟩ := frame.retired_structuralContributor_published generated valid
    known contributes retired uncancelled
  have count
      : (w.events.flatMap normalizedObjectValues).length
        = (((initialQueue work).rawBatches inputs).2.flatMap
            WorkQueueEvent.objectValues).length := by
    have exactValues := IncrementalPublisher.normalizeBatch_atomicObjectValues
      ({ active := (initialQueue work).initialGroups ++ (initialQueue work).initialStreams }
        : IncrementalPublisher) ((initialQueue work).rawBatches inputs).2
    rw [Witness.rawBatches_shape history, List.flatMap_append] at exactValues
    split at exactValues <;>
      simpa only [List.flatMap_singleton, List.flatMap_nil, normalizedObjectValues,
        List.append_nil] using congrArg List.length exactValues
  have atEnd := interpret w.events.length (Nat.le_refl _) (.executionGroup address)
  rw [List.take_length] at atEnd
  apply atEnd
  rw [count, ← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), delivered, rfl⟩

/-- A healthy retired structural group is fully accounted, even if it was never announced.
Witness: every object contributor is published under the canonical matching. Generated
group/stream ref separation excludes item contributors, so no cancellation premise is used.
-/
theorem retiredGroup_nodeAccounted
    {work inputs group dependencies producer} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (known : NodeAt work group .group dependencies producer)
    (retired : ((initialQueue work).runNormalized inputs).1.RetiredGroup group.ref)
    (healthy
      : ¬GroupRecordInvalidated work
          ((initialQueue work).admittedObjectFailureContributionsForBatches inputs)
          group.ref)
    : NodeAccounted work w.matching w.events w.failures group.ref := by
  intro occurrence owners ⟨taskProducer, payload, task⟩ contributes
  cases occurrence with
  | executionGroup address =>
      exact Or.inr (retiredGroup_contributorPublished generated valid started history ledger
        task contributes retired healthy)
  | item address ordinal =>
      obtain ⟨stream, entries, enclosing, result, children, located, entry, sameOwners,
        samePayload⟩ := task
      rw [sameOwners] at contributes
      exact False.elim (generated.groupStreamRefsDisjoint known (.stream located)
        (List.mem_singleton.mp contributes))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
