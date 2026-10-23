import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredGroupAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SupportedOwnerHealth

/-! Concrete final failure contributions are visible on the shared canonical witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Accepted failures remain visible even when their handlers emit no output
-----------------------------------------------------------------------------------------

/-- Every concrete object invalidation is preserved at the canonical witness's final cutoff.
Witness: exact source-label replay identifies the contribution ledger with the raw object cuts;
selection preserves invalidation, and the complete inventory bounds every retained cut
by the nonterminal history.
No event-admission or terminal-accounting premise is used.
-/
theorem objectFailureContributions_visible {work inputs} {w : Witness}
    (started : inputsStarted work inputs = true)
    (inventory : CausalFailureInventory work w.events w.failures)
    {streams : FailureCuts}
    (partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures.Perm
          (streams
            ++ informativeObjectFailureCuts work
                (queue.sourceRunBlocks publisher inputs).2.2))
    : ∀ ref,
        GroupInvalidated work
          ((initialQueue work).admittedObjectFailureContributionsForBatches inputs) ref
        → GroupInvalidated work (failedBefore w.failures w.events.length) ref := by
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let raw := availableObjectFailureCuts work 0
    (queue.sourceRunBlocks publisher inputs).2.2
  have ledger := sourceObjectFailureCuts_occurrences 0
    (queue.sourceRunBlocks publisher inputs).2.2
  rw [queue.sourceRunBlocks_inputs_of_started publisher
    (by rwa [← inputsStarted_eq_batchesStarted])] at ledger
  intro ref invalid
  have rawInvalid : GroupInvalidated work (raw.map Prod.snd) ref := by
    apply invalid.mono
    intro occurrence member
    rw [State.admittedObjectFailureContributionsForBatches_eq_of_started _ inputs
      (by rwa [← inputsStarted_eq_batchesStarted]),
      GraphEvent.failureSettlements_eq_objectFailures_reverse, List.mem_reverse, ← ledger] at member
    obtain ⟨entry, source, same⟩ := List.mem_map.mp member
    have candidate : entry ∈ objectFailureCandidates work 0
        (queue.sourceRunBlocks publisher inputs).2.2 :=
      (objectFailureCandidates_partition _ _ _).mem_iff.mpr (List.mem_append_right _ source)
    obtain ⟨kept, retained, identity, _⟩ := firstReportingCuts_earlier (seen := [])
      (objectFailureCandidates_ordered _ _ _) candidate (by simp)
    exact List.mem_map.mpr ⟨kept, retained, identity.trans same⟩
  have selected : GroupInvalidated work
      ((selectObjectFailureCuts work [] raw).map Prod.snd) ref := by
    exact (selectObjectFailureCuts_groupInvalidated work [] raw ref).mp rawInvalid
  apply selected.mono
  intro occurrence recorded
  obtain ⟨entry, retained, same⟩ := List.mem_map.mp recorded
  have member : entry ∈ w.failures :=
    partition.mem_iff.mpr (List.mem_append_right _ retained)
  exact same ▸ mem_failedBefore member (inventory.2.2.1 entry member).1

/-- Concrete invalidation of a structural group has a cause under the same matching/cuts.
Witness: generated group metadata converts record invalidation to causal invalidation;
publication support then transports the full accepted-failure inventory historically.
-/
theorem groupRecordInvalidated_nodeFailed
    {work group dependencies producer} {inputs : List (List GraphEvent)} {w : Witness}
    (generated : ExecutedWork work)
    (inventory : CausalFailureInventory work w.events w.failures)
    (support : PublicationSupport work w.matching w.events w.failures)
    (visible
      : ∀ ref,
          GroupInvalidated work
            ((initialQueue work).admittedObjectFailureContributionsForBatches inputs) ref
          → GroupInvalidated work (failedBefore w.failures w.events.length) ref)
    (known : NodeAt work group .group dependencies producer)
    (invalid
      : GroupRecordInvalidated work
          ((initialQueue work).admittedObjectFailureContributionsForBatches inputs)
          group.ref)
    : NodeFailed work w.matching w.events w.failures group.ref := by
  have cause := (generated.groupRecordInvalidated_iff_groupInvalidated known).mp invalid
  apply (visible _ cause).toNodeFailed_of_support support ?_ (List.Subset.refl _)
  intro cut occurrence member
  exact (inventory.2.2.1 (cut, occurrence) member).2.2

/-- Every retired structural group is failed or accounted on the existing shared witness.
Witness: concrete invalidation has a historical failure cause; otherwise structural
retirement publishes every contributor. This includes silent, unannounced retirement.
Retirement itself remains a separate concrete-state obligation for latent terminal nodes.
-/
theorem retiredGroup_failed_or_accounted
    {work inputs group dependencies producer} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (inventory : CausalFailureInventory work w.events w.failures)
    (support : PublicationSupport work w.matching w.events w.failures)
    (visible
      : ∀ ref,
          GroupInvalidated work
            ((initialQueue work).admittedObjectFailureContributionsForBatches inputs) ref
          → GroupInvalidated work (failedBefore w.failures w.events.length) ref)
    (known : NodeAt work group .group dependencies producer)
    (retired : ((initialQueue work).runNormalized inputs).1.RetiredGroup group.ref)
    : NodeFailed work w.matching w.events w.failures group.ref
      ∨ NodeAccounted work w.matching w.events w.failures group.ref := by
  classical
  by_cases invalid : GroupRecordInvalidated work
      ((initialQueue work).admittedObjectFailureContributionsForBatches inputs) group.ref
  · exact .inl (groupRecordInvalidated_nodeFailed generated inventory support visible known
      invalid)
  · exact .inr (retiredGroup_nodeAccounted generated valid started history ledger known
      retired invalid)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
