import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredGroupAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SupportedOwnerHealth

/-! Concrete final failure contributions are visible on the shared canonical witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Accepted failures remain visible even when their handlers emit no output
-----------------------------------------------------------------------------------------

/-- Every accepted object failure is retained at the canonical witness's final cutoff.
Witness: exact source-label replay identifies the contribution ledger with the object-cut
partition; the complete inventory bounds every retained cut by the nonterminal history.
No event-admission or terminal-accounting premise is used.
-/
theorem objectFailureContributions_visible {work inputs} {w : Witness}
    (started : inputsStarted work inputs = true)
    (inventory : CompleteFailureInventory work w.events w.failures)
    {streams : FailureCuts}
    (partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures.Perm
          (streams
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher inputs).2.2)))
    : ((initialQueue work).objectFailureContributions inputs.flatten).Subset
        (failedBefore w.failures w.events.length) := by
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  have ledger := queue.eligibleObjectFailureCuts_ledger 0
    (queue.sourceRunBlocks publisher inputs).2.2
  rw [queue.sourceRunBlocks_inputs_of_started publisher
    (by rwa [← inputsStarted_eq_batchesStarted])] at ledger
  intro occurrence recorded
  rw [← ledger, List.mem_reverse] at recorded
  obtain ⟨entry, retained, same⟩ := List.mem_map.mp recorded
  have member : entry ∈ w.failures :=
    partition.mem_iff.mpr (List.mem_append_right _ retained)
  have visible := mem_failedBefore member (inventory.2.2.1 entry member).1
  exact same ▸ visible

/-- Concrete invalidation of a structural group has a cause under the same matching/cuts.
Witness: generated group metadata converts record invalidation to causal invalidation;
publication support then transports the full accepted-failure inventory historically.
-/
theorem groupRecordInvalidated_nodeFailed
    {work group dependencies producer} {inputs : List (List GraphEvent)} {w : Witness}
    (generated : ExecutedWork work)
    (inventory : CompleteFailureInventory work w.events w.failures)
    (support : PublicationSupport work w.matching w.events w.failures)
    (visible
      : ((initialQueue work).objectFailureContributions inputs.flatten).Subset
          (failedBefore w.failures w.events.length))
    (known : NodeAt work group .group dependencies producer)
    (invalid
      : GroupRecordInvalidated work
          ((initialQueue work).objectFailureContributions inputs.flatten) group.key)
    : NodeFailed work w.matching w.events w.failures group.key := by
  have cause := (generated.groupRecordInvalidated_iff_groupInvalidated known).mp invalid
  apply cause.toNodeFailed_of_support support ?_ visible
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
    (inventory : CompleteFailureInventory work w.events w.failures)
    (support : PublicationSupport work w.matching w.events w.failures)
    (visible
      : ((initialQueue work).objectFailureContributions inputs.flatten).Subset
          (failedBefore w.failures w.events.length))
    (known : NodeAt work group .group dependencies producer)
    (retired
      : ((initialQueue work).replayGraphEvents inputs.flatten).RetiredGroup group.key)
    : NodeFailed work w.matching w.events w.failures group.key
      ∨ NodeAccounted work w.matching w.events w.failures group.key := by
  classical
  by_cases invalid : GroupRecordInvalidated work
      ((initialQueue work).objectFailureContributions inputs.flatten) group.key
  · exact .inl (groupRecordInvalidated_nodeFailed generated inventory support visible known
      invalid)
  · exact .inr (retiredGroup_nodeAccounted generated valid started history ledger known
      retired invalid)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
