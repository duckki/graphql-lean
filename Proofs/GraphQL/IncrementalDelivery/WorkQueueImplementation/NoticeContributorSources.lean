import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetainedNoticeProducers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventHealth

/-! Accepted notice failures retain their successful source-producer prerequisites. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every failed group-task settlement retains its original source occurrence identity.
Witness: discard reversal, then inspect the actual task-failure constructor.
-/
theorem GraphEvent.failureSettlements_subsetIdentities (received : List GraphEvent)
    : (GraphEvent.failureSettlements received).Subset
        (received.flatMap (fun event => event.identities.1)) := by
  intro occurrence member
  rw [GraphEvent.failureSettlements, List.mem_reverse] at member
  obtain ⟨event, supplied, failed⟩ := List.mem_flatMap.mp member
  refine List.mem_flatMap.mpr ⟨event, supplied, ?_⟩
  cases event <;> simp_all [GraphEvent.groupFailures, GraphEvent.identities]

namespace ConformancePlan

/-- A recorded object failure's producer succeeded in the actual received source.
Witness: the mixed-cut partition identifies an accepted queue failure, which is a real
input task settlement. Source validity then supplies the preceding successful producer.
Ignored failures are not added, and output notice admission is never assumed.
-/
theorem recordedObjectFailure_producerSucceeded
    {work inputs streams failures count address owners producer payload}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (cuts
      : StreamFailureCuts work
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streams)
    (partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        failures.Perm
          (streams
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher inputs).2.2)))
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (failed : Occurrence.executionGroup address ∈ failedBefore failures count)
    : ∀ source,
        producer = some source
        → source ∈ inputs.flatten.flatMap GraphEvent.successes := by
  intro source same
  subst producer
  obtain ⟨path, result, samePayload⟩ : ∃ path result, payload = .object path result := by
    obtain ⟨_, path, result, _, _, _, _, same⟩ := known
    exact ⟨path, result, same⟩
  have recorded := createWorkQueue_mixedFailureCuts_objectsRecorded started cuts partition
    (samePayload ▸ known) failed
  have received := ((initialQueue work).objectFailureContributions_sublist inputs.flatten).subset
    recorded
  exact valid.groupSettlement_producerBefore known
    (GraphEvent.failureSettlements_subsetIdentities inputs.flatten received)

/-- Actual cut-supported notice contents always supply a source-ready group contributor.
Witness: retained tasks carry registration prerequisites; error-only caches use the exact
mixed-cut/source bridge above. Both alternatives use the canonical input and failure list,
not an independently selected failure inventory or an added host assumption.
-/
theorem retainedNotice_sourceReadyContributor
    {work inputs events count child streams} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (cuts
      : StreamFailureCuts work
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streams)
    (partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures.Perm
          (streams
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher inputs).2.2)))
    (contents
      : RetainedNoticeContents work w.matching events
          (failedBefore w.failures count) inputs.flatten child)
    : ∃ address owners producer payload,
        TaskAt work (.executionGroup address) owners producer payload
        ∧ child.ref ∈ owners
        ∧ ∀ source,
            producer = some source
            → source ∈ inputs.flatten.flatMap GraphEvent.successes := by
  exact contents.sourceReadyContributor generated (fun _ _ _ _ known failed =>
    recordedObjectFailure_producerSucceeded valid started cuts partition known failed)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
