import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamClosureOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamProducerReadiness

/-! Every actual generated-work stream reference uses an announced, uncompleted key. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An actual stream-reference key has a structural stream descriptor in the original work.
Witness: its strictly prior notice is either initially registered or emitted by a carrier;
both notice sources already have structural metadata. No caller descriptor is required.
-/
theorem createWorkQueue_runNormalized_streamReference_keyLocated {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index : Nat} {event key}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (reference : key ∈ streamReferenceKeys event)
    : ∃ stream dependencies producer,
        stream.key = key ∧ NodeAt work stream .stream dependencies producer := by
  have noticed := (createWorkQueue_runNormalized_atomicStreamReferences valid).atEvent
    atEvent reference
  rcases List.mem_append.mp noticed with initial | earlier
  · obtain ⟨stream, member, same⟩ := List.mem_map.mp initial
    exact ⟨stream, [], none, same, (createWorkQueue_initialStreams_nodeAt work).2 stream member⟩
  · obtain ⟨carrier, member, streamKey⟩ := List.mem_flatMap.mp earlier
    have metadata := createWorkQueue_runNormalized_atomicStreamNoticesLocated valid carrier
      (List.mem_of_mem_take member)
    obtain ⟨stream, same, dependencies, producer, known⟩ := metadata.of_key streamKey
    exact ⟨stream, dependencies, producer, same, known⟩

-----------------------------------------------------------------------------------------
-- Stream closure ordering and generated role separation discharge the full Open clause
-----------------------------------------------------------------------------------------

/-- Every actual atomic stream value or closure refers to an open notice.
Witness: earlier notices establish announcement; valid source order excludes earlier
stream closures, and structural group-closure provenance plus generated key roles excludes
same-key group closures. No matching, failure witness, or start check is assumed here.
Notice freshness, node health, and the remaining EventAllowed clauses are separate.
-/
theorem createWorkQueue_runNormalized_streamOpenAt {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) {index : Nat} {event key}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (reference : key ∈ streamReferenceKeys event)
    : let queue := State.initialize (Work.fromExecution work)
      Open ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.key)
        (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take index)
        key := by
  refine ⟨createWorkQueue_runNormalized_streamAnnouncedAt valid atEvent reference, ?_⟩
  obtain ⟨stream, streamDependencies, streamProducer, sameKey, streamKnown⟩ :=
    createWorkQueue_runNormalized_streamReference_keyLocated valid atEvent reference
  have unclosed := createWorkQueue_runNormalized_streamUnclosedAt valid atEvent reference
  intro completed
  obtain ⟨prior, member, closed⟩ := List.mem_flatMap.mp completed
  have known := createWorkQueue_runNormalized_atomicGroupClosuresLocated generated valid prior
    (List.mem_of_mem_take member)
  cases prior with
  | groupSuccess group groups streams | groupFailure group _ =>
      obtain ⟨dependencies, producer, located⟩ := known
      have same := List.mem_singleton.mp closed
      exact generated.groupStreamKeysDisjoint located streamKnown (same.symm.trans sameKey.symm)
  | streamSuccess closedStream | streamFailure closedStream _ =>
      apply unclosed
      have same := List.mem_singleton.mp closed
      exact List.mem_filterMap.mpr ⟨_, member, by simp [streamAction, same]⟩
  | groupValues | streamValues | workQueueTermination => cases closed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
