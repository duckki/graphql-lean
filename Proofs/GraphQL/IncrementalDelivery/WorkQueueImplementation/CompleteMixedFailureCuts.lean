import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MixedFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureProvenance

/-! Selected positive group causes under the common object/stream candidate inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Selected group causes persist under additional stream cuts
-----------------------------------------------------------------------------------------

/-- Prepending known tasks that do not own the ref preserves its selected error cause.
Witness: the same positive contributing task remains in the larger inventory.
No freshness or disjointness premise is needed for this inclusion.
-/
theorem nodeErrors_prepend_nonowners {work failed ref errors}
    (counts : NodeFailureCause work failed ref errors) (more : List Occurrence)
    (_known
      : ∀ occurrence ∈ more,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload ∧ ref ∉ owners)
    : NodeFailureCause work (more ++ failed) ref errors :=
  counts.mono (List.subset_append_right more failed)

/-- Adding visible stream failures preserves the exact total for a generated group.
Witness: each failed item's sole stream owner is disjoint from the group's ref.
This concerns summation only, not licensing the added failure cuts.
-/
theorem nodeErrors_with_streams {work events streams objects index group errors}
    (counts : NodeFailureCause work objects group.ref errors)
    (cuts : StreamFailureCuts work events streams) (generated : ExecutedWork work)
    {dependencies producer} (groupKnown : NodeAt work group .group dependencies producer)
    : NodeFailureCause work (failedBefore streams index ++ objects) group.ref errors := by
  apply nodeErrors_prepend_nonowners counts
  intro occurrence member
  obtain ⟨entry, retained, same⟩ := List.mem_map.mp member
  obtain ⟨stream, count, parent, _, task⟩ := cuts.2 entry (List.mem_filter.mp retained).1
  rw [same] at task
  exact ⟨[stream.ref], parent, _, task,
    generated.itemFailure_not_groupOwner groupKnown task⟩

/-- Interleaving stream cuts preserves a group's selected visible object-failure cause.
Witness: partition at the unchanged unbatched output index, add only zero stream
contributions, and permute the summands back to the actual mixed inventory.
-/
theorem nodeErrors_group_mixed
    {work events streamCuts objectCuts failures index group errors}
    (counts : NodeFailureCause work (failedBefore objectCuts index) group.ref errors)
    (cuts : StreamFailureCuts work events streamCuts)
    (partition : failures.Perm (streamCuts ++ objectCuts))
    (generated : ExecutedWork work) {dependencies producer}
    (groupKnown : NodeAt work group .group dependencies producer)
    : NodeFailureCause work (failedBefore failures index) group.ref errors := by
  exact nodeErrors_of_perm (nodeErrors_with_streams counts cuts generated groupKnown)
    (failedBefore_partition partition index).symm

-----------------------------------------------------------------------------------------
-- Actual group closures count the same full mixed inventory as stream closures
-----------------------------------------------------------------------------------------

/-- Every actual group failure retains its complete count under interleaved stream cuts.
Witness: derive all visible object contributions from accepted replay, recover the
closing group's structural role, then insert the unrelated stream contributions.
Neither output admission nor completeness of a selected contributor subset is assumed.
-/
theorem createWorkQueue_mixedFailureCuts_groupNodeErrors {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {streamCuts failures : FailureCuts}
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) streamCuts)
    (partition
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        failures.Perm
          (streamCuts
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher batches).2.2)))
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : NodeFailureCause work (failedBefore failures index) group.ref errors := by
  obtain ⟨dependencies, producer, groupKnown⟩ :=
    createWorkQueue_runNormalized_atomicGroupClosuresLocated generated valid _
      (List.mem_of_getElem? atEvent)
  exact nodeErrors_group_mixed
    (createWorkQueue_sourceObjectFailureCuts_nodeErrors generated valid started atEvent)
    cuts partition generated groupKnown

/-- Every actual stream failure uses the same mixed inventory as the group-count theorem.
Witness: actual source object cuts have failed-object provenance; generated role separation
and ordered stream closures therefore leave this stream's count unchanged.
-/
theorem createWorkQueue_mixedFailureCuts_streamNodeErrors {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) {streamCuts failures : FailureCuts}
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) streamCuts)
    (partition
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        failures.Perm
          (streamCuts
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher batches).2.2)))
    {index : Nat} {stream : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.streamFailure stream errors))
    : NodeFailureCause work (failedBefore failures index) stream.ref errors := by
  apply cuts.nodeErrors_mixed partition ?_ generated
    (createWorkQueue_runNormalized_atomicStreamActions_ordered valid) atEvent
  intro entry member
  obtain ⟨_, owners, producer, path, count, task, _⟩ :=
    createWorkQueue_eligibleObjectFailureCuts_origin generated valid entry member
  exact ⟨owners, producer, path, count, task⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
