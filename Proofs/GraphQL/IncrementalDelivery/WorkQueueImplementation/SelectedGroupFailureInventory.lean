import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SelectedFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectFailureCuts

/-! Causal selection preserves group failure, while reporting retains aggregate causes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Causal selection preserves an actual failed group's visible invalidation.
Witness: an aggregate report has a contributing source task at its output boundary.
Selection preserves the invalidation closure; it need not retain every reporting cause
or reproduce the report's aggregate count. Licensing the selected cuts remains separate.
-/
theorem createWorkQueue_selectedObjectFailureCuts_groupInvalidated
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let candidates :=
        availableObjectFailureCuts work 0 (queue.sourceRunBlocks publisher batches).2.2
      GroupInvalidated work
        (failedBefore (selectObjectFailureCuts work [] candidates) index) group.ref := by
  obtain ⟨parts, nonempty, _, _, contributions⟩ :=
    createWorkQueue_availableObjectFailureCuts_contributions generated valid atEvent
  obtain ⟨⟨occurrence, count⟩, member⟩ := List.exists_mem_of_ne_nil parts nonempty
  obtain ⟨visible, owners, producer, path, known, owner⟩ :=
    contributions occurrence count member
  have raw : GroupInvalidated work _ group.ref :=
    .task ⟨producer, _, known⟩ owner visible
  exact (selectObjectFailureCuts_failedBefore_groupInvalidated work [] _ index group.ref
    (availableObjectFailureCuts_ordered _ _ _)).mp raw

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
