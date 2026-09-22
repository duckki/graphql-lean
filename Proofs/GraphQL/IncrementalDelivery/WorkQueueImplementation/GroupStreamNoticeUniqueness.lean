import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamInventoryReplay

/-! A successful group flush releases each generated child stream at most once. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Distinct selected producers have disjoint stored child-stream lists
-----------------------------------------------------------------------------------------

/-- Equal stored stream keys identify the same task occurrence in generated work.
Witness: link provenance and uniqueness of the stream's structural producer.
-/
theorem State.ChildStreamsMatchWork.shared_key_producer {queue : State}
    {work : Execution.Work} (matching : queue.ChildStreamsMatchWork work)
    (generated : ExecutedWork work) {first second : TaskNode}
    (firstStored : first ∈ queue.taskNodes) (secondStored : second ∈ queue.taskNodes)
    {key : Nat} (firstLinked : key ∈ first.childStreams)
    (secondLinked : key ∈ second.childStreams)
    : first.task.occurrence = second.task.occurrence := by
  obtain ⟨stream, dependencies, known, same⟩ := matching first firstStored key firstLinked
  have producer := matching.producer generated secondStored known (same ▸ secondLinked)
  exact Option.some.inj producer

/-- Occurrence-unique task selections have globally distinct child-stream keys.
Witness: per-task link uniqueness and generated-work producer separation across tasks.
-/
theorem State.ChildStreamInventory.selected_keys_nodup {queue : State}
    {work : Execution.Work} (inventory : queue.ChildStreamInventory)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    (selected : List TaskNode)
    (unique : (selected.map (fun node => node.task.occurrence)).Nodup)
    (stored : selected.Subset queue.taskNodes)
    : (selected.flatMap TaskNode.childStreams).Nodup := by
  induction selected with
  | nil => simp
  | cons first rest ih =>
      have separated := List.nodup_cons.mp unique
      have firstStored := stored List.mem_cons_self
      have restStored : rest.Subset queue.taskNodes :=
        fun _ member => stored (List.mem_cons_of_mem _ member)
      apply List.nodup_append.mpr
      refine ⟨(inventory first firstStored).1, ih separated.2 restStored, ?_⟩
      intro key linked other included same
      obtain ⟨second, member, secondLinked⟩ := List.mem_flatMap.mp included
      have equal := matching.shared_key_producer generated firstStored (restStored member)
        linked (same ▸ secondLinked)
      exact separated.1 (List.mem_map.mpr ⟨second, member, equal.symm⟩)

private theorem streamLookup_keys_sublist (queue : State) (keys : Keys)
    : ((keys.filterMap (fun key => (queue.stream? key).map Stream.node)).map
        Execution.DeliveryNode.key).Sublist
        keys := by
  induction keys with
  | nil => exact .refl []
  | cons key rest ih =>
      cases found : queue.stream? key with
      | none => simpa [found] using ih.cons key
      | some stream =>
          have same : stream.node.key = key := beq_iff_eq.mp
            (List.find?_some (p := fun entry : Stream => entry.node.key == key) found)
          simpa [found, same] using ih.cons_cons key

-----------------------------------------------------------------------------------------
-- Actual group flushes and initialized replay
-----------------------------------------------------------------------------------------

/-- A group flush's stream-notice keys are distinct, including shared-task membership.
Witness: the flush selects each task occurrence once; registered child lists are disjoint,
and descriptor lookup preserves a sublist of those unique keys.
-/
theorem State.ChildStreamInventory.finishGroupSuccess_streamKeys_nodup
    {queue : State} {work : Execution.Work} (inventory : queue.ChildStreamInventory)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    (group : GroupNode)
    : ((queue.finishGroupSuccess group).2.2.newStreams.map
        Execution.DeliveryNode.key).Nodup := by
  obtain ⟨selected, unique, known, _, streams, _⟩ :=
    flushGroupTask_witness queue group.tasks [] []
  have keys := inventory.selected_keys_nodup matching generated selected unique
    (fun _ member => (known _ member).1)
  change (((group.tasks.foldl flushGroupTask (queue, [], [])).2.2.filterMap
    (fun key => ((queue.finishGroupSuccess group).1.stream? key).map Stream.node)).map
      Execution.DeliveryNode.key).Nodup
  rw [streams]
  exact keys.sublist (streamLookup_keys_sublist _ _)

/-- Any local group flush after valid initialized replay has distinct stream notices.
Witness: executable replay supplies the link inventory and matching provenance; generated
work supplies producer uniqueness. No output-admission premise is assumed.
-/
theorem createWorkQueue_runNormalized_groupStreamKeys_nodup {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) (group : GroupNode)
    : ((((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.finishGroupSuccess
          group).2.2.newStreams.map
        Execution.DeliveryNode.key).Nodup :=
  (createWorkQueue_runNormalized_childStreamInventory _
    _).finishGroupSuccess_streamKeys_nodup
    (createWorkQueue_runNormalized_childStreamsMatchWork valid) generated group

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
