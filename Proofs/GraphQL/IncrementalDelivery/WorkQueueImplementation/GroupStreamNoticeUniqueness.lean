import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamInventoryReplay

/-! A successful group flush releases each generated child stream at most once. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Distinct selected producers have disjoint stored child-stream lists
-----------------------------------------------------------------------------------------

/-- Equal stored stream refs identify the same task occurrence in generated work.
Witness: link provenance and uniqueness of the stream's structural producer.
-/
theorem State.ChildStreamsMatchWork.shared_ref_producer {queue : State}
    {work : Execution.Work} (matching : queue.ChildStreamsMatchWork work)
    (generated : ExecutedWork work) {first second : TaskNode}
    (firstStored : first ∈ queue.taskNodes) (secondStored : second ∈ queue.taskNodes)
    {ref : NodeRef} (firstLinked : ref ∈ first.childStreams)
    (secondLinked : ref ∈ second.childStreams)
    : first.task.occurrence = second.task.occurrence := by
  obtain ⟨stream, dependencies, known, same⟩ := matching first firstStored ref firstLinked
  have producer := matching.producer generated secondStored known (same ▸ secondLinked)
  exact Option.some.inj producer

/-- Occurrence-unique task selections have globally distinct child-stream refs.
Witness: per-task link uniqueness and generated-work producer separation across tasks.
-/
theorem State.ChildStreamInventory.selected_refs_nodup {queue : State}
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
      intro ref linked other included same
      obtain ⟨second, member, secondLinked⟩ := List.mem_flatMap.mp included
      have equal := matching.shared_ref_producer generated firstStored (restStored member)
        linked (same ▸ secondLinked)
      exact separated.1 (List.mem_map.mpr ⟨second, member, equal.symm⟩)

private theorem streamLookup_refs_sublist (queue : State) (refs : NodeRefs)
    : ((refs.filterMap (fun ref => (queue.stream? ref).map Stream.node)).map
        Execution.DeliveryNode.ref).Sublist
        refs := by
  induction refs with
  | nil => exact .refl []
  | cons ref rest ih =>
      cases found : queue.stream? ref with
      | none => simpa [found] using ih.cons ref
      | some stream =>
          have same : stream.node.ref = ref := beq_iff_eq.mp
            (List.find?_some (p := fun entry : Stream => entry.node.ref == ref) found)
          simpa [found, same] using ih.cons_cons ref

-----------------------------------------------------------------------------------------
-- Actual group flushes and initialized replay
-----------------------------------------------------------------------------------------

/-- A group flush's stream-notice refs are distinct, including shared-task membership.
Witness: the flush selects each task occurrence once; registered child lists are disjoint,
and descriptor lookup preserves a sublist of those unique refs.
-/
theorem State.ChildStreamInventory.finishGroupSuccess_streamRefs_nodup
    {queue : State} {work : Execution.Work} (inventory : queue.ChildStreamInventory)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    (group : GroupNode)
    : ((queue.finishGroupSuccess group).2.2.newStreams.map
        Execution.DeliveryNode.ref).Nodup := by
  obtain ⟨selected, unique, known, _, streams, _⟩ :=
    flushGroupTask_witness queue group.tasks [] []
  have refs := inventory.selected_refs_nodup matching generated selected unique
    (fun _ member => (known _ member).1)
  change (((group.tasks.foldl flushGroupTask (queue, [], [])).2.2.filterMap
    (fun ref => ((queue.finishGroupSuccess group).1.stream? ref).map Stream.node)).map
      Execution.DeliveryNode.ref).Nodup
  rw [streams]
  exact refs.sublist (streamLookup_refs_sublist _ _)

/-- Any local group flush after valid initialized replay has distinct stream notices.
Witness: executable replay supplies the link inventory and matching provenance; generated
work supplies producer uniqueness. No output-admission premise is assumed.
-/
theorem createWorkQueue_runNormalized_groupStreamRefs_nodup {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) (group : GroupNode)
    : ((((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.finishGroupSuccess
          group).2.2.newStreams.map
        Execution.DeliveryNode.ref).Nodup :=
  (createWorkQueue_runNormalized_childStreamInventory _
    _).finishGroupSuccess_streamRefs_nodup
    (createWorkQueue_runNormalized_childStreamsMatchWork valid) generated group

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
