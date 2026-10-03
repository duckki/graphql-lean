import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRootCoverage

/-! Item-produced stream notices and initial stream notices are all activated. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Item preparation activates each registered release before constructing its carrier
-----------------------------------------------------------------------------------------

/-- The actual item fold covers all earlier roots and its accumulated stream notices.
Witness: every child integration registers its releases; pruning preserves that registry,
and activation retains old roots while adding each registered child stream.
-/
theorem State.streamItemFold_streamRoots_cover (queue : State) (items : List StreamItem)
    : let prepared := items.foldl streamItemStep (queue, [], [], [])
      (queue.rootStreams ++ prepared.2.2.1.map Execution.DeliveryNode.ref).Subset
        prepared.1.rootStreams := by
  have loop (remaining : List StreamItem)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue)
      (prior : (queue.rootStreams ++ acc.2.2.1.map Execution.DeliveryNode.ref).Subset
        acc.1.rootStreams)
      : let final := remaining.foldl streamItemStep acc
        (queue.rootStreams ++ final.2.2.1.map Execution.DeliveryNode.ref).Subset
          final.1.rootStreams := by
    induction remaining generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih
        let integrated := acc.1.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        have registered : integrated.2.newStreams.Subset (pruned.1.streams.map Stream.node) := by
          rw [State.pruneEmptyGroups_streams]
          exact (acc.1.maybeIntegrateWork_streams_registered item.work).2
        have next := pruned.1.startNewWork_streamRoots_cover
          { integrated.2 with newGroups := pruned.2 } registered
        have roots : pruned.1.rootStreams = acc.1.rootStreams := by
          rw [State.pruneEmptyGroups_rootStreams, State.maybeIntegrateWork_rootStreams]
        rw [roots] at next
        intro ref member
        apply next
        change ref ∈ queue.rootStreams
          ++ (acc.2.2.1 ++ integrated.2.newStreams).map Execution.DeliveryNode.ref at member
        rw [List.map_append] at member
        rcases List.mem_append.mp member with old | noticed
        · exact List.mem_append_left _ (prior (List.mem_append_left _ old))
        · rcases List.mem_append.mp noticed with earlier | added
          · exact List.mem_append_left _ (prior (List.mem_append_right _ earlier))
          · exact List.mem_append_right _ added
  exact loop items (queue, [], [], []) (by intro ref member; simpa using member)

/-- An item handler activates every carried stream notice and retains all old roots.
Witness: the leading item carrier names the prepared streams exactly; its subsequent
group drain also covers every emitted notice and does not remove any stream root.
-/
theorem State.streamItems_streamRoots_cover (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : (queue.rootStreams
        ++ (queue.streamItems stream items).2.flatMap rawStreamNoticeRefs).Subset
        (queue.streamItems stream items).1.rootStreams := by
  rw [queue.streamItems_eq stream items]
  split
  · intro ref member; simpa using member
  · let prepared := items.foldl streamItemStep (queue, [], [], [])
    have first := queue.streamItemFold_streamRoots_cover items
    have later := State.drainReadyGroups_go_streamRoots_cover prepared.1.groupNodes.length
      prepared.1
    intro ref member
    apply later
    simp only [List.flatMap_cons, rawStreamNoticeRefs] at member
    rcases List.mem_append.mp member with old | noticed
    · exact List.mem_append_left _ (first (List.mem_append_left _ old))
    · rcases List.mem_append.mp noticed with early | late
      · exact List.mem_append_left _ (first (List.mem_append_right _ early))
      · exact List.mem_append_right _ late

-----------------------------------------------------------------------------------------
-- Initialization has no unactivated stream notice, including exhausted streams
-----------------------------------------------------------------------------------------

/-- Every initial stream notice is an active queue root after initialization.
Witness: initial integration registers its releases, pruning keeps the stream registry,
and startNewWork activates each registered descriptor. No nonempty-item assumption is used.
-/
theorem createWorkQueue_initialStreams_active (work : Work)
    : ((State.initialize work).initialStreams.map Execution.DeliveryNode.ref).Subset
        (State.initialize work).rootStreams := by
  let integrated := ({} : State).maybeIntegrateWork work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have registered : integrated.2.newStreams.Subset (pruned.1.streams.map Stream.node) := by
    rw [State.pruneEmptyGroups_streams]
    exact (({} : State).maybeIntegrateWork_streams_registered work).2
  have covered := pruned.1.startNewWork_streamRoots_cover
    { integrated.2 with newGroups := pruned.2 } registered
  intro ref member
  exact covered (List.mem_append_right _ member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
