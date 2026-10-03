import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNoticeContents

/-! Ancestor contributions precede the exact notice carrier within a recursive drain. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Count the common ledger at the emitting iteration, before any later cleanup
-----------------------------------------------------------------------------------------

/-- A buffered ancestor contribution precedes its child's exact drain notice carrier.
Witness: recover the real post-carrier iteration prefix. The noticed child's task-bearing
ancestors are already retired there, so same-prefix owner conservation excludes buffering.
The carrier adds no object value; its inclusive and strict object counts coincide.
`offset` retains prior owner-fold output on the same publication ledger when present.
-/
theorem State.drainReadyGroups_go_noticeAncestorValue_before
    {queue original : State} {work parents} {published : List ObjectPublication}
    {fuel offset : Nat}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    (closed : queue.UncancelledRetiredAncestors work)
    (prefixes
      : ∀ steps,
          steps ≤ fuel
          → original.StoredOwnersConserved
              (published.take
                (offset
                  + ((State.drainReadyGroups.go steps queue).2.flatMap
                      WorkQueueEvent.objectValues).length))
              (State.drainReadyGroups.go steps queue).1)
    {index group groups streams child dependencies ref occurrence node value}
    (selected
      : (State.drainReadyGroups.go fuel queue).2[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (found : original.taskNode? occurrence = some node) (stored : node.value = some value)
    (task
      : TaskHasOwners work occurrence (node.task.groups.map Execution.DeliveryNode.ref))
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ original.groupNodes.map (fun owner => owner.group.node.ref))
    (uncancelled : ref ∉ (State.drainReadyGroups.go fuel queue).1.cancelledGroups)
    : (occurrence, value)
      ∈ published.take
          (offset
            + (((State.drainReadyGroups.go fuel queue).2.take index).flatMap
                WorkQueueEvent.objectValues).length) := by
  obtain ⟨steps, bound, exactPrefix, _⟩ :=
    State.drainReadyGroups_go_noticeContents generated refs records support fuel selected
      noticed
  let boundary := State.drainReadyGroups.go (steps + 1) queue
  have atBoundary : boundary.2[index]? = some (.groupSuccess group groups streams) := by
    rw [← exactPrefix, List.getElem?_take_of_lt (Nat.lt_succ_self _)]
    exact selected
  have ancestry := State.drainReadyGroups_go_noticeAncestorsRetired generated records
    links canonical live tasks roots closed (steps + 1)
  have retired := ancestry child.ref
    (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? atBoundary,
      List.mem_map_of_mem (f := Execution.DeliveryNode.ref) noticed⟩)
    child dependencies known rfl ref ancestor occurrence _ task contributes
  have notCancelled : ref ∉ boundary.1.cancelledGroups := fun member => uncancelled
    (State.drainReadyGroups_go_prefix_cancelledSubset queue (by omega) member)
  have emitted := (prefixes (steps + 1) (by omega)
    occurrence node value found stored ref contributes present notCancelled).resolve_right
      (fun retained => retired.2 retained.2)
  have count : (boundary.2.flatMap WorkQueueEvent.objectValues).length
      = (((State.drainReadyGroups.go fuel queue).2.take index).flatMap
          WorkQueueEvent.objectValues).length := by
    rw [← exactPrefix, List.take_add_one, selected]
    simp [WorkQueueEvent.objectValues]
  change (occurrence, value) ∈ published.take
    (offset + (boundary.2.flatMap WorkQueueEvent.objectValues).length) at emitted
  rwa [count] at emitted

-----------------------------------------------------------------------------------------
-- Both notice-producing handlers supply the structural frame independently
-----------------------------------------------------------------------------------------

/-- Task-success drain notices publish prepared ancestor buffers before their carrier.
Witness: matching replay supplies metadata; the real owner fold supplies root/retirement
certificates and the common drain-prefix ledger, including its preceding object offset.
Storage and noncancellation are local obligations, not added source assumptions.
-/
theorem ExecutedWork.taskSuccess_drainNoticeAncestorValue_before
    {work before occurrence result incoming published}
    {index group groups streams child dependencies ref buffered node value}
    (generated : ExecutedWork work)
    (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task : TaskHasOwners work buffered (node.task.groups.map Execution.DeliveryNode.ref))
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (stored : node.value = some value)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let prepared :=
        ((queue.putTaskNode
            { incoming with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := released.1.startNewWork released.2.2
      queue.PreparedReleaseOwners (.taskSuccess occurrence result) published
      → queue.taskNode? occurrence = some incoming
      → queue.taskHasHealthyOwner incoming.task = true
      → prepared.taskNode? buffered = some node
      → ref ∈ prepared.groupNodes.map (fun owner => owner.group.node.ref)
      → active.drainReadyGroups.2[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ref ∉ active.drainReadyGroups.1.cancelledGroups
      → (buffered, value)
        ∈ published.take
            ((released.2.1 ++ active.drainReadyGroups.2.take index).flatMap
              WorkQueueEvent.objectValues).length := by
  intro queue prepared released active prefixes found healthy lookup present selected
    noticed uncancelled
  obtain ⟨parents, canonical, records, links, live, tasks, roots, closed⟩ :=
    generated.replayGraphEvents_preparedRetirement before matching matched incoming
  have folded := successGroupFold_uncancelledRetirement closed generated records links
    canonical live tasks roots incoming.task.groups
  have protectedRoots := successGroupFold_ancestorsRetired generated records links canonical
    live tasks roots incoming.task.groups
  have registered := State.startNewWork_registration folded.2.2.1 folded.2.2.2.1 released.2.2
  obtain ⟨refs, activeRecords, support⟩ :=
    generated.taskSuccess_drain_noticeMetadata matching matched incoming
  have conserved : ∀ steps, steps ≤ active.groupNodes.length →
      prepared.StoredOwnersConserved
        (published.take ((released.2.1.flatMap WorkQueueEvent.objectValues).length
          + ((State.drainReadyGroups.go steps active).2.flatMap
            WorkQueueEvent.objectValues).length))
        (State.drainReadyGroups.go steps active).1 := by
    simpa only [State.ReleaseDrainOwners, List.flatMap_append, List.length_append]
      using (prefixes incoming found healthy).drain
  have emitted := State.drainReadyGroups_go_noticeAncestorValue_before generated refs
    activeRecords support (folded.2.1.startNewWork _) canonical registered.1 registered.2
    (folded.2.2.2.2.1.startNewWork _ protectedRoots.2)
    (folded.2.2.2.2.2.startNewWork _) conserved selected noticed known ancestor lookup stored
    task contributes present uncancelled
  simpa only [List.flatMap_append, List.length_append, State.drainReadyGroups]
    using emitted

/-- Item-handler drain notices publish earlier ancestor buffers before their carrier.
Witness: all item integrations supply the prepared structural frame. The original queue's
same drain-prefix conservation ledger has zero object offset because the leading carrier
contains only stream items, not object publications.
-/
theorem ExecutedWork.streamItems_drainNoticeAncestorValue_before
    {work before stream items published}
    {index group groups streams child dependencies ref occurrence node value}
    (generated : ExecutedWork work)
    (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task
      : TaskHasOwners work occurrence (node.task.groups.map Execution.DeliveryNode.ref))
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (stored : node.value = some value)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let prepared := queue.preparedStreamItems items
      queue.StreamDrainOwners stream items published
      → queue.rootStreams.contains stream.ref = true
      → queue.taskNode? occurrence = some node
      → ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref)
      → prepared.drainReadyGroups.2[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ref ∉ prepared.drainReadyGroups.1.cancelledGroups
      → (occurrence, value)
        ∈ published.take
            ((prepared.drainReadyGroups.2.take index).flatMap
              WorkQueueEvent.objectValues).length := by
  intro queue prepared prefixes active found present selected noticed uncancelled
  obtain ⟨parents, canonical, records, links, live, tasks, roots, closed⟩ :=
    generated.replayGraphEvents_streamPreparedRetirement before matching matched
  obtain ⟨refs, _, support⟩ := generated.streamItems_prepared_noticeMetadata matching matched
  simpa only [Nat.zero_add, State.drainReadyGroups]
    using State.drainReadyGroups_go_noticeAncestorValue_before (offset := 0)
      generated refs records support links canonical live tasks roots closed
      (by simpa only [Nat.zero_add] using prefixes active)
      selected noticed known ancestor found stored task contributes present uncancelled

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
