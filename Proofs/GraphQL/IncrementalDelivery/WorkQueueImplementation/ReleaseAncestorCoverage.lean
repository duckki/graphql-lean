import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAncestorCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReleasePublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementReplay

/-! Strict ancestor publication across single-pass release and its recursive ready drain. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The owner fold and drain share one prefix-aware publication witness
-----------------------------------------------------------------------------------------

/-- Buffered ancestor data precedes a child's drain value, including earlier fold output.
Witness: successful owner processing establishes root/retirement certificates before
activation. At the exact pre-value drain boundary the ancestor has retired, so the
supplied common release-prefix ledger cannot retain its buffered contributor.
-/
theorem State.ReleaseDrainOwners.ancestorValue_before {queue : State}
    {work parents groups published} (prefixes : queue.ReleaseDrainOwners groups published)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.key)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    (closed : queue.UncancelledRetiredAncestors work)
    {index group values dependencies key occurrence node value}
    (record : GroupRecordAt work group dependencies) (ancestor : key ∈ dependencies)
    (found : queue.taskNode? occurrence = some node) (stored : node.value = some value)
    (known
      : TaskHasOwners work occurrence (node.task.groups.map Execution.DeliveryNode.key))
    (contributes : key ∈ node.task.groups.map Execution.DeliveryNode.key)
    (present : key ∈ queue.groupNodes.map (fun owner => owner.group.node.key))
    : let released := groups.foldl successGroupStep (queue, [], {})
      let activated := released.1.startNewWork released.2.2
      activated.drainReadyGroups.2[index]? = some (.groupValues group values)
      → key ∉ activated.drainReadyGroups.1.cancelledGroups
      → (occurrence, value)
        ∈ published.take
            ((released.2.1 ++ activated.drainReadyGroups.2.take index).flatMap
              WorkQueueEvent.objectValues).length := by
  dsimp only
  let released := groups.foldl successGroupStep (queue, [], {})
  let activated := released.1.startNewWork released.2.2
  intro selected uncancelled
  obtain ⟨steps, current, bounded, _, active, _, _, same, exactPrefix⟩ :=
    State.drainReadyGroups_go_value_boundary activated.groupNodes.length activated selected
  have folded := successGroupFold_uncancelledRetirement closed generated matching links
    canonical live tasks roots groups
  have protectedRoots := successGroupFold_ancestorsRetired generated matching links canonical
    live tasks roots groups
  have registered := State.startNewWork_registration folded.2.2.1 folded.2.2.2.1 released.2.2
  have prefixRoots := (State.drainReadyGroups_go_uncancelledRetirement
    (folded.2.2.2.2.2.startNewWork released.2.2) generated
    (folded.1.startNewWork _) (folded.2.1.startNewWork _) canonical
    registered.1 registered.2
    (folded.2.2.2.2.1.startNewWork _ protectedRoots.2) steps).1
  have retired := prefixRoots current.group.node.key active group dependencies record
    (congrArg Execution.DeliveryNode.key same.symm) key ancestor occurrence _ known contributes
  have notCancelled : key ∉ (State.drainReadyGroups.go steps activated).1.cancelledGroups :=
    fun member => uncancelled
      (State.drainReadyGroups_go_prefix_cancelledSubset activated (Nat.le_of_lt bounded) member)
  have emitted := (prefixes steps (Nat.le_of_lt bounded)
    occurrence node value found stored key contributes present notCancelled).resolve_right
      (fun retained => retired.2 retained.2)
  change (occurrence, value) ∈ published.take
    ((released.2.1 ++ activated.drainReadyGroups.2.take index).flatMap
      WorkQueueEvent.objectValues).length
  simpa only [State.drainReadyGroups, exactPrefix] using emitted

-----------------------------------------------------------------------------------------
-- Matching generated replay supplies the internal structural premises
-----------------------------------------------------------------------------------------

/-- A generated task handler orders every prepared buffered ancestor before its child.
Witness: derive the full prepared structural frame from matched replay, then apply the
release-prefix theorem on the supplied handler ledger. Storage and noncancellation remain
explicit local obligations; no new assumptions are imposed on the host event source.
-/
theorem ExecutedWork.taskSuccess_drainAncestorValue_before
    {work events occurrence result incoming} {published : List ObjectPublication}
    {index group values dependencies key buffered node value}
    (generated : ExecutedWork work)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (record : GroupRecordAt work group dependencies) (ancestor : key ∈ dependencies)
    (known
      : TaskHasOwners work buffered (node.task.groups.map Execution.DeliveryNode.key))
    (contributes : key ∈ node.task.groups.map Execution.DeliveryNode.key)
    (stored : node.value = some value)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      let prepared :=
        ((queue.putTaskNode
            { incoming with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let activated := released.1.startNewWork released.2.2
      queue.PreparedReleaseOwners (.taskSuccess occurrence result) published
      → queue.taskNode? occurrence = some incoming
      → queue.taskHasHealthyOwner incoming.task = true
      → prepared.taskNode? buffered = some node
      → key ∈ prepared.groupNodes.map (fun owner => owner.group.node.key)
      → activated.drainReadyGroups.2[index]? = some (.groupValues group values)
      → key ∉ activated.drainReadyGroups.1.cancelledGroups
      → (buffered, value)
        ∈ published.take
            ((released.2.1 ++ activated.drainReadyGroups.2.take index).flatMap
              WorkQueueEvent.objectValues).length := by
  intro queue prepared released activated prefixes found healthy lookup present selected uncancelled
  obtain ⟨parents, canonical, groups, links, live, tasks, roots, closed⟩ :=
    generated.replayGraphEvents_preparedRetirement events matching matched incoming
  exact (prefixes incoming found healthy).drain.ancestorValue_before generated groups links
    canonical live tasks roots closed record ancestor lookup stored known contributes present
    selected uncancelled

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
