import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerPublicationLedger
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
    {work parents groups published} {available : List (Occurrence × Nat)}
    (prefixes : queue.ReleaseDrainOwners groups published available)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.ref)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (roots : queue.RootAncestorsRetired work)
    (closed : queue.UncancelledRetiredAncestors work)
    {index group values dependencies ref occurrence node value}
    (record : GroupRecordAt work group dependencies) (ancestor : ref ∈ dependencies)
    (found : queue.taskNode? occurrence = some node) (stored : node.value = some value)
    (known
      : TaskHasOwners work occurrence (node.task.groups.map Execution.DeliveryNode.ref))
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref))
    : let released := groups.foldl successGroupStep (queue, [], {})
      let activated := (released.1.startNewWork released.2.2 available).1
      (activated.drainReadyGroups available).2.1[index]?
        = some (.groupValues group values)
      → ref ∉ (activated.drainReadyGroups available).1.cancelledGroups
      → (occurrence, value)
        ∈ published.take
            ((released.2.1
              ++ (activated.drainReadyGroups available).2.1.take index).flatMap
              WorkQueueEvent.objectValues).length := by
  dsimp only
  let released := groups.foldl successGroupStep (queue, [], {})
  let activated := (released.1.startNewWork released.2.2 available).1
  intro selected uncancelled
  obtain ⟨steps, current, bounded, _, active, _, same, exactPrefix⟩ :=
    State.drainReadyGroups_go_value_boundary activated.groupNodes.length activated available
      selected
  have folded := successGroupFold_uncancelledRetirement closed generated matching links
    canonical live tasks roots groups
  have protectedRoots := successGroupFold_ancestorsRetired generated matching links canonical
    live tasks roots groups
  have registered := State.startNewWork_registration folded.2.2.1 folded.2.2.2.1
    released.2.2 available
  have prefixRoots := (State.drainReadyGroups_go_uncancelledRetirement
    (folded.2.2.2.2.2.startNewWork released.2.2 available) generated
    (folded.1.startNewWork _ available) (folded.2.1.startNewWork _ available) canonical
    registered.1 registered.2
    (folded.2.2.2.2.1.startNewWork _ protectedRoots.2 available) steps available).1
  have retired := prefixRoots current.group.node.ref active group dependencies record
    (congrArg Execution.DeliveryNode.ref same.symm) ref ancestor occurrence _ known contributes
  have notCancelled
      : ref ∉ (State.drainReadyGroups.go available steps activated).1.cancelledGroups :=
    fun member => uncancelled
      (State.drainReadyGroups_go_prefix_cancelledSubset activated (Nat.le_of_lt bounded) available
        member)
  have emitted := (prefixes steps (Nat.le_of_lt bounded)
    occurrence node value found stored ref contributes present notCancelled).resolve_right
      (fun retained => retired.2 retained.2)
  change (occurrence, value) ∈ published.take
    ((released.2.1 ++ (activated.drainReadyGroups available).2.1.take index).flatMap
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
    {index group values dependencies ref buffered node value}
    (generated : ExecutedWork work)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (record : GroupRecordAt work group dependencies) (ancestor : ref ∈ dependencies)
    (known
      : TaskHasOwners work buffered (node.task.groups.map Execution.DeliveryNode.ref))
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (stored : node.value = some value)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents events
      let prepared :=
        ((queue.putTaskNode
            { incoming with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let activated := (released.1.startNewWork released.2.2).1
      queue.PreparedReleaseOwners (.taskSuccess occurrence result) published
      → queue.taskNode? occurrence = some incoming
      → prepared.taskNode? buffered = some node
      → ref ∈ prepared.groupNodes.map (fun owner => owner.group.node.ref)
      → activated.drainReadyGroups.2.1[index]? = some (.groupValues group values)
      → ref ∉ activated.drainReadyGroups.1.cancelledGroups
      → (buffered, value)
        ∈ published.take
            ((released.2.1 ++ activated.drainReadyGroups.2.1.take index).flatMap
              WorkQueueEvent.objectValues).length := by
  intro queue prepared released activated prefixes found lookup present selected uncancelled
  obtain ⟨parents, canonical, groups, links, live, tasks, roots, closed⟩ :=
    generated.replayGraphEvents_preparedRetirement events matching matched incoming (found := found)
  exact State.ReleaseDrainOwners.ancestorValue_before (prefixes incoming found).drain
    generated groups links
    canonical live tasks roots closed record ancestor lookup stored known contributes present
    selected uncancelled

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
