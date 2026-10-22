import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedDrainProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRootCompletion

/-! Derive compatible ready-drain frames at the actual reference handler phases.
These constructions use generated source prefixes, not a desired reduction endpoint or
alternative replay equivalence. The registration bridge can transport them afterwards.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs Occurrence)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

/-- Proof notation for the reference task-success state immediately before ready draining.
It names the actual shared registration/owner/release calculation, not a new public queue
algorithm or a cleanup observer.
-/
def referenceTaskSuccessReady (queue : ReferenceWorkQueue.State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (available : List (Occurrence × Nat) := [])
    : ReferenceWorkQueue.State :=
  let integrated :=
    (ReferenceWorkQueue.State.maybeIntegrateWork
      (queue.putTaskNode { node with value := some result.value }) result.work
      (some occurrence)).1
  let released :=
    node.task.groups.foldl ReferenceWorkQueue.successGroupStep (integrated, [], {})
  (released.1.startNewWork released.2.2 available).1

theorem referencePrefix_childGroupsUnique (work : Work) (events : List GraphEvent)
    : (ReferenceWorkQueue.State.replayGraphEvents
        (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work))
        events).ChildGroupsUnique := by
  have loop (more : List GraphEvent) (queue : ReferenceWorkQueue.State)
      (unique : queue.ChildGroupsUnique)
      : (queue.replayGraphEvents more).ChildGroupsUnique := by
    induction more generalizing queue with
    | nil => exact unique
    | cons event rest ih => exact ih _ (unique.handleGraphEvent event)
  exact loop events _ (ReferenceWorkQueue.createWorkQueue_childGroupsUnique _)

theorem referencePrefix_removalForest {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ∃ parents,
        (ReferenceWorkQueue.State.replayGraphEvents
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events).RemovalForest
          parents := by
  obtain ⟨parents, canonical, frame⟩ := generated.replay_rootClosureFrame matching
  exact ⟨parents, ReferenceWorkQueue.State.RemovalForest.of_generated generated
    (referencePrefix_childGroupsUnique work events) frame.links frame.records canonical⟩

private theorem childGroupsUnique_successFold (groups : List Execution.DeliveryNode)
    (acc : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork)
    (unique : acc.1.ChildGroupsUnique)
    : (groups.foldl ReferenceWorkQueue.successGroupStep acc).1.ChildGroupsUnique := by
  induction groups generalizing acc with
  | nil => exact unique
  | cons group rest ih =>
      simp only [List.foldl_cons, ReferenceWorkQueue.successGroupStep]
      split
      · exact ih _ unique
      · rename_i node found
        have changed := unique.putGroupNode { node with pending := node.pending - 1 }
          (unique node (List.mem_of_find?_eq_some found))
        split
        · exact ih _ (changed.finishGroupSuccess _)
        · exact ih _ changed

private theorem childGroupsUnique_preparedItems (queue : ReferenceWorkQueue.State)
    (unique : queue.ChildGroupsUnique) (items : List ReferenceWorkQueue.StreamItem)
    (available : List (Occurrence × Nat) := [])
    : (queue.preparedStreamItems items available).ChildGroupsUnique :=
  ReferenceWorkQueue.State.preparedStreamItems_preserves
    ReferenceWorkQueue.State.ChildGroupsUnique unique items available
    (fun _ item _ prior =>
      ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available)

/-- Structural queue certificates justify task-success startup at any actual source cut.
Witness: eager child registration and the successful contributor fold retain exact
ownership, canonical child links and duplicate-free children before cached cleanup.
-/
theorem taskSuccess_startFrames {queue : ReferenceWorkQueue.State} {work : Work}
    {parents : Nat → NodeRefs} (generated : ReferenceWorkQueue.ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (roots : ReferenceWorkQueue.LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work)
    (owners : queue.TaskOwnerFrame work) (children : queue.ChildGroupsUnique)
    (occurrence : Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (matched
      : (ReferenceWorkQueue.GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (node : ReferenceWorkQueue.TaskNode) (found : queue.taskNode? occurrence = some node)
    : let prepared :=
        ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      let released :=
        node.task.groups.foldl ReferenceWorkQueue.successGroupStep (prepared, [], {})
      released.1.TaskOwnerFrame work ∧ released.1.RemovalForest parents := by
  have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
    intro task member
    obtain ⟨address, payload, same, located⟩ := matched.childTask_producer member
    exact ⟨⟨address, payload, some occurrence, same, located⟩, matched.childTask_groupsExact member⟩
  have stored := owners.putExistingTaskNode node (List.mem_of_find?_eq_some found)
    { node with value := some result.value } rfl
  have integrated := stored.maybeIntegrateWork roots.present roots.tasks result.work known
    (some occurrence)
  let current := queue.putTaskNode { node with value := some result.value }
  have currentRecords : current.GroupNodesMatchWork work := roots.records
  have currentLinks : current.ChildLinksCanonical parents := roots.links
  have currentLive : current.LiveGroupsRegistered := roots.registered
  have currentTasks : current.TaskGroupsRegistered := roots.tasks
  have currentRoots : current.RootAncestorsRetired work := roots.roots
  have currentRetired : current.UncancelledRetiredAncestors work := retired
  have fields := fun group member =>
    matched.taskChildGroups_parentCanonical canonical (group := group) member
  have records := fun group member => matched.taskChildGroups_recordAt (group := group) member
  have supplied := (context.children node.task
    (context.started node (ReferenceWorkQueue.State.taskNode?_some found).1)).sourceChild
      (ReferenceWorkQueue.State.taskNode?_some found).2 matched
  have registration := current.maybeIntegrateWork_registration currentLive currentTasks
    result.work supplied.contributors (some occurrence)
  have preparedRecords := currentRecords.maybeIntegrateWork result.work records (some occurrence)
  have preparedLinks := currentLinks.maybeIntegrateWork result.work fields (some occurrence)
  have preparedRoots := currentRoots.mono (by
    rw [ReferenceWorkQueue.State.maybeIntegrateWork_rootGroups]
    exact fun _ member => member)
    (fun _ prior => prior.maybeIntegrateWork result.work (some occurrence))
  have folded := ReferenceWorkQueue.successGroupFold_uncancelledRetirement
    (currentRetired.maybeIntegrateWork result.work (some occurrence) generated currentLive
      (by
        intro group member
        obtain ⟨dependencies, known⟩ := records group member
        exact ⟨dependencies, known, by rw [canonical _ _ known]; exact fields group member⟩)
      supplied.parentRefs) generated
    preparedRecords preparedLinks canonical registration.1 registration.2.1
    preparedRoots node.task.groups
  have currentChildren : current.ChildGroupsUnique := children
  have preparedChildren := currentChildren.maybeIntegrateWork result.work (some occurrence)
  exact ⟨integrated.successFold node.task.groups [] {},
    ReferenceWorkQueue.State.RemovalForest.of_generated generated
      (childGroupsUnique_successFold node.task.groups (_, [], {}) preparedChildren)
      folded.2.1 folded.1 canonical⟩

/-- Any matching item prefix supplies concrete ownership and removal frames for its next item.
Witness: fixed-snapshot preparation preserves structural roots, and exact child provenance
licenses registration before pruning. No flattened replay state is used.
-/
theorem streamItem_startFrames {queue : ReferenceWorkQueue.State} {work : Work}
    {parents : Nat → NodeRefs} (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (roots : ReferenceWorkQueue.LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work)
    (owners : queue.TaskOwnerFrame work) (children : queue.ChildGroupsUnique)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    (earlier : List ReferenceWorkQueue.StreamItem) (included : earlier.Subset items)
    (item : ReferenceWorkQueue.StreamItem) (member : item ∈ items)
    (available : List (Occurrence × Nat))
    : let prepared :=
        (queue.preparedStreamItems earlier available).maybeIntegrateWork item.work
      let pruned := (prepared.1.pruneEmptyGroups prepared.2.newGroups).1
      pruned.TaskOwnerFrame work ∧ pruned.RemovalForest parents := by
  have partialMatch : (ReferenceWorkQueue.GraphEvent.streamItems stream earlier).MatchesWork work :=
    fun item member => matched item (included member)
  have preparedOwners := owners.prepareItems_of_registered roots.registered roots.tasks
    roots.present generated.declarations partialMatch available
  have frame := (roots.prepareItems retired generated canonical partialMatch available).1
  have known : ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
    intro task supplied
    obtain ⟨address, payload, same, located⟩ :=
      matched.streamItem_childTask_producer member supplied
    exact ⟨⟨address, payload, some item.occurrence, same, located⟩,
      matched.streamItem_childTask_groupsExact member supplied⟩
  have fields := fun group supplied =>
    matched.streamItem_childGroups_parentCanonical canonical member (group := group) supplied
  have records := fun group supplied =>
    matched.streamItem_childGroups_recordAt member (group := group) supplied
  have integrated := preparedOwners.maybeIntegrateWork frame.present frame.tasks item.work known
  have preparedChildren := (childGroupsUnique_preparedItems queue children earlier available
    ).maybeIntegrateWork item.work
  exact ⟨integrated.pruneEmptyGroups _,
    ReferenceWorkQueue.State.RemovalForest.of_generated generated
      (preparedChildren.pruneEmptyGroups _)
      ((frame.links.maybeIntegrateWork item.work fields).pruneEmptyGroups _)
      ((frame.records.maybeIntegrateWork item.work records).pruneEmptyGroups _) canonical⟩

/-- Complete item preparation supplies the concrete frames required by the fused drain. -/
theorem streamItems_drainFrames {queue : ReferenceWorkQueue.State} {work : Work}
    {parents : Nat → NodeRefs} (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (roots : ReferenceWorkQueue.LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work)
    (owners : queue.TaskOwnerFrame work) (children : queue.ChildGroupsUnique)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat))
    : (queue.preparedStreamItems items available).TaskOwnerFrame work
      ∧ (queue.preparedStreamItems items available).RemovalForest parents := by
  have frame := (roots.prepareItems retired generated canonical matched available).1
  exact ⟨owners.prepareItems_of_registered roots.registered roots.tasks roots.present
    generated.declarations matched available,
    ReferenceWorkQueue.State.RemovalForest.of_generated generated
      (childGroupsUnique_preparedItems queue children items available)
      frame.links frame.records canonical⟩

/-- Generated pre-startup frames justify fused cached removal before ready draining. -/
theorem referencePrefix_taskSuccess_startFrames {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (occurrence : Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work
          (events ++ [.taskSuccess occurrence result]))
    (accepted
      : ReferenceWorkQueue.State.eventsStarted []
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events
        = true)
    (node : ReferenceWorkQueue.TaskNode)
    (found
      : (ReferenceWorkQueue.State.replayGraphEvents
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events).taskNode?
          occurrence
        = some node)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let prepared :=
        ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      let ready :=
        (node.task.groups.foldl ReferenceWorkQueue.successGroupStep (prepared, [], {})).1
      ∃ parents, ready.TaskOwnerFrame work ∧ ready.RemovalForest parents := by
  obtain ⟨prior, matched, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have sources : ∀ event ∈ events, event.MatchesWork work :=
    fun _ member => prior.eachMatches member
  have roots := generated.replayGraphEvents_rootsPresent events sources
  have accounted := (ReferenceWorkQueue.createWorkQueue_pendingAccounting work generated.declarations).replayGraphEvents
    (before := []) generated events prior accepted
  have frame := generated.replayGraphEvents_taskOwnerFrame_of_matching events sources
  have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
    intro task member
    obtain ⟨address, payload, same, located⟩ := matched.childTask_producer member
    exact ⟨⟨address, payload, some occurrence, same, located⟩, matched.childTask_groupsExact member⟩
  have stored := frame.putExistingTaskNode node (List.mem_of_find?_eq_some found)
    { node with value := some result.value } rfl
  have integrated := stored.maybeIntegrateWork roots accounted.taskGroups result.work known
    (some occurrence)
  let queue := ReferenceWorkQueue.State.replayGraphEvents
    (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)) events
  let prepared := ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
    result.work (some occurrence)).1
  let released := node.task.groups.foldl ReferenceWorkQueue.successGroupStep (prepared, [], {})
  have ownerFrame := integrated.successFold node.task.groups [] {}
  obtain ⟨parents, canonical, records, links, live, tasks, ancestors, retired⟩ :=
    generated.replayGraphEvents_preparedRetirement events sources matched node (found := found)
  have folded := ReferenceWorkQueue.successGroupFold_uncancelledRetirement retired
    generated records links canonical live tasks ancestors node.task.groups
  have initialChildren := referencePrefix_childGroupsUnique work events
  have storedChildren
      : (queue.putTaskNode { node with value := some result.value }).ChildGroupsUnique :=
    initialChildren
  have preparedChildren := storedChildren.maybeIntegrateWork result.work (some occurrence)
  have children := childGroupsUnique_successFold node.task.groups (_, [], {}) preparedChildren
  exact ⟨parents, ownerFrame, ReferenceWorkQueue.State.RemovalForest.of_generated
    generated children folded.2.1 folded.1 canonical⟩

/-- The same reference task-success ready boundary supplies owners and the removal forest.
All local record and forest premises are independently derived at that exact phase.
-/
theorem referencePrefix_taskSuccess_drainFrames {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (occurrence : Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work
          (events ++ [.taskSuccess occurrence result]))
    (accepted
      : ReferenceWorkQueue.State.eventsStarted []
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events
        = true)
    (node : ReferenceWorkQueue.TaskNode)
    (found
      : (ReferenceWorkQueue.State.replayGraphEvents
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events).taskNode?
          occurrence
        = some node)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let ready := referenceTaskSuccessReady queue occurrence result node
      ∃ parents, ready.TaskOwnerFrame work ∧ ready.RemovalForest parents := by
  obtain ⟨prior, matched, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have sources : ∀ event ∈ events, event.MatchesWork work :=
    fun _ member => prior.eachMatches member
  have roots := generated.replayGraphEvents_rootsPresent events sources
  have accounted := (ReferenceWorkQueue.createWorkQueue_pendingAccounting work generated.declarations).replayGraphEvents
    (before := []) generated events prior accepted
  have frame := generated.replayGraphEvents_taskOwnerFrame_of_matching events sources
  have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
    intro task member
    obtain ⟨address, payload, same, located⟩ := matched.childTask_producer member
    exact ⟨⟨address, payload, some occurrence, same, located⟩, matched.childTask_groupsExact member⟩
  have stored := frame.putExistingTaskNode node (List.mem_of_find?_eq_some found)
    { node with value := some result.value } rfl
  have integrated := stored.maybeIntegrateWork roots accounted.taskGroups result.work known
    (some occurrence)
  let queue := ReferenceWorkQueue.State.replayGraphEvents
    (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)) events
  let prepared := ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
    result.work (some occurrence)).1
  let released := node.task.groups.foldl ReferenceWorkQueue.successGroupStep (prepared, [], {})
  have ready := (integrated.successFold node.task.groups [] {}).startNewWork released.2.2
  obtain ⟨parents, canonical, metadata⟩ := generated.taskSuccess_drain_liveRootFrame
    sources matched node found roots
  have initialChildren := referencePrefix_childGroupsUnique work events
  have storedChildren
      : (queue.putTaskNode { node with value := some result.value }).ChildGroupsUnique :=
    initialChildren
  have integratedChildren := storedChildren.maybeIntegrateWork result.work (some occurrence)
  have readyChildren := (childGroupsUnique_successFold node.task.groups (_, [], {})
    integratedChildren).startNewWork released.2.2
  refine ⟨parents, ready, ReferenceWorkQueue.State.RemovalForest.of_generated generated
    readyChildren metadata.links metadata.records canonical⟩

/-- Each generated item supplies owner and forest frames before cached group startup. -/
theorem referencePrefix_streamItem_startFrames {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (valid : ReferenceWorkQueue.ValidGraphEvents work events)
    (accepted
      : ReferenceWorkQueue.State.eventsStarted []
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events
        = true)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    (earlier : List ReferenceWorkQueue.StreamItem) (included : earlier.Subset items)
    (item : ReferenceWorkQueue.StreamItem) (member : item ∈ items)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let prepared := (queue.preparedStreamItems earlier).maybeIntegrateWork item.work
      let pruned := (prepared.1.pruneEmptyGroups prepared.2.newGroups).1
      ∃ parents, pruned.TaskOwnerFrame work ∧ pruned.RemovalForest parents := by
  have sources : ∀ event ∈ events, event.MatchesWork work :=
    fun _ member => valid.eachMatches member
  have partialMatch : (ReferenceWorkQueue.GraphEvent.streamItems stream earlier).MatchesWork work :=
    fun item member => matched item (included member)
  have roots := generated.replayGraphEvents_rootsPresent events sources
  have accounted := (ReferenceWorkQueue.createWorkQueue_pendingAccounting work generated.declarations).replayGraphEvents
    (before := []) generated events valid accepted
  have owners :=
    (generated.replayGraphEvents_taskOwnerFrame_of_matching events sources).prepareItems
    accounted roots partialMatch
  obtain ⟨parents, canonical, frame⟩ := generated.streamItems_prepared_liveRootFrame
    sources partialMatch roots
  have known : ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
    intro task supplied
    obtain ⟨address, payload, same, located⟩ :=
      matched.streamItem_childTask_producer member supplied
    exact ⟨⟨address, payload, some item.occurrence, same, located⟩,
      matched.streamItem_childTask_groupsExact member supplied⟩
  have fields := fun group supplied =>
    matched.streamItem_childGroups_parentCanonical canonical member (group := group) supplied
  have records := fun group supplied =>
    matched.streamItem_childGroups_recordAt member (group := group) supplied
  have integrated := owners.maybeIntegrateWork frame.present frame.tasks item.work known
  have children := (childGroupsUnique_preparedItems _
    (referencePrefix_childGroupsUnique work events) earlier).maybeIntegrateWork item.work
  exact ⟨parents, integrated.pruneEmptyGroups _,
    ReferenceWorkQueue.State.RemovalForest.of_generated generated
      (children.pruneEmptyGroups _)
      ((frame.links.maybeIntegrateWork item.work fields).pruneEmptyGroups _)
      ((frame.records.maybeIntegrateWork item.work records).pruneEmptyGroups _) canonical⟩

/-- Arbitrary-width prepared stream items have one compatible owner/forest endpoint. -/
theorem referencePrefix_streamItems_drainFrames {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (valid : ReferenceWorkQueue.ValidGraphEvents work events)
    (accepted
      : ReferenceWorkQueue.State.eventsStarted []
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events
        = true)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      ∃ parents,
        (queue.preparedStreamItems items).TaskOwnerFrame work
        ∧ (queue.preparedStreamItems items).RemovalForest parents := by
  have sources : ∀ event ∈ events, event.MatchesWork work :=
    fun _ member => valid.eachMatches member
  have roots := generated.replayGraphEvents_rootsPresent events sources
  have accounted := (ReferenceWorkQueue.createWorkQueue_pendingAccounting work generated.declarations).replayGraphEvents
    (before := []) generated events valid accepted
  have frame := generated.replayGraphEvents_taskOwnerFrame_of_matching events sources
  obtain ⟨parents, canonical, metadata⟩ :=
    generated.streamItems_prepared_liveRootFrame sources matched roots
  exact ⟨parents, frame.prepareItems accounted roots matched,
    ReferenceWorkQueue.State.RemovalForest.of_generated generated
      (childGroupsUnique_preparedItems _ (referencePrefix_childGroupsUnique work events) items)
      metadata.links metadata.records canonical⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
