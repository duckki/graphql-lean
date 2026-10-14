import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReleaseFailureFrontier
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSnapshotProjection

/-! Derive task-catalogue and buffered membership evidence at the actual registration
snapshot, including newly stored values and the per-item pre-drain registration fold.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task TaskNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Registration extends the same generated group topology before pruning begins
-----------------------------------------------------------------------------------------

private structure SnapshotGroupEvidence (queue : Kernel) (work : Work)
    (parents : Nat → WorkQueueSemantics.NodeRefs)
    : Prop where
  matching : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  unique : queue.ChildGroupsUnique

private theorem SnapshotGroupEvidence.integrate {queue : Kernel} {work parents}
    (frame : SnapshotGroupEvidence queue work parents)
    (children : ReferenceWorkQueue.Work)
    (known
      : ∀ group ∈ children.groups,
          ∃ dependencies, ReferenceWorkQueue.GroupRecordAt work group.node dependencies)
    (canonical : ∀ group ∈ children.groups, group.parent = (parents group.node.ref).head?)
    (producer : Option Occurrence := none)
    : SnapshotGroupEvidence (queue.maybeIntegrateWork children producer).1 work parents :=
  ⟨
    frame.matching.maybeIntegrateWork children known producer,
    frame.links.maybeIntegrateWork children canonical producer,
    frame.unique.maybeIntegrateWork children producer
  ⟩

private theorem SnapshotGroupEvidence.integrateItem {queue : Kernel}
    {work parents stream items} (frame : SnapshotGroupEvidence queue work parents)
    (canonical
      : ∀ group dependencies,
          ReferenceWorkQueue.GroupRecordAt work group dependencies
          → dependencies = parents group.ref)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    {item : ReferenceWorkQueue.StreamItem} (member : item ∈ items)
    : SnapshotGroupEvidence (queue.integrateStreamItem item) work parents := by
  have prepared := frame.integrate item.work
    (fun _ listed => matched.streamItem_childGroups_recordAt member listed)
    (fun _ listed => matched.streamItem_childGroups_parentCanonical canonical member listed)
  exact ⟨(prepared.matching.pruneEmptyGroups _).startNewWork _,
    (prepared.links.pruneEmptyGroups _).startNewWork _,
    (prepared.unique.pruneEmptyGroups _).startNewWork _⟩

-----------------------------------------------------------------------------------------
-- Keep just the task evidence needed by the last-owner cleanup reduction
-----------------------------------------------------------------------------------------

/-- Proof-side registration frame; no additional runtime state or source premise. -/
structure SnapshotTaskEvidence (queue : Kernel) (work : Work) : Prop where
  keys : queue.GroupRefsUnique
  live : queue.LiveGroupsRegistered
  contributors : queue.TaskGroupsRegistered
  started : queue.StartedTasksRegistered
  matching : queue.RegisteredTasksMatch work
  buffered : queue.StoredTaskLinks
  sound : queue.GroupMembershipSound

private theorem SnapshotTaskEvidence.integrate {queue : Kernel} {work}
    (frame : SnapshotTaskEvidence queue work) (children : ReferenceWorkQueue.Work)
    (covered
      : ∀ task ∈ children.tasks,
        ∀ key ∈ task.groups.map Execution.DeliveryNode.ref,
          ∃ group ∈ children.groups, group.node.ref = key)
    (matching : ∀ task ∈ children.tasks, ReferenceWorkQueue.TaskMatches work task)
    (producer : Option Occurrence := none)
    : SnapshotTaskEvidence (queue.maybeIntegrateWork children producer).1 work := by
  have registration := queue.maybeIntegrateWork_registration frame.live frame.contributors
    children covered producer
  exact ⟨frame.keys.maybeIntegrateWork children producer, registration.1, registration.2.1,
    frame.started.maybeIntegrateWork children producer,
    frame.matching.maybeIntegrateWork children matching producer,
    frame.buffered.maybeIntegrateWork frame.keys frame.contributors frame.started children producer,
    frame.sound.maybeIntegrateWork children producer⟩

private theorem SnapshotTaskEvidence.integrateItem {queue : Kernel} {work stream items}
    (frame : SnapshotTaskEvidence queue work)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    {item : ReferenceWorkQueue.StreamItem} (member : item ∈ items)
    : SnapshotTaskEvidence (queue.integrateStreamItem item) work := by
  have prepared := frame.integrate item.work (matched.streamItem_childTasksCovered member)
    (by
      intro task listed
      obtain ⟨address, payload, same, known⟩ := matched.streamItem_childTask_producer member listed
      exact ⟨⟨address, payload, some item.occurrence, same, known⟩,
        matched.streamItem_childTask_groupsExact member listed⟩)
  have registration := queue.integrateStreamItem_registration frame.live frame.contributors matched member
  exact ⟨
    (prepared.keys.pruneEmptyGroups _).startNewWork _,
    registration.1,
    registration.2.1,
    (prepared.started.pruneEmptyGroups _).startNewWork _,
    (prepared.matching.pruneEmptyGroups _).startNewWork _,
    (prepared.buffered.pruneEmptyGroups _).startNewWork _,
    (prepared.sound.pruneEmptyGroups _).startNewWork _
  ⟩

theorem eagerRegistrationSnapshot_streamItems (queue : Kernel)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (active : queue.rootStreams.contains stream.ref = true)
    : eagerRegistrationSnapshot queue (.streamItems stream items)
      = queue.preparedStreamItems items := by
  simp only [eagerRegistrationSnapshot, active, ↓reduceIte]

/-- Generated item preparation agrees with the reference before the ready drain.
The supplied projection is derived from generated replay, not a host assumption.
-/
theorem registrationSnapshot_streamItems (queue : Kernel)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (projection : SnapshotProjection queue (.streamItems stream items))
    (active : queue.rootStreams.contains stream.ref = true)
    : registrationSnapshot queue (.streamItems stream items)
      = queue.preparedStreamItems items := by
  rw [projection.items stream items rfl]
  exact eagerRegistrationSnapshot_streamItems queue stream items active

private theorem eagerRegistrationSnapshot_groupEvidence {queue : Kernel} {work parents}
    (frame : SnapshotGroupEvidence queue work parents)
    (canonical
      : ∀ group dependencies,
          ReferenceWorkQueue.GroupRecordAt work group dependencies
          → dependencies = parents group.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : SnapshotGroupEvidence (eagerRegistrationSnapshot queue event) work parents := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [eagerRegistrationSnapshot, found] using frame
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false =>
              simpa only [eagerRegistrationSnapshot, found, healthy, Bool.false_eq_true,
                ↓reduceIte] using frame
          | true =>
              simp only [eagerRegistrationSnapshot, found, healthy, ↓reduceIte]
              have installed : SnapshotGroupEvidence
                  (queue.putTaskNode { node with value := some result.value }) work parents :=
                ⟨frame.matching, frame.links, frame.unique⟩
              exact installed.integrate result.work
                (fun _ member => matching.taskChildGroups_recordAt member)
                (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
                (some occurrence)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [eagerRegistrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] using frame
      | true =>
          rw [eagerRegistrationSnapshot_streamItems queue stream items active]
          exact ReferenceWorkQueue.State.preparedStreamItems_preserves
            (fun current => SnapshotGroupEvidence current work parents) frame items
            (fun _ _ member next => next.integrateItem canonical matching member)
  | taskFailure | streamSuccess | streamFailure => exact frame

-----------------------------------------------------------------------------------------
-- Fresh input identity licenses the new buffered value's existing task memberships
-----------------------------------------------------------------------------------------

/-- Each matching fresh input preserves registration evidence before publication/removal.
Pending accounting justifies storing the incoming value; earlier buffered values retain
their links through registration. Item preparation also covers newly started child tasks.
-/
theorem eagerRegistrationSnapshot_taskEvidence {queue : Kernel} {work settled before}
    (accounted : queue.PendingAccounting work settled) (buffered : queue.StoredTaskLinks)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    : SnapshotTaskEvidence (eagerRegistrationSnapshot queue event) work := by
  have initial : SnapshotTaskEvidence queue work :=
    ⟨accounted.refs, accounted.liveGroups, accounted.taskGroups, accounted.started,
      accounted.matching, buffered, accounted.sound⟩
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [eagerRegistrationSnapshot, found] using initial
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false =>
              simpa only [eagerRegistrationSnapshot, found, healthy, Bool.false_eq_true,
                ↓reduceIte] using initial
          | true =>
              simp only [eagerRegistrationSnapshot, found, healthy, ↓reduceIte]
              have known := ReferenceWorkQueue.State.taskNode?_some found
              have registered := accounted.started node known.1
              have unsettled : node.task.occurrence ∉ settled := by
                rw [known.2]
                intro member
                exact fresh.2.2.1 occurrence List.mem_cons_self (included member)
              have installed : SnapshotTaskEvidence
                  (queue.putTaskNode { node with value := some result.value }) work :=
                ⟨initial.keys, initial.live, initial.contributors,
                  initial.started.putTaskNode _ registered, initial.matching,
                  buffered.putTaskNode _ (fun _ => accounted.links node.task registered unsettled),
                  initial.sound⟩
              exact installed.integrate result.work matching.childTasksCovered
                (by
                  intro task member
                  obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
                  exact ⟨⟨address, payload, some occurrence, same, known⟩,
                    matching.childTask_groupsExact member⟩)
                (some occurrence)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [eagerRegistrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] using initial
      | true =>
          rw [eagerRegistrationSnapshot_streamItems queue stream items active]
          exact ReferenceWorkQueue.State.preparedStreamItems_preserves
            (fun current => SnapshotTaskEvidence current work) initial items
            (fun _ _ member frame => frame.integrateItem matching member)
  | taskFailure | streamSuccess | streamFailure => exact initial

/-- Erasing only fresh empty computation nodes retains all cleanup-frame evidence. -/
theorem SnapshotTaskEvidence.of_projection {queue : Kernel} {work event}
    (projection : SnapshotProjection queue event)
    (frame : SnapshotTaskEvidence (eagerRegistrationSnapshot queue event) work)
    : SnapshotTaskEvidence (registrationSnapshot queue event) work := by
  have catalogue := congrArg ReferenceWorkQueue.State.tasks projection.core
  change (registrationSnapshot queue event).tasks = (eagerRegistrationSnapshot queue event).tasks
    at catalogue
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (registrationCore (registrationSnapshot queue event)).GroupRefsUnique
    rw [projection.core]
    exact frame.keys
  · change (registrationCore (registrationSnapshot queue event)).LiveGroupsRegistered
    rw [projection.core]
    exact frame.live
  · change (registrationCore (registrationSnapshot queue event)).TaskGroupsRegistered
    rw [projection.core]
    exact frame.contributors
  · intro node member
    rw [catalogue]
    exact frame.started node (projection.nodes member)
  · change (registrationCore (registrationSnapshot queue event)).RegisteredTasksMatch work
    rw [projection.core]
    exact frame.matching
  · intro node member stored
    change (registrationCore (registrationSnapshot queue event)).TaskLinkedOn _ _
    rw [projection.core]
    exact frame.buffered node (projection.nodes member) stored
  · change (registrationCore (registrationSnapshot queue event)).GroupMembershipSound
    rw [projection.core]
    exact frame.sound

/-- The old eager frame transfers to the actual delayed snapshot through its projection. -/
theorem registrationSnapshot_taskEvidence {queue : Kernel} {work settled before}
    (projection : SnapshotProjection queue event)
    (accounted : queue.PendingAccounting work settled) (buffered : queue.StoredTaskLinks)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    : SnapshotTaskEvidence (registrationSnapshot queue event) work :=
  SnapshotTaskEvidence.of_projection projection
    (eagerRegistrationSnapshot_taskEvidence accounted buffered included event matching
      fresh)

-----------------------------------------------------------------------------------------
-- Generated replay supplies the frame, including terminal accounting erasure
-----------------------------------------------------------------------------------------

private theorem cleared_taskEvidence (state : State) (work : Work)
    : SnapshotTaskEvidence state.clearRecords.queue work := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ReferenceWorkQueue.State.GroupRefsUnique, State.clearRecords]
  all_goals intro node member; cases member

private theorem cleared_snapshot (state : State) (event : GraphEvent)
    : eagerRegistrationSnapshot state.clearRecords.queue event
      = state.clearRecords.queue := by
  cases event with
  | taskSuccess => rfl
  | streamItems => simp [eagerRegistrationSnapshot, State.clearRecords]
  | taskFailure | streamSuccess | streamFailure => rfl

/-- Generated matching source inputs derive both the registration snapshot's forest and
the actual effect view's forest. New child registration and item activation use the same
 canonical parent map; no caller supplies acyclicity or a traversal budget.
-/
theorem generatedSnapshot_removalForest {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ∃ parents,
        (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
          event).RemovalForest
          parents
        ∧ ∀ events,
            (failurePruningView ((State.initialize work).runNormalized inputs).1.queue
              event events).RemovalForest
              parents := by
  obtain ⟨earlier, matching, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have projection := generatedSnapshot_projection generated valid started
  have eagerForest : ∃ parents,
      (eagerRegistrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
        event).RemovalForest parents := by
    rw [State.runNormalized_initialize work inputs generated earlier started]
    simp only [State.fromReference]
    split
    · refine ⟨fun _ => [], ?_⟩
      rw [cleared_snapshot]
      refine ⟨?_, ?_, ?_⟩
      · intro node member; cases member
      · intro node member; cases member
      · intro node child member; cases member
    · obtain ⟨parents, canonical, links, groups⟩ := generated.runNormalized_groupMetadata earlier
      have frame : SnapshotGroupEvidence
          ((ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)).runNormalized inputs).1
          work parents :=
        ⟨groups, links, ReferenceWorkQueue.createWorkQueue_runNormalized_childGroupsUnique _ _⟩
      have snapshot := eagerRegistrationSnapshot_groupEvidence frame canonical event matching
      exact ⟨parents, ReferenceWorkQueue.State.RemovalForest.of_generated generated
        snapshot.unique snapshot.links snapshot.matching canonical⟩
  obtain ⟨parents, forest⟩ := eagerForest
  have actual : (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
      event).RemovalForest parents := by
    have groups := congrArg ReferenceWorkQueue.State.groupNodes projection.core
    change (registrationSnapshot _ event).groupNodes = (eagerRegistrationSnapshot _ event).groupNodes
      at groups
    refine ⟨?_, ?_, ?_⟩
    · change (registrationCore (registrationSnapshot _ event)).ChildGroupsUnique
      rw [projection.core]
      exact forest.uniqueChildren
    · change (registrationCore (registrationSnapshot _ event)).ChildLinksCanonical parents
      rw [projection.core]
      exact forest.canonical
    · intro parent child memberParent memberChild linked
      rw [groups] at memberParent memberChild
      exact forest.increasing memberParent memberChild linked
  exact ⟨parents, actual, fun _ => failurePruningView_removalForest actual⟩

/-- Every generated started prefix supplies exact catalogue and membership evidence at the
next fresh matching input's registration snapshot. No caller supplies an internal invariant.
The claim includes rejected inputs and vacuous terminal snapshots, without permitting an
invalid input or changing the original source contract.
-/
def GeneratedSnapshotTaskEvidence : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → SnapshotTaskEvidence
        (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
          event) work

/-- Initialization, normalized accounting and source freshness discharge the local frame. -/
theorem GeneratedSnapshotTaskEvidence_holds : GeneratedSnapshotTaskEvidence := by
  intro work inputs event generated valid started
  obtain ⟨earlier, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  apply SnapshotTaskEvidence.of_projection (generatedSnapshot_projection generated valid started)
  rw [State.runNormalized_initialize work inputs generated earlier started]
  simp only [State.fromReference]
  split
  · rw [cleared_snapshot]
    exact cleared_taskEvidence _ _
  · obtain ⟨settled, included, accounted⟩ := generated.runNormalized_pendingAccounting inputs earlier started
    apply eagerRegistrationSnapshot_taskEvidence accounted
      (generated.runNormalized_storedTaskLinks inputs earlier started) included event matching fresh

/-- Generated snapshot lookups use the permanent catalogue's exact contributing owners. -/
theorem generatedSnapshot_taskCatalogue {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    {occurrence node}
    (found
      : (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
          event).taskNode?
          occurrence
        = some node)
    : ∃ task,
        (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
            event).task?
            occurrence
          = some task
        ∧ task.groups = node.task.groups := by
  have frame := GeneratedSnapshotTaskEvidence_holds work inputs event generated valid started
  exact canonicalTaskCatalogue frame.started frame.matching found

-----------------------------------------------------------------------------------------
-- Consume derived evidence at the actual generated single-event dispatch
-----------------------------------------------------------------------------------------

/-- Generated topology facts license held-source membership in a supplied mathematical
frontier trace. This does not identify that trace with actual handler effects; actual
disposal is constructed independently in PreparedSourceProgress.
-/
theorem generatedSnapshot_failureFrontierSource {work inputs event occurrence}
    {node : TaskNode} {key : Nat}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    (found
      : (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
          event).taskNode?
          occurrence
        = some node)
    (stored : node.value.isSome = true)
    (pending
      : pruningPending
          (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
            event) event
          ((((State.initialize work).runNormalized inputs).1.queue.handleGraphEvent
              event).2) occurrence
        = true)
    (owned
      : ∃ owner ∈ node.task.groups,
          ∃ group,
            (failurePruningView ((State.initialize work).runNormalized inputs).1.queue
              event
              ((((State.initialize work).runNormalized inputs).1.queue.handleGraphEvent
                  event).2)).groupNode?
              owner.ref
            = some group)
    (cut
      : ∀ owner ∈ node.task.groups,
          ∀ group,
            (failurePruningView ((State.initialize work).runNormalized inputs).1.queue
                event
                ((((State.initialize work).runNormalized inputs).1.queue.handleGraphEvent
                    event).2)).groupNode?
                owner.ref
              = some group
            → ∃ root ∈
                failureRoots
                  ((((State.initialize work).runNormalized
                      inputs).1.queue.handleGraphEvent
                      event).2),
                (failurePruningView ((State.initialize work).runNormalized inputs).1.queue
                  event
                  ((((State.initialize work).runNormalized
                      inputs).1.queue.handleGraphEvent
                      event).2)).LiveDescendant
                  root owner.ref)
    (held : key ∈ node.childStreams)
    {final targets}
    (trace
      : let before := ((State.initialize work).runNormalized inputs).1.queue
        let events := (before.handleGraphEvent event).2
        PruningGroups (failurePruningView before event events) (failureRoots events) final
          targets)
    : .stream key ∈ targets := by
  have frame := GeneratedSnapshotTaskEvidence_holds work inputs event generated valid started
  obtain ⟨parents, _, viewForest⟩ := generatedSnapshot_removalForest generated valid started
  obtain ⟨task, catalogue, groups⟩ := canonicalTaskCatalogue frame.started frame.matching found
  have linked := frame.buffered node (List.mem_of_find?_eq_some found) stored
  rw [(ReferenceWorkQueue.State.taskNode?_some found).2] at linked
  exact failureFrontier_heldSource trace (viewForest _) linked pending found catalogue groups owned cut held

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
