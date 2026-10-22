import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitializationSpecialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ParentCutsTransitions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain

/-! Derive live-parent safety from actual generated queue execution. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Shared structural evidence follows the same concrete accumulator
-----------------------------------------------------------------------------------------

/-- Shared proof certificate for canonical registration and live-parent cancellation safety. -/
structure ParentCutFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs)
    : Prop where
  safe : queue.LiveParentsUncancelled
  keys : queue.GroupRefsUnique
  records : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  children : queue.ChildGroupsUnique
  live : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  closed : queue.ParentRegistryClosed parents
  fields : queue.GroupParentsCanonical parents
  complete : queue.ParentLinksComplete parents
  cancelled : queue.CancellationsRetired
  registration : queue.RegistrationFrame work

theorem ParentCutFrame.removeTask {queue work parents}
    (frame : ParentCutFrame queue work parents) (occurrence : Occurrence)
    : ParentCutFrame (queue.removeTask occurrence) work parents := by
  refine ⟨frame.safe.removeTask _, frame.keys.removeTask _, frame.records.removeTask _,
    frame.links.removeTask _, frame.children.removeTask _, ?_, frame.tasks,
    frame.closed, frame.fields.removeTask _, frame.complete.removeTask _,
    frame.cancelled.of_frame rfl (fun _ retired => retired.removeTask occurrence), ?_⟩
  · intro node member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    exact frame.live old oldMember
  · apply frame.registration.retain (next := queue.removeTask occurrence)
      (fun node member => by
        obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
        exact frame.live old oldMember) frame.tasks
      (frame.registration.started.removeTask occurrence)
    · exact fun _ member => member
    · exact fun _ member => member

theorem ParentCutFrame.putGroupNode {queue work parents key node}
    (frame : ParentCutFrame queue work parents) (found : queue.groupNode? key = some node)
    (updated : GroupNode) (sameGroup : updated.group = node.group)
    (sameChildren : updated.childGroups = node.childGroups)
    : ParentCutFrame (queue.putGroupNode updated) work parents := by
  have member := List.mem_of_find?_eq_some found
  refine ⟨
    frame.safe.putGroupNode _ ?_,
    frame.keys.putGroupNode _,
    frame.records.putGroupNode _ ?_,
    frame.links.putGroupNode _ ?_,
    frame.children.putGroupNode _ ?_,
    frame.live.putGroupNode _ ?_,
    frame.tasks,
    frame.closed,
    frame.fields.putGroupNode _ ?_,
    frame.complete.putGroupNode frame.keys found _ ?_ ?_,
    frame.cancelled.putGroupNode _,
    frame.registration.putGroupNode _
      (by
        rw [sameGroup]; exact frame.live node member)
  ⟩
  · simpa only [sameGroup] using frame.safe node member
  · simpa only [sameGroup] using frame.records node member
  · simpa only [sameGroup, sameChildren] using frame.links node member
  · simpa only [sameChildren] using frame.children node member
  · simpa only [sameGroup] using frame.live node member
  · simpa only [sameGroup] using frame.fields node member
  · rw [sameGroup]
  · rw [sameChildren]; exact List.Subset.refl _

theorem ParentCutFrame.pruneEmptyGroups {queue work parents}
    (frame : ParentCutFrame queue work parents) (groups : List Execution.DeliveryNode)
    : ParentCutFrame (queue.pruneEmptyGroups groups).1 work parents := by
  have registered := queue.pruneEmptyGroups_registration frame.live frame.tasks groups
  exact ⟨frame.safe.pruneEmptyGroups _, frame.keys.pruneEmptyGroups _,
    frame.records.pruneEmptyGroups _, frame.links.pruneEmptyGroups _,
    frame.children.pruneEmptyGroups _, registered.1, registered.2.1,
    frame.closed.of_sameRegistry registered.2.2, frame.fields.pruneEmptyGroups _,
    frame.complete.pruneEmptyGroups _, frame.cancelled.pruneEmptyGroups _,
    frame.registration.pruneEmptyGroups _⟩

theorem ParentCutFrame.startNewWork {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (released : NewWork) (available : List (Occurrence × Nat) := [])
    : ParentCutFrame (queue.startNewWork released available).1 work parents := by
  have registered := State.startNewWork_registration frame.live frame.tasks released available
  have forest := State.RemovalForest.of_generated generated frame.children frame.links
    frame.records canonical
  exact ⟨frame.safe.startNewWork frame.keys frame.fields frame.complete forest _ available,
    frame.keys.startNewWork _ available, frame.records.startNewWork _ available,
    frame.links.startNewWork _ available, frame.children.startNewWork _ available,
    registered.1, registered.2,
    frame.closed.of_sameRegistry (queue.startNewWork_registeredGroups released available),
    frame.fields.startNewWork _ available, frame.complete.startNewWork _ available,
    frame.cancelled.startNewWork frame.live _ available, frame.registration.startNewWork _ available⟩

theorem ParentCutFrame.cacheTaskFailures {queue work parents}
    (frame : ParentCutFrame queue work parents) (available : List (Occurrence × Nat))
    : ParentCutFrame (queue.cacheTaskFailures available) work parents := by
  have included : (queue.cacheTaskFailures available).groupNodes.Subset queue.groupNodes := by
    rw [State.cacheTaskFailures_groupNodes]
    exact List.Subset.refl _
  have registered := State.cacheTaskFailures_registration frame.live frame.tasks available
  exact ⟨
    frame.safe.of_subset included (queue.cacheTaskFailures_cancelledGroups available),
    frame.keys.cacheTaskFailures _,
    frame.records.cacheTaskFailures _,
    frame.links.cacheTaskFailures _,
    frame.children.cacheTaskFailures _,
    registered.1,
    registered.2,
    frame.closed.of_sameRegistry (queue.cacheTaskFailures_registeredGroups available),
    frame.fields.cacheTaskFailures _,
    frame.complete.of_subset included,
    frame.cancelled.cacheTaskFailures _, frame.registration.cacheTaskFailures _
  ⟩

theorem ParentCutFrame.finishGroupSuccess {queue work parents}
    (frame : ParentCutFrame queue work parents) (group : GroupNode)
    : ParentCutFrame (queue.finishGroupSuccess group).1 work parents := by
  have registered := queue.finishGroupSuccess_registration frame.live frame.tasks group
  exact ⟨frame.safe.finishGroupSuccess _, frame.keys.finishGroupSuccess _,
    frame.records.finishGroupSuccess _, frame.links.finishGroupSuccess _,
    frame.children.finishGroupSuccess _, registered.1, registered.2.1,
    frame.closed.of_sameRegistry registered.2.2, frame.fields.finishGroupSuccess _,
    frame.complete.finishGroupSuccess _, frame.cancelled.finishGroupSuccess _,
    frame.registration.finishGroupSuccess _⟩

theorem ParentCutFrame.removeGroup {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (root : Nat)
    : ParentCutFrame (queue.removeGroup root) work parents := by
  have forest := State.RemovalForest.of_generated generated frame.children frame.links
    frame.records canonical
  refine ⟨frame.safe.removeGroup frame.keys frame.fields frame.complete forest root,
    frame.keys.removeGroup _, frame.records.removeGroup _, frame.links.removeGroup _,
    frame.children.removeGroup _, fun node member => frame.live node (List.mem_filter.mp member).1,
    frame.tasks, frame.closed, frame.fields.removeGroup _, frame.complete.removeGroup _,
    frame.cancelled.removeGroup frame.live root, ?_⟩
  apply frame.registration.retain (next := queue.removeGroup root)
    (fun node member => frame.live node (List.mem_filter.mp member).1) frame.tasks
    (frame.registration.started.removeGroup root)
  · exact fun _ member => member
  · exact fun _ member => member

theorem ParentCutFrame.maybeIntegrateWork {queue work parents}
    (frame : ParentCutFrame queue work parents) (newWork : Work)
    (known
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (fields : ∀ group ∈ newWork.groups, group.parent = (parents group.node.ref).head?)
    (certificate
      : DeclarationCoverage.WorkCertificate work queue.registeredGroups newWork)
    (parentTask : Option Occurrence := none)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : ParentCutFrame (queue.maybeIntegrateWork newWork parentTask).1 work parents := by
  have registered := queue.maybeIntegrateWork_registration frame.live frame.tasks
    newWork certificate.contributors parentTask
  exact ⟨frame.safe.maybeIntegrateWork frame.live frame.closed frame.fields _ fields
      frame.cancelled generated known canonical certificate.parents _,
    frame.keys.maybeIntegrateWork _ _, frame.records.maybeIntegrateWork _ known _,
    frame.links.maybeIntegrateWork _ fields _, frame.children.maybeIntegrateWork _ _,
    registered.1, registered.2.1,
    frame.closed.maybeIntegrateWork frame.live _ fields certificate.parents _,
    frame.fields.maybeIntegrateWork _ fields _,
    frame.complete.maybeIntegrateWork frame.keys frame.live frame.closed _ fields _,
    frame.cancelled.maybeIntegrateWork _ _,
    (frame.registration.maybeIntegrateWork _ certificate _).1⟩

-----------------------------------------------------------------------------------------
-- Ready draining and task settlements
-----------------------------------------------------------------------------------------

theorem ParentCutFrame.taskFailure {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (errors : Nat)
    : ParentCutFrame (queue.taskFailure occurrence errors).1 work parents := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using frame
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves (fun current => ParentCutFrame current work parents)
        (fun _ ref prior => prior.removeGroup generated canonical ref) _ _ _
        ⟨frame.safe, frame.keys, frame.records, frame.links, frame.children, frame.live,
          frame.tasks, frame.closed, frame.fields, frame.complete, frame.cancelled,
          frame.registration.putTaskNode _ (frame.registration.started node
            (List.mem_of_find?_eq_some found))⟩

theorem ParentCutFrame.drainReadyGroups {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    : ParentCutFrame (queue.drainReadyGroups available).1 work parents := by
  exact State.drainReadyGroups_preserves (fun queue => ParentCutFrame queue work parents)
    (fun _ group prior _ _ _ =>
      (prior.finishGroupSuccess group).startNewWork generated canonical _ available) frame

theorem ParentCutFrame.taskSuccess {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ParentCutFrame (queue.taskSuccess occurrence result available).1 work parents := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using frame
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
      have storedFrame : ParentCutFrame stored work parents :=
        ⟨frame.safe, frame.keys, frame.records, frame.links, frame.children, frame.live,
          frame.tasks, frame.closed, frame.fields, frame.complete, frame.cancelled,
          frame.registration.putTaskNode _ (frame.registration.started node
            (List.mem_of_find?_eq_some found))⟩
      have certificate := (frame.registration.children node.task
        (frame.registration.started node (List.mem_of_find?_eq_some found))).sourceChild
          (State.taskNode?_some found).2 matching
      have integrated := storedFrame.maybeIntegrateWork result.work
        (fun _ member => matching.taskChildGroups_recordAt member)
        (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
        certificate (some occurrence) generated canonical
      have loop (groups : List Execution.DeliveryNode)
          (acc : State × List WorkQueueEvent × NewWork)
          (frame : ParentCutFrame acc.1 work parents)
          : ParentCutFrame (groups.foldl successGroupStep acc).1 work parents := by
        induction groups generalizing acc with
        | nil => exact frame
        | cons group rest ih =>
            apply ih
            dsimp only [successGroupStep]
            split
            · exact frame
            · rename_i groupNode lookup
              have updated := frame.putGroupNode lookup
                { groupNode with pending := groupNode.pending - 1 } rfl rfl
              split
              · exact updated.finishGroupSuccess _
              · exact updated
      exact ((loop node.task.groups (_, [], {}) integrated).startNewWork generated
              canonical _ available)
      |>.drainReadyGroups generated canonical available

-----------------------------------------------------------------------------------------
-- Stream receipts and actual graph-event replay
-----------------------------------------------------------------------------------------

theorem ParentCutFrame.integrateStreamItem {queue work parents stream items}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (available : List (Occurrence × Nat) := [])
    : ParentCutFrame (queue.integrateStreamItem item available) work parents := by
  have integrated := frame.maybeIntegrateWork item.work
    (fun _ group => matching.streamItem_childGroups_recordAt member group)
    (fun _ group => matching.streamItem_childGroups_parentCanonical canonical member group)
    (generated.declarations.sourceStreamItem matching member queue.registeredGroups)
    none generated canonical
  exact (integrated.pruneEmptyGroups _).startNewWork generated canonical _ available

theorem ParentCutFrame.streamItems {queue work parents stream items}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ParentCutFrame (queue.streamItems stream items available).1 work parents := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact frame
  · have prepared := State.preparedStreamItems_preserves
      (fun queue => ParentCutFrame queue work parents) frame items available
      (fun current item member frame =>
        frame.integrateStreamItem generated canonical matching member available)
    exact prepared.drainReadyGroups generated canonical available

theorem ParentCutFrame.handleGraphEvent {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ParentCutFrame (queue.handleGraphEvent event available).1 work parents := by
  have cached := frame.cacheTaskFailures available
  simp only [State.handleGraphEvent]
  cases event with
  | taskSuccess occurrence result =>
      exact cached.taskSuccess generated canonical matching available
  | taskFailure occurrence errors =>
      exact cached.taskFailure generated canonical occurrence errors
  | streamItems stream items =>
      exact cached.streamItems generated canonical matching available
  | streamSuccess stream =>
      change ParentCutFrame
        ((queue.cacheTaskFailures available).streamSuccess stream).1 work parents
      unfold State.streamSuccess
      split <;> exact ⟨cached.safe, cached.keys, cached.records, cached.links, cached.children,
        cached.live, cached.tasks, cached.closed, cached.fields, cached.complete,
        cached.cancelled, ⟨cached.registration.source, cached.registration.live,
          cached.registration.tasks, cached.registration.children, cached.registration.started⟩⟩
  | streamFailure stream errors =>
      change ParentCutFrame
        ((queue.cacheTaskFailures available).streamFailure stream errors).1 work parents
      unfold State.streamFailure
      split <;> exact ⟨cached.safe, cached.keys, cached.records, cached.links, cached.children,
        cached.live, cached.tasks, cached.closed, cached.fields, cached.complete,
        cached.cancelled, ⟨cached.registration.source, cached.registration.live,
          cached.registration.tasks, cached.registration.children, cached.registration.started⟩⟩
  | groupFailure notice =>
      change ParentCutFrame ((queue.cacheTaskFailures available).groupFailure notice).1 work parents
      unfold State.groupFailure
      split
      · exact cached
      · split
        · exact ⟨cached.safe, cached.keys, cached.records, cached.links, cached.children,
            cached.live, cached.tasks, cached.closed, cached.fields, cached.complete,
            cached.cancelled, cached.registration.withGroupFailures _⟩
        · exact cached

/-- Realized enqueue effects retain every structural frame field. -/
theorem ParentCutFrame.dispatchGraphEvent {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ParentCutFrame (queue.dispatchGraphEvent event available).1 work parents := by
  have next := frame.handleGraphEvent generated canonical event matching available
  exact ⟨next.safe, next.keys, next.records, next.links, next.children, next.live,
    next.tasks, next.closed, next.fields, next.complete, next.cancelled,
    next.registration.withGroupFailures _⟩

theorem ParentCutFrame.replayGraphEvents {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ParentCutFrame (queue.replayGraphEvents events available) work parents := by
  induction events generalizing queue with
  | nil => exact frame
  | cons event rest ih =>
      exact ih (frame.dispatchGraphEvent generated canonical event
        (matching event List.mem_cons_self) available)
        (fun next member => matching next (List.mem_cons_of_mem _ member))

theorem ParentCutFrame.handleGraphEvents {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : ParentCutFrame (queue.handleGraphEvents events).1 work parents := by
  by_cases ended : queue.terminated = true
  · simpa only [State.handleGraphEvents, ended, ite_true] using frame
  · have running : queue.terminated = false := Bool.eq_false_iff.mpr ended
    obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
    have replayed := frame.replayGraphEvents generated canonical events matching
      (GraphEvent.availableFailures events)
    rw [same]
    exact ⟨replayed.safe, replayed.keys, replayed.records, replayed.links, replayed.children,
      replayed.live, replayed.tasks, replayed.closed, replayed.fields, replayed.complete,
      replayed.cancelled, replayed.registration.withTerminated _⟩

-----------------------------------------------------------------------------------------
-- Initialization and generated normalized replay discharge the complete frame
-----------------------------------------------------------------------------------------

set_option maxHeartbeats 800000 in
theorem initial_parentCutFrame {work : Execution.Work} {parents : Nat → NodeRefs}
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : ParentCutFrame (State.initialize (Work.fromExecution work)) work parents := by
  rw [State.initialize_empty_eq_activation]
  have empty : ParentCutFrame {} work parents := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro node member; cases member
    · simp [State.GroupRefsUnique]
    · intro node member; cases member
    · intro node member; cases member
    · intro node member; cases member
    · intro node member; cases member
    · intro task member; cases member
    · intro ref member; cases member
    · intro node member; cases member
    · intro child member; cases member
    · intro ref member; cases member
    · refine ⟨generated.declarations, ?_, ?_, ?_, ?_⟩ <;>
        intro node member <;> cases member
  have integrated := empty.maybeIntegrateWork (Work.fromExecution work)
    (fun _ member => (workFromSpec_groups_recordAt_root member).imp
      (fun _ record => record.1))
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)
    (generated.declarations.lower (Located.root (root := work))) none generated canonical
  let initial := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  let pruned := initial.1.pruneEmptyGroups initial.2.newGroups
  let released : NewWork := { initial.2 with newGroups := pruned.2 }
  have finished := (integrated.pruneEmptyGroups initial.2.newGroups).startNewWork
    generated canonical released
  exact ⟨
    finished.safe,
    finished.keys,
    finished.records,
    finished.links,
    finished.children,
    finished.live,
    finished.tasks,
    finished.closed,
    finished.fields,
    finished.complete,
    finished.cancelled,
    finished.registration.withInitialNotices _ _
  ⟩

/-- Every live parent remains uncancelled throughout matched generated replay.
Witness: the same complete frame follows each raw handler without choosing batch boundaries.
-/
theorem ExecutedWork.replayGraphEvents_liveParentsUncancelled {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).LiveParentsUncancelled := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  exact ((initial_parentCutFrame generated canonical).replayGraphEvents generated canonical
    events matching).safe

/-- Every live parent remains uncancelled throughout matched generated replay.
The actual registration, settlement, draining, and terminal branches derive this invariant;
no safe-cut premise or stronger source admission is assumed. Start discipline is unnecessary.
-/
theorem ExecutedWork.runNormalized_liveParentsUncancelled {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.LiveParentsUncancelled := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have loop (more : List (List GraphEvent)) (included : more.Subset batches)
      (current : State) (frame : ParentCutFrame current work parents)
      : ParentCutFrame
          (more.foldl (fun next batch => (next.handleGraphEvents batch).1) current)
          work parents := by
    induction more generalizing current with
    | nil => exact frame
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (frame.handleGraphEvents generated canonical batch (fun _ member => valid.eachMatches
            (List.mem_flatten.mpr ⟨batch, included List.mem_cons_self, member⟩)))
  rw [State.runNormalized_stateFold]
  exact (loop batches (List.Subset.refl _) _
          (initial_parentCutFrame generated canonical)).safe

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
