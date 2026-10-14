import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ParentCutsTransitions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain

/-! Derive live-parent safety from actual generated queue execution. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Shared structural evidence follows the same concrete accumulator
-----------------------------------------------------------------------------------------

private structure ParentCutFrame (queue : State) (work : Execution.Work)
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

private theorem ParentCutFrame.removeTask {queue work parents}
    (frame : ParentCutFrame queue work parents) (occurrence : Occurrence)
    : ParentCutFrame (queue.removeTask occurrence) work parents := by
  refine ⟨frame.safe.removeTask _, frame.keys.removeTask _, frame.records.removeTask _,
    frame.links.removeTask _, frame.children.removeTask _, ?_, frame.tasks,
    frame.closed, frame.fields.removeTask _, frame.complete.removeTask _⟩
  intro node member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact frame.live old oldMember

private theorem ParentCutFrame.putGroupNode {queue work parents key node}
    (frame : ParentCutFrame queue work parents) (found : queue.groupNode? key = some node)
    (updated : GroupNode) (sameGroup : updated.group = node.group)
    (sameChildren : updated.childGroups = node.childGroups)
    : ParentCutFrame (queue.putGroupNode updated) work parents := by
  have member := List.mem_of_find?_eq_some found
  refine ⟨frame.safe.putGroupNode _ ?_, frame.keys.putGroupNode _,
    frame.records.putGroupNode _ ?_, frame.links.putGroupNode _ ?_,
    frame.children.putGroupNode _ ?_, frame.live.putGroupNode _ ?_, frame.tasks,
    frame.closed, frame.fields.putGroupNode _ ?_,
    frame.complete.putGroupNode frame.keys found _ ?_ ?_⟩
  · simpa only [sameGroup] using frame.safe node member
  · simpa only [sameGroup] using frame.records node member
  · simpa only [sameGroup, sameChildren] using frame.links node member
  · simpa only [sameChildren] using frame.children node member
  · simpa only [sameGroup] using frame.live node member
  · simpa only [sameGroup] using frame.fields node member
  · rw [sameGroup]
  · rw [sameChildren]; exact List.Subset.refl _

private theorem ParentCutFrame.pruneEmptyGroups {queue work parents}
    (frame : ParentCutFrame queue work parents) (groups : List Execution.DeliveryNode)
    : ParentCutFrame (queue.pruneEmptyGroups groups).1 work parents := by
  have registered := queue.pruneEmptyGroups_registration frame.live frame.tasks groups
  exact ⟨frame.safe.pruneEmptyGroups _, frame.keys.pruneEmptyGroups _,
    frame.records.pruneEmptyGroups _, frame.links.pruneEmptyGroups _,
    frame.children.pruneEmptyGroups _, registered.1, registered.2.1,
    frame.closed.of_sameRegistry registered.2.2, frame.fields.pruneEmptyGroups _,
    frame.complete.pruneEmptyGroups _⟩

private theorem ParentCutFrame.startNewWork {queue work parents}
    (frame : ParentCutFrame queue work parents) (released : NewWork)
    : ParentCutFrame (queue.startNewWork released) work parents := by
  have registered := State.startNewWork_registration frame.live frame.tasks released
  exact ⟨frame.safe.startNewWork _, frame.keys.startNewWork _, frame.records.startNewWork _,
    frame.links.startNewWork _, frame.children.startNewWork _, registered.1, registered.2,
    frame.closed.of_sameRegistry (queue.startNewWork_registeredGroups released),
    frame.fields.startNewWork _, frame.complete.startNewWork _⟩

private theorem ParentCutFrame.finishGroupSuccess {queue work parents}
    (frame : ParentCutFrame queue work parents) (group : GroupNode)
    : ParentCutFrame (queue.finishGroupSuccess group).1 work parents := by
  have registered := queue.finishGroupSuccess_registration frame.live frame.tasks group
  exact ⟨frame.safe.finishGroupSuccess _, frame.keys.finishGroupSuccess _,
    frame.records.finishGroupSuccess _, frame.links.finishGroupSuccess _,
    frame.children.finishGroupSuccess _, registered.1, registered.2.1,
    frame.closed.of_sameRegistry registered.2.2, frame.fields.finishGroupSuccess _,
    frame.complete.finishGroupSuccess _⟩

private theorem ParentCutFrame.removeGroup {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (root : Nat)
    : ParentCutFrame (queue.removeGroup root) work parents := by
  have forest := State.RemovalForest.of_generated generated frame.children frame.links
    frame.records canonical
  exact ⟨frame.safe.removeGroup frame.keys frame.fields frame.complete forest root,
    frame.keys.removeGroup _, frame.records.removeGroup _, frame.links.removeGroup _,
    frame.children.removeGroup _, fun node member => frame.live node (List.mem_filter.mp member).1,
    frame.tasks, frame.closed, frame.fields.removeGroup _, frame.complete.removeGroup _⟩

private theorem ParentCutFrame.maybeIntegrateWork {queue work parents}
    (frame : ParentCutFrame queue work parents) (newWork : Work)
    (known
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (fields : ∀ group ∈ newWork.groups, group.parent = (parents group.node.ref).head?)
    (covered
      : ∀ task ∈ newWork.tasks,
        ∀ key ∈ task.groups.map Execution.DeliveryNode.ref,
          ∃ group ∈ newWork.groups, group.node.ref = key)
    (parentsCovered : newWork.ParentsCovered) (ordered : ParentsBefore [] newWork.groups)
    (parentTask : Option Occurrence := none)
    : ParentCutFrame (queue.maybeIntegrateWork newWork parentTask).1 work parents := by
  have registered := queue.maybeIntegrateWork_registration frame.live frame.tasks
    newWork covered parentTask
  exact ⟨frame.safe.maybeIntegrateWork frame.live frame.closed frame.fields _ fields ordered _,
    frame.keys.maybeIntegrateWork _ _, frame.records.maybeIntegrateWork _ known _,
    frame.links.maybeIntegrateWork _ fields _, frame.children.maybeIntegrateWork _ _,
    registered.1, registered.2.1,
    frame.closed.maybeIntegrateWork frame.live _ fields parentsCovered _,
    frame.fields.maybeIntegrateWork _ fields _,
    frame.complete.maybeIntegrateWork frame.keys frame.live frame.closed _ fields _⟩

-----------------------------------------------------------------------------------------
-- Ready draining and task settlements
-----------------------------------------------------------------------------------------

private theorem ParentCutFrame.drainReadyGroups {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : ParentCutFrame queue.drainReadyGroups.1 work parents := by
  apply State.drainReadyGroups_preserves (fun queue => ParentCutFrame queue work parents)
    (fun queue group frame _ _ _ _ => (frame.finishGroupSuccess group).startNewWork _)
    (fun queue group errors frame _ _ _ => frame.removeGroup generated canonical _) frame

private theorem ParentCutFrame.taskFailure {queue work parents}
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
      split
      · exact frame.removeTask occurrence
      · have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
            (frame : ParentCutFrame acc.1 work parents)
            : ParentCutFrame (groups.foldl (failureGroupStep errors) acc).1 work parents := by
          induction groups generalizing acc with
          | nil => exact frame
          | cons group rest ih =>
              apply ih
              dsimp only [failureGroupStep]
              split
              · exact frame
              · rename_i groupNode lookup
                split
                · exact frame.removeGroup generated canonical _
                · exact frame.putGroupNode lookup _ rfl rfl
        exact loop node.task.groups (queue.removeTask occurrence, [])
          (frame.removeTask occurrence)

private theorem ParentCutFrame.taskSuccess {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : ParentCutFrame (queue.taskSuccess occurrence result).1 work parents := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using frame
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact frame.removeTask occurrence
      · let stored := queue.putTaskNode { node with value := some result.value }
        have storedFrame : ParentCutFrame stored work parents :=
          ⟨frame.safe, frame.keys, frame.records, frame.links, frame.children, frame.live,
            frame.tasks, frame.closed, frame.fields, frame.complete⟩
        have integrated := storedFrame.maybeIntegrateWork result.work
          (fun _ member => matching.taskChildGroups_recordAt member)
          (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
          matching.childTasksCovered matching.childParentsCovered matching.childParentsBefore
          (some occurrence)
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
        exact ((loop node.task.groups (_, [], {}) integrated).startNewWork _)
          |>.drainReadyGroups generated canonical

-----------------------------------------------------------------------------------------
-- Stream receipts and actual graph-event replay
-----------------------------------------------------------------------------------------

private theorem ParentCutFrame.integrateStreamItem {queue work parents stream items}
    (frame : ParentCutFrame queue work parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : ParentCutFrame (queue.integrateStreamItem item) work parents := by
  have integrated := frame.maybeIntegrateWork item.work
    (fun _ group => matching.streamItem_childGroups_recordAt member group)
    (fun _ group => matching.streamItem_childGroups_parentCanonical canonical member group)
    (matching.streamItem_childTasksCovered member)
    (matching.streamItem_parentsCovered member) (matching.streamItem_parentsBefore member)
  exact (integrated.pruneEmptyGroups _).startNewWork _

private theorem ParentCutFrame.streamItems {queue work parents stream items}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : ParentCutFrame (queue.streamItems stream items).1 work parents := by
  rw [queue.streamItems_eq stream items]
  split
  · exact frame
  · have prepared := State.preparedStreamItems_preserves
      (fun queue => ParentCutFrame queue work parents) frame items
      (fun current item member frame => frame.integrateStreamItem canonical matching member)
    exact prepared.drainReadyGroups generated canonical

private theorem ParentCutFrame.handleGraphEvent {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : ParentCutFrame (queue.handleGraphEvent event).1 work parents := by
  cases event with
  | taskSuccess occurrence result => exact frame.taskSuccess generated canonical matching
  | taskFailure occurrence errors =>
      exact frame.taskFailure generated canonical occurrence errors
  | streamItems stream items => exact frame.streamItems generated canonical matching
  | streamSuccess stream =>
      change ParentCutFrame (queue.streamSuccess stream).1 work parents
      unfold State.streamSuccess
      split <;> exact ⟨frame.safe, frame.keys, frame.records, frame.links, frame.children,
        frame.live, frame.tasks, frame.closed, frame.fields, frame.complete⟩
  | streamFailure stream errors =>
      change ParentCutFrame (queue.streamFailure stream errors).1 work parents
      unfold State.streamFailure
      split <;> exact ⟨frame.safe, frame.keys, frame.records, frame.links, frame.children,
        frame.live, frame.tasks, frame.closed, frame.fields, frame.complete⟩

private theorem ParentCutFrame.replayGraphEvents {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : ParentCutFrame (queue.replayGraphEvents events) work parents := by
  induction events generalizing queue with
  | nil => exact frame
  | cons event rest ih =>
      exact ih (frame.handleGraphEvent generated canonical event
        (matching event List.mem_cons_self))
        (fun next member => matching next (List.mem_cons_of_mem _ member))

private theorem ParentCutFrame.handleGraphEvents {queue work parents}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : ParentCutFrame (queue.handleGraphEvents events).1 work parents := by
  unfold State.handleGraphEvents
  split
  · exact frame
  · have replayed := frame.replayGraphEvents generated canonical events matching
    dsimp only
    rw [State.foldGraphEvents_state]
    split
    · exact ⟨replayed.safe, replayed.keys, replayed.records, replayed.links, replayed.children,
        replayed.live, replayed.tasks, replayed.closed, replayed.fields, replayed.complete⟩
    · exact replayed

-----------------------------------------------------------------------------------------
-- Initialization and generated normalized replay discharge the complete frame
-----------------------------------------------------------------------------------------

private theorem initial_parentCutFrame {work : Execution.Work} {parents : Nat → NodeRefs}
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : ParentCutFrame (State.initialize (Work.fromExecution work)) work parents := by
  have empty : ParentCutFrame {} work parents := by
    constructor <;> simp [State.LiveParentsUncancelled, State.GroupRefsUnique,
      State.GroupNodesMatchWork, State.ChildLinksCanonical, State.ChildGroupsUnique,
      State.LiveGroupsRegistered, State.TaskGroupsRegistered, State.ParentRegistryClosed,
      State.GroupParentsCanonical, State.ParentLinksComplete]
  have integrated := empty.maybeIntegrateWork (Work.fromExecution work)
    (fun _ member => (workFromSpec_groups_recordAt (Located.root (root := work)) member).imp
      (fun _ record => record.1))
    (fun _ member => workFromSpec_groups_parentCanonical
      (Located.root (root := work)) canonical member)
    (workFromSpec_immediateGroupsCoverTasks work []) (workFromSpec_parentsCovered work)
    (workFromExecution_parentsBefore work)
  let initial := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  let pruned := initial.1.pruneEmptyGroups initial.2.newGroups
  let released : NewWork := { initial.2 with newGroups := pruned.2 }
  have finished := (integrated.pruneEmptyGroups initial.2.newGroups).startNewWork released
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
    finished.complete
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
  exact ((initial_parentCutFrame canonical).replayGraphEvents generated canonical
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
          (more.foldl (fun next batch => (next.handleGraphEvents batch).1) current) work parents := by
    induction more generalizing current with
    | nil => exact frame
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (frame.handleGraphEvents generated canonical batch (fun _ member => valid.eachMatches
            (List.mem_flatten.mpr ⟨batch, included List.mem_cons_self, member⟩)))
  rw [State.runNormalized_stateFold]
  exact (loop batches (List.Subset.refl _) _ (initial_parentCutFrame canonical)).safe

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
