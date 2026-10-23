import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchedNoticeHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupSupportReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementReplay

/-! Generated active roots form a duplicate-free antichain in the stored group forest.
These facts justify the fixed-snapshot stop traversal, not the shrinking failure walk.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Active roots are an ordered sublist of actual announcements
-----------------------------------------------------------------------------------------

private theorem rootSublist_append {initial : NodeRefs}
    {first second : State × List Execution.WorkQueueEvent}
    (before : first.1.rootGroups.Sublist (initial ++ first.2.flatMap rawGroupNoticeRefs))
    (after
      : second.1.rootGroups.Sublist
          (first.1.rootGroups ++ second.2.flatMap rawGroupNoticeRefs))
    : second.1.rootGroups.Sublist
        (initial ++ (first.2 ++ second.2).flatMap rawGroupNoticeRefs) := by
  rw [List.flatMap_append, ← List.append_assoc]
  exact after.trans (before.append (List.Sublist.refl _))

private theorem finishSuccess_rootSublist (queue : State) (node : GroupNode)
    (available : List (Occurrence × Nat))
    : ((queue.finishGroupSuccess node).1.startNewWork
        (queue.finishGroupSuccess node).2.2 available).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.finishGroupSuccess node).2.1.flatMap rawGroupNoticeRefs) := by
  have roots := ((queue.finishGroupSuccess node).1.startNewWork_groupCore
    (queue.finishGroupSuccess node).2.2 available).2.2
  rw [queue.finishGroupSuccess_groupNotices, queue.finishGroupSuccess_rootGroups] at roots
  exact roots.trans (List.filter_sublist.append (List.Sublist.refl _))

private theorem taskFailure_rootSublist (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.rootGroups.Sublist queue.rootGroups := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List Execution.WorkQueueEvent)
      (roots : acc.1.rootGroups.Sublist queue.rootGroups)
      : (groups.foldl (failureGroupStep errors) acc).1.rootGroups.Sublist queue.rootGroups := by
    induction groups generalizing acc with
    | nil => exact roots
    | cons group rest ih =>
        apply ih
        dsimp only [failureGroupStep]
        split
        · exact roots
        · split
          · exact List.filter_sublist.trans roots
          · exact roots
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found]
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact loop _ _ (List.Sublist.refl _)

private theorem drain_rootSublist (queue : State) (fuel : Nat)
    (available : List (Occurrence × Nat))
    : (State.drainReadyGroups.go available fuel queue).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (State.drainReadyGroups.go available fuel queue).2.1.flatMap
              rawGroupNoticeRefs) := by
  induction fuel generalizing queue with
  | zero => simp [State.drainReadyGroups.go]
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · simp
      · rename_i node selected
        let released := queue.finishGroupSuccess node
        let active := (released.1.startNewWork released.2.2 available).1
        exact rootSublist_append (first := (active, released.2.1))
          (second := ((State.drainReadyGroups.go available fuel active).1,
            (State.drainReadyGroups.go available fuel active).2.1))
          (finishSuccess_rootSublist queue node available) (ih active)

private theorem taskSuccess_rootSublist (queue : State) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat))
    : (queue.taskSuccess occurrence result available).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.taskSuccess occurrence result available).2.1.flatMap
              rawGroupNoticeRefs) := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode {node with value := some result.value}
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let folded := node.task.groups.foldl successGroupStep (prepared, [], {})
      have loop (groups : List Execution.DeliveryNode)
          (acc : State × List Execution.WorkQueueEvent × NewWork)
          (roots : acc.1.rootGroups.Sublist prepared.rootGroups)
          : (groups.foldl successGroupStep acc).1.rootGroups.Sublist prepared.rootGroups := by
        induction groups generalizing acc with
        | nil => exact roots
        | cons group rest ih =>
            apply ih
            dsimp only [successGroupStep]
            split
            · exact roots
            · split
              · rw [State.finishGroupSuccess_rootGroups]
                exact List.filter_sublist.trans roots
              · exact roots
      have roots := loop node.task.groups (prepared, [], {}) (List.Sublist.refl _)
      have notices := successGroupFold_groupNotices prepared node.task.groups
      have initial : prepared.rootGroups = queue.rootGroups :=
        State.maybeIntegrateWork_rootGroups _ _ _
      have first : (folded.1.startNewWork folded.2.2 available).1.rootGroups.Sublist
          (queue.rootGroups ++ folded.2.1.flatMap rawGroupNoticeRefs) := by
        have included := (folded.1.startNewWork_groupCore folded.2.2 available).2.2
        rw [notices] at included
        rw [initial] at roots
        exact included.trans (roots.append (List.Sublist.refl _))
      exact rootSublist_append
        (first := ((folded.1.startNewWork folded.2.2 available).1, folded.2.1))
        (second :=
          (
            ((folded.1.startNewWork folded.2.2 available).1.drainReadyGroups available).1,
            ((folded.1.startNewWork folded.2.2 available).1.drainReadyGroups
              available).2.1
          ))
        first (drain_rootSublist _ _ available)

private theorem itemFold_rootSublist (queue : State) (items : List StreamItem)
    (available : List (Occurrence × Nat))
    : let prepared :=
        items.foldl (fun acc item => streamItemStep acc item available)
          (queue, [], [], [], [])
      prepared.1.rootGroups.Sublist
        (queue.rootGroups ++ prepared.2.1.map Execution.DeliveryNode.ref) := by
  have loop (more : List StreamItem)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode ×
        List Execution.StreamItemValue × List GroupFailureEvent)
      (included : acc.1.rootGroups.Sublist
        (queue.rootGroups ++ acc.2.1.map Execution.DeliveryNode.ref))
      : (more.foldl (fun acc item => streamItemStep acc item available) acc).1.rootGroups.Sublist
        (queue.rootGroups ++ (more.foldl (fun acc item => streamItemStep acc item available)
          acc).2.1.map Execution.DeliveryNode.ref) := by
    induction more generalizing acc with
    | nil => exact included
    | cons item rest ih =>
        apply ih
        have starts := (((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
          (acc.1.maybeIntegrateWork item.work).2.newGroups).1.startNewWork_groupCore
            { (acc.1.maybeIntegrateWork item.work).2 with newGroups :=
              ((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
                (acc.1.maybeIntegrateWork item.work).2.newGroups).2 } available).2.2
        simp only [streamItemStep, State.pruneEmptyGroups_rootGroups,
          State.maybeIntegrateWork_rootGroups] at starts ⊢
        rw [List.map_append, ← List.append_assoc]
        exact starts.trans (included.append (List.Sublist.refl _))
  exact loop items (queue, [], [], [], []) (by simp)

private theorem streamItems_rootSublist (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat))
    : (queue.streamItems stream items available).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.streamItems stream items available).2.1.flatMap
              rawGroupNoticeRefs) := by
  rw [queue.streamItems_eq stream items available]
  split
  · simp
  · let prepared := items.foldl (fun acc item => streamItemStep acc item available)
      (queue, [], [], [], [])
    exact rootSublist_append (first := (prepared.1,
      [.streamValues stream prepared.2.2.2.1 prepared.2.1 prepared.2.2.1]))
        (second := ((prepared.1.drainReadyGroups available).1,
          (prepared.1.drainReadyGroups available).2.1))
        (by simpa only [List.flatMap_singleton, rawGroupNoticeRefs]
          using itemFold_rootSublist queue items available) (drain_rootSublist _ _ available)

private theorem handleGraphEvent_rootSublist (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.handleGraphEvent event available).2.1.flatMap
              rawGroupNoticeRefs) := by
  let current := queue.cacheTaskFailures available
  rw [← queue.cacheTaskFailures_rootGroups available]
  cases event with
  | taskSuccess occurrence result =>
      exact taskSuccess_rootSublist current occurrence result available
  | taskFailure occurrence errors =>
      rw [State.handleGraphEvent, current.taskFailure_groupNoticeRefs, List.append_nil]
      exact taskFailure_rootSublist current occurrence errors
  | streamItems stream items =>
      exact streamItems_rootSublist current stream items available
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [rawGroupNoticeRefs]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [rawGroupNoticeRefs]

  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · simp
      · split <;> simp [rawGroupNoticeRefs]

/-- Root filtering and activation preserve multiplicities from actual FIFO notices. -/
theorem State.rawEventReplay_rootGroups_sublist (queue : State) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.rawEventReplay events available).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.rawEventReplay events available).2.flatMap rawGroupNoticeRefs) := by
  induction events generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      rw [State.rawEventReplay_cons queue event rest available]
      exact rootSublist_append
        (first := queue.dispatchGraphEvent event available)
        (second := (queue.dispatchGraphEvent event available).1.rawEventReplay rest available)
        (handleGraphEvent_rootSublist queue event available) (ih _)

private theorem handleGraphEvents_rootSublist (queue : State) (batch : List GraphEvent)
    : (queue.handleGraphEvents batch).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.handleGraphEvents batch).2.flatMap rawGroupNoticeRefs) := by
  cases running : queue.terminated with
  | true => simp only [State.handleGraphEvents, running, ↓reduceIte, List.flatMap_nil,
      List.append_nil]; exact List.Sublist.refl _
  | false =>
      have roots := queue.rawEventReplay_rootGroups_sublist batch
        (GraphEvent.availableFailures batch)
      rw [State.rawEventReplay_state _ batch (GraphEvent.availableFailures batch)] at roots
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore batch running
      rw [same, queue.handleGraphEvents_groupNoticeRefs batch running]
      exact roots

/-- Actual host batches retain active roots as a sublist of their complete notice inventory. -/
theorem State.rawBatches_rootGroups_sublist (queue : State)
    (batches : List (List GraphEvent))
    : (queue.rawBatches batches).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.rawBatches batches).2.flatMap rawGroupNoticeRefs) := by
  induction batches generalizing queue with
  | nil => simp [State.rawBatches]
  | cons batch rest ih =>
      exact rootSublist_append (handleGraphEvents_rootSublist queue batch) (ih _)

/-- Generated actual batch replay has no repeated active group root. -/
theorem ExecutedWork.runNormalized_rootGroups_nodup {work : Execution.Work}
    (generated : ExecutedWork work) (inputs : List (List GraphEvent))
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.rootGroups.Nodup := by
  have history := generated.rawBatches_groupRefs_nodup valid started
  have roots := (State.initialize (Work.fromExecution work)).rawBatches_rootGroups_sublist inputs
  rw [State.rawBatches_state] at roots
  rw [State.runNormalized_replayBatches]
  exact history.sublist roots

-----------------------------------------------------------------------------------------
-- Supported roots cannot lie below another protected active root
-----------------------------------------------------------------------------------------

/-- The live group forest has pairwise non-overlapping active roots.
This says nothing about whether every live group is reachable from one of those roots.
-/
def State.RootAntichain (queue : State) : Prop :=
  ∀ root ∈ queue.rootGroups,
  ∀ target ∈ queue.rootGroups, queue.LiveDescendant root target → root = target

/-- A protected root cannot have another supported root above it.
Witness: generated support supplies an actual contributor; a nontrivial path would make
that live contributor a permanently retired ancestor, contradicting its lookup.
-/
theorem State.RootAncestorsRetired.rootAntichain {queue : State} {work parents}
    (roots : queue.RootAncestorsRetired work) (generated : ExecutedWork work)
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (support
      : queue.GroupRefSupport
          (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies))
    : queue.RootAntichain := by
  intro root active target atTarget path
  obtain ⟨dependencies, node, producer, known, same⟩ := support.roots root active
  obtain ⟨occurrence, owners, payload, task, contributes⟩ := known.group_task
  exact (roots target atTarget).supported_path_eq generated records links canonical path
    ⟨producer, payload, task⟩ (same ▸ contributes)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- The exact alternative replay derives both stop-root topology obligations
-----------------------------------------------------------------------------------------

/-- Generated legal started replay gives duplicate-free, non-overlapping active roots.
The source contract is unchanged; this is derived topology, not supplied host evidence.
-/
def GeneratedStopRootTopology : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → let queue := ((State.initialize work).runNormalized inputs).1.queue
      queue.rootGroups.Nodup ∧ queue.RootAntichain

/-- Reference announcement and retired-ancestry proofs apply to the actual projected state.
Terminal retirement has no roots; nonterminal replay uses generated canonical metadata.
-/
theorem GeneratedStopRootTopology_holds : GeneratedStopRootTopology := by
  intro work inputs generated valid started
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · exact ⟨List.nodup_nil, by intro key member; cases member⟩
  · obtain ⟨parents, canonical, links, records⟩ := generated.runNormalized_groupMetadata valid
    have roots := (generated.runNormalized_structuralRetirement inputs
      (fun batch member event within => valid.eachMatches
        (List.mem_flatten.mpr ⟨batch, member, within⟩))).1
    exact ⟨generated.runNormalized_rootGroups_nodup inputs valid started,
      roots.rootAntichain generated records links canonical
        (ReferenceWorkQueue.createWorkQueue_runNormalized_groupRefSupport valid)⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
