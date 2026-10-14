import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeUniqueness
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
    : ((queue.finishGroupSuccess node).1.startNewWork
        (queue.finishGroupSuccess node).2.2).rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.finishGroupSuccess node).2.1.flatMap rawGroupNoticeRefs) := by
  rw [((queue.finishGroupSuccess node).1.startNewWork_groupCore _).2.2,
    queue.finishGroupSuccess_groupNotices, queue.finishGroupSuccess_rootGroups]
  exact List.filter_sublist.append (List.Sublist.refl _)

private theorem removeGroup_rootSublist (queue : State) (key : Nat)
    : (queue.removeGroup key).rootGroups.Sublist queue.rootGroups :=
  List.filter_sublist

private theorem drain_rootSublist (queue : State) (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (State.drainReadyGroups.go fuel queue).2.flatMap rawGroupNoticeRefs) := by
  induction fuel generalizing queue with
  | zero => simp [State.drainReadyGroups.go]
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · simp
      · rename_i node selected
        cases cached : node.failure with
        | none => exact rootSublist_append (finishSuccess_rootSublist queue node) (ih _)
        | some errors =>
            apply rootSublist_append (first := ((queue.finishGroupFailure node errors).1,
              [(queue.finishGroupFailure node errors).2])) _ (ih _)
            simpa only [State.finishGroupFailure, List.flatMap_singleton, rawGroupNoticeRefs,
              List.append_nil] using removeGroup_rootSublist queue node.group.node.ref

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
          · exact (removeGroup_rootSublist _ _).trans roots
          · exact roots
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found]
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      split
      · exact List.Sublist.refl _
      · exact loop _ _ (List.Sublist.refl _)

private theorem taskSuccess_rootSublist (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.taskSuccess occurrence result).2.flatMap rawGroupNoticeRefs) := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · simpa only [State.removeTask, List.flatMap_nil, List.append_nil]
          using List.Sublist.refl queue.rootGroups
      · let stored := queue.putTaskNode { node with value := some result.value }
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
        have first : (folded.1.startNewWork folded.2.2).rootGroups.Sublist
            (queue.rootGroups ++ folded.2.1.flatMap rawGroupNoticeRefs) := by
          rw [(folded.1.startNewWork_groupCore _).2.2, notices]
          rw [initial] at roots
          exact roots.append (List.Sublist.refl _)
        exact rootSublist_append
          (first := (folded.1.startNewWork folded.2.2, folded.2.1))
          first (drain_rootSublist _ _)

private theorem streamItems_rootSublist (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : (queue.streamItems stream items).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.streamItems stream items).2.flatMap rawGroupNoticeRefs) := by
  rw [queue.streamItems_eq stream items]
  split
  · simp
  · let prepared := items.foldl streamItemStep (queue, [], [], [])
    apply rootSublist_append (first := (prepared.1,
      [.streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1])) _
      (drain_rootSublist _ _)
    rw [queue.streamItemFold_rootGroups items]
    simp [prepared, rawGroupNoticeRefs]

private theorem handleGraphEvent_rootSublist (queue : State) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.handleGraphEvent event).2.flatMap rawGroupNoticeRefs) := by
  cases event with
  | taskSuccess occurrence result => exact taskSuccess_rootSublist queue occurrence result
  | taskFailure occurrence errors =>
      rw [State.handleGraphEvent, queue.taskFailure_groupNoticeRefs, List.append_nil]
      exact taskFailure_rootSublist queue occurrence errors
  | streamItems stream items => exact streamItems_rootSublist queue stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [rawGroupNoticeRefs]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [rawGroupNoticeRefs]

/-- Root filtering and activation preserve multiplicities from the actual notice history.
Unlike set inclusion, this ordered sublist fact can derive root-list uniqueness.
-/
theorem State.rawEventReplay_rootGroups_sublist (queue : State) (events : List GraphEvent)
    : (queue.rawEventReplay events).1.rootGroups.Sublist
        (queue.rootGroups
          ++ (queue.rawEventReplay events).2.flatMap rawGroupNoticeRefs) := by
  induction events generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      exact rootSublist_append (handleGraphEvent_rootSublist queue event) (ih _)

/-- Generated matching replay has no repeated active root, independently of output admission.
Witness: active roots are a sublist of globally unique actual group announcements.
-/
theorem ExecutedWork.runNormalized_rootGroups_nodup {work : Execution.Work}
    (generated : ExecutedWork work) (inputs : List (List GraphEvent))
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.rootGroups.Nodup := by
  have history := generated.rawEventReplay_groupRefs_nodup inputs.flatten
    (fun _ member => valid.eachMatches member)
  have roots := (State.initialize (Work.fromExecution work)).rawEventReplay_rootGroups_sublist
    inputs.flatten
  rw [State.rawEventReplay_state] at roots
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
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
