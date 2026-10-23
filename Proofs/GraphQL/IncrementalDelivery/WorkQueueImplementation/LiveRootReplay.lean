import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshGroupPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementReplay

/-! Live-root and retirement frames follow actual cache-aware handlers and batch replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics

private theorem notice_supported {work event ref}
    (known : Execution.WorkQueueEvent.GroupNoticesLocated work event)
    (noticed : ref ∈ rawGroupNoticeRefs event)
    : ∃ dependencies, NodeHasDependencies work ref .group dependencies := by
  have groups (nodes : List Execution.DeliveryNode)
      (located : ∀ node ∈ nodes,
        ∃ dependencies producer, NodeAt work node .group dependencies producer)
      (member : ref ∈ nodes.map Execution.DeliveryNode.ref)
      : ∃ dependencies, NodeHasDependencies work ref .group dependencies := by
    obtain ⟨node, member, same⟩ := List.mem_map.mp member
    obtain ⟨dependencies, producer, present⟩ := located node member
    exact ⟨dependencies, node, producer, present, same⟩
  cases event <;> simp only [rawGroupNoticeRefs] at noticed
  case groupSuccess group nodes streams => exact groups nodes known noticed
  case streamValues stream values nodes streams => exact groups nodes known noticed
  all_goals cases noticed

/-- Shared proof certificate combining live-root support with uncancelled retirement. -/
structure RootReplayFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs)
    : Prop where
  live : LiveRootFrame queue work parents
  retired : queue.UncancelledRetiredAncestors work

theorem RootReplayFrame.cacheTaskFailures {queue work parents}
    (frame : RootReplayFrame queue work parents) (available : List (Occurrence × Nat))
    : RootReplayFrame (queue.cacheTaskFailures available) work parents := by
  have registered := queue.cacheTaskFailures_registration frame.live.registered frame.live.tasks
    available
  refine ⟨⟨frame.live.refs.cacheTaskFailures _, frame.live.records.cacheTaskFailures _,
    frame.live.links.cacheTaskFailures _, registered.1, registered.2, ?_,
    frame.live.support.cacheTaskFailures _, ?_⟩, frame.retired.cacheTaskFailures _⟩
  · intro ref active
    rw [State.cacheTaskFailures_rootGroups] at active
    exact (frame.live.roots ref active).mono (fun _ retired => retired.cacheTaskFailures available)
  · intro ref active
    rw [State.cacheTaskFailures_rootGroups] at active
    rw [State.cacheTaskFailures_groupNodes]
    exact frame.live.present ref active

theorem RootReplayFrame.maybeIntegrateWork {queue work parents}
    (frame : RootReplayFrame queue work parents) (incoming : Work)
    (known
      : ∀ group ∈ incoming.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (fields : ∀ group ∈ incoming.groups, group.parent = (parents group.node.ref).head?)
    (covered
      : ∀ task ∈ incoming.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ref ∈ queue.registeredGroups ∨ ∃ group ∈ incoming.groups, group.node.ref = ref)
    (owners
      : ∀ task ∈ incoming.tasks,
        ∀ group ∈ task.groups,
          ∃ dependencies, NodeHasDependencies work group.ref .group dependencies)
    (producer : Option Occurrence := none)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (closed
      : ∀ group ∈ incoming.groups,
          ∀ parent,
            group.parent = some parent
            → parent
              ∈ queue.registeredGroups
                ++ incoming.groups.map (fun group => group.node.ref))
    : RootReplayFrame (queue.maybeIntegrateWork incoming producer).1 work parents := by
  have registered := queue.maybeIntegrateWork_registration frame.live.registered frame.live.tasks
    incoming covered producer
  refine ⟨
    ⟨
      frame.live.refs.maybeIntegrateWork _ _,
      frame.live.records.maybeIntegrateWork _ known _,
      frame.live.links.maybeIntegrateWork _ fields _,
      registered.1,
      registered.2.1,
      ?_,
      frame.live.support.maybeIntegrateWork _ owners _,
      frame.live.present.maybeIntegrateWork _ _
    ⟩,
    frame.retired.maybeIntegrateWork incoming producer generated frame.live.registered
      (by
        intro group member
        obtain ⟨dependencies, record⟩ := known group member
        exact ⟨
          dependencies,
          record,
          by rw [canonical _ _ record]; exact fields group member
        ⟩)
      closed
  ⟩
  exact frame.live.roots.mono
    (by rw [State.maybeIntegrateWork_rootGroups]; exact fun _ member => member)
    (fun _ retired => retired.maybeIntegrateWork incoming producer)

theorem RootReplayFrame.drainReadyGroups {queue work parents}
    (frame : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat))
    : RootReplayFrame (queue.drainReadyGroups available).1 work parents := by
  have retirement := queue.drainReadyGroups_uncancelledRetirement frame.retired generated
    frame.live.records frame.live.links canonical frame.live.registered frame.live.tasks
    frame.live.roots available
  exact ⟨frame.live.drainReadyGroups generated canonical available, retirement.2⟩

/-- The actual successful owner fold activates its protected releases with structural roots.
Witness: independent retirement, notice metadata and live-record results describe the same
concrete fold before startup; no failure-inventory or notification-consumption premise is used.
-/
theorem RootReplayFrame.successGroupFold_start {queue work parents}
    (frame : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (groups : List Execution.DeliveryNode) (available : List (Occurrence × Nat))
    : let folded := groups.foldl successGroupStep (queue, [], {})
      RootReplayFrame (folded.1.startNewWork folded.2.2 available).1 work parents := by
  let folded := groups.foldl successGroupStep (queue, [], {})
  have retirement := successGroupFold_uncancelledRetirement frame.retired generated
    frame.live.records frame.live.links canonical frame.live.registered
    frame.live.tasks frame.live.roots groups
  have metadata := State.successGroupFold_noticeMetadata generated frame.live.refs
    frame.live.records frame.live.support groups
  have presence := successGroupFold_supported_rootsPresent generated frame.live.refs
    frame.live.records frame.live.links canonical frame.live.registered
    frame.live.tasks frame.live.roots frame.live.support frame.live.present
    groups
  have ancestry := successGroupFold_ancestorsRetired generated frame.live.records
    frame.live.links canonical frame.live.registered frame.live.tasks
    frame.live.roots groups
  have foldedFrame : LiveRootFrame folded.1 work parents :=
    ⟨metadata.1, retirement.1, retirement.2.1, retirement.2.2.1, retirement.2.2.2.1,
      retirement.2.2.2.2.1, metadata.2.2, presence.1⟩
  have active : RootReplayFrame (folded.1.startNewWork folded.2.2 available).1 work parents :=
    ⟨foldedFrame.startNewWork _ ancestry.2
      (fun child member => (presence.2 child member).2.1)
      (fun child member => by
        have notices := (successGroupFold_groupNotices queue groups).symm
        have located := State.successGroupFold_groupNoticesLocated generated frame.live.refs
          frame.live.records frame.live.support groups
        have announced : child.ref ∈ folded.2.1.flatMap rawGroupNoticeRefs := by
          rw [notices]
          exact List.mem_map_of_mem member
        obtain ⟨event, emitted, mentioned⟩ := List.mem_flatMap.mp announced
        exact notice_supported (located event emitted) mentioned) available,
      retirement.2.2.2.2.2.startNewWork _ available⟩
  exact active

theorem RootReplayFrame.taskSuccess {queue work parents occurrence result}
    (frame : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat))
    : RootReplayFrame (queue.taskSuccess occurrence result available).1 work parents := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using frame
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
      have storedFrame : RootReplayFrame stored work parents :=
        ⟨⟨frame.live.refs, frame.live.records, frame.live.links, frame.live.registered,
          frame.live.tasks, frame.live.roots,
          ⟨frame.live.support.contents, frame.live.support.roots⟩, frame.live.present⟩,
          frame.retired⟩
      have supplied := (context.children node.task
        (context.started node (State.taskNode?_some found).1)).sourceChild
          (State.taskNode?_some found).2 matching
      have prepared := storedFrame.maybeIntegrateWork result.work
        (fun _ member => matching.taskChildGroups_recordAt member)
        (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
        supplied.contributors (by
          intro task member group contributes
          obtain ⟨address, payload, same, located⟩ := matching.childTask_producer member
          have taskKnown : TaskMatches work task :=
            ⟨⟨address, payload, some occurrence, same, located⟩,
              matching.childTask_groupsExact member⟩
          exact taskKnown.contributorKnown (List.mem_map_of_mem contributes))
        (some occurrence) generated canonical supplied.parentRefs
      exact (prepared.successGroupFold_start generated canonical node.task.groups
              available).drainReadyGroups
        generated canonical available

/-- Cache exposure preserves the full structural live-root frame and retirement.
Witness: only task-local rejection slots change; root metadata and topology remain intact.
-/
theorem LiveRootFrame.cacheTaskFailures {queue work parents}
    (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work)
    (available : List (Occurrence × Nat))
    : LiveRootFrame (queue.cacheTaskFailures available) work parents
      ∧ (queue.cacheTaskFailures available).UncancelledRetiredAncestors work := by
  have cached := (show RootReplayFrame queue work parents from ⟨frame, retired⟩
    ).cacheTaskFailures available
  exact ⟨cached.live, cached.retired⟩

/-- Item preparation preserves live roots and structural retirement under its snapshot.
Witness: item registration, pruning and startup retain the structural frame before the
stream carrier and final drain. No accepted-source or healthy-owner premise is needed.
-/
theorem LiveRootFrame.prepareItems {queue work parents stream items}
    (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : LiveRootFrame (queue.preparedStreamItems items available) work parents
      ∧ (queue.preparedStreamItems items available).UncancelledRetiredAncestors work := by
  have retirement := State.preparedStreamItems_structuralRetirement generated
    frame.records frame.links canonical frame.registered frame.tasks frame.roots retired
    matching available
  have metadata := State.preparedStreamItems_noticeMetadata generated frame.refs
    frame.records frame.support matching available
  exact ⟨⟨metadata.1, retirement.1, retirement.2.1, retirement.2.2.1, retirement.2.2.2.1,
    retirement.2.2.2.2.1, metadata.2.2,
    frame.present.preparedStreamItems frame.refs frame.registered frame.tasks matching available⟩,
    retirement.2.2.2.2.2⟩

theorem RootReplayFrame.streamItems {queue work parents stream items}
    (frame : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat))
    : RootReplayFrame (queue.streamItems stream items available).1 work parents := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact frame
  · have prepared := frame.live.prepareItems frame.retired generated canonical matching available
    have prepared : RootReplayFrame (queue.preparedStreamItems items available) work parents :=
      ⟨prepared.1, prepared.2⟩
    exact prepared.drainReadyGroups generated canonical available

theorem RootReplayFrame.handleGraphEvent {queue work parents}
    (frame : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : RootReplayFrame (queue.handleGraphEvent event available).1 work parents := by
  have cached := frame.cacheTaskFailures available
  simp only [State.handleGraphEvent]
  cases event with
  | taskSuccess occurrence result =>
      exact cached.taskSuccess generated (context.cacheTaskFailures available) canonical matching available
  | taskFailure occurrence errors =>
      exact ⟨cached.live.taskFailure occurrence errors,
        cached.retired.taskFailure occurrence errors⟩
  | streamItems stream items =>
      exact cached.streamItems generated canonical matching available
  | streamSuccess stream =>
      simp only [State.streamSuccess]
      split <;> exact ⟨⟨cached.live.refs, cached.live.records, cached.live.links,
        cached.live.registered, cached.live.tasks, cached.live.roots,
        ⟨cached.live.support.contents, cached.live.support.roots⟩, cached.live.present⟩,
        cached.retired⟩
  | streamFailure stream errors =>
      simp only [State.streamFailure]
      split <;> exact ⟨⟨cached.live.refs, cached.live.records, cached.live.links,
        cached.live.registered, cached.live.tasks, cached.live.roots,
        ⟨cached.live.support.contents, cached.live.support.roots⟩, cached.live.present⟩,
        cached.retired⟩

  | groupFailure failure =>
      simp only [State.groupFailure]
      split
      · exact cached
      · split <;> exact ⟨⟨cached.live.refs, cached.live.records, cached.live.links,
          cached.live.registered, cached.live.tasks, cached.live.roots,
          ⟨cached.live.support.contents, cached.live.support.roots⟩, cached.live.present⟩,
          cached.retired⟩

/-- A matched host transition preserves the full live-root frame and structural retirement
under its fixed rejection snapshot. These are local queue invariants, not source laws.
-/
theorem LiveRootFrame.handleGraphEvent {queue work parents}
    (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : LiveRootFrame (queue.handleGraphEvent event available).1 work parents
      ∧ (queue.handleGraphEvent event available).1.UncancelledRetiredAncestors work := by
  have next := (show RootReplayFrame queue work parents from ⟨frame, retired⟩).handleGraphEvent
    generated context canonical event matching available
  exact ⟨next.live, next.retired⟩

/-- Internal enqueue effects retain structural roots and retirement evidence. -/
theorem RootReplayFrame.dispatchGraphEvent {queue work parents}
    (frame : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : RootReplayFrame (queue.dispatchGraphEvent event available).1 work parents := by
  have next := frame.handleGraphEvent generated context canonical event matching available
  exact ⟨⟨next.live.refs, next.live.records, next.live.links, next.live.registered,
    next.live.tasks, next.live.roots, ⟨next.live.support.contents, next.live.support.roots⟩,
    next.live.present⟩, next.retired⟩

theorem RootReplayFrame.replayGraphEvents {queue work parents}
    (frame : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : RootReplayFrame (queue.replayGraphEvents events available) work parents := by
  induction events generalizing queue with
  | nil => exact frame
  | cons event rest ih =>
      exact ih (frame.dispatchGraphEvent generated context canonical event
        (matching event List.mem_cons_self) available)
        (context.dispatchGraphEvent event (matching event List.mem_cons_self) available).1
        (fun next member => matching next (List.mem_cons_of_mem _ member))

theorem RootReplayFrame.handleGraphEvents {queue work parents}
    (frame : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : RootReplayFrame (queue.handleGraphEvents events).1 work parents := by
  by_cases ended : queue.terminated = true
  · simpa only [State.handleGraphEvents, ended, ite_true] using frame
  · have running : queue.terminated = false := Bool.eq_false_iff.mpr ended
    obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
    have replayed := frame.replayGraphEvents generated context canonical events matching
      (GraphEvent.availableFailures events)
    rw [same]
    exact ⟨⟨replayed.live.refs, replayed.live.records, replayed.live.links,
      replayed.live.registered, replayed.live.tasks, replayed.live.roots,
      ⟨replayed.live.support.contents, replayed.live.support.roots⟩,
      replayed.live.present⟩, replayed.retired⟩

theorem initialRootReplayFrame {work parents} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : RootReplayFrame (State.initialize (Work.fromExecution work)) work parents := by
  have registered := createWorkQueue_registration work generated.declarations
  exact ⟨⟨createWorkQueue_groupRefsUnique _, createWorkQueue_groupNodesMatchWork work,
    createWorkQueue_childLinksCanonical _ parents
      (fun _ member => workFromSpec_groups_parentCanonical_root canonical member),
    registered.1, registered.2, generated.initialRootAncestorsRetired,
    createWorkQueue_fromSpec_groupRefSupport work, createWorkQueue_rootGroupsPresent _⟩,
    generated.initialUncancelledRetirement⟩

/-- Actual normalized replay has live roots and retired ancestry at every batch boundary.
Generated matching supplies the invariant from real initialization; no accepted-start or
output-admission premise and no flattened-state correspondence is used.
-/
theorem ExecutedWork.runNormalized_liveRootFrame {work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : ∃ parents,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ LiveRootFrame
            ((State.initialize (Work.fromExecution work)).runNormalized batches).1 work
            parents
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.UncancelledRetiredAncestors
            work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have loop (more : List (List GraphEvent)) (included : more.Subset batches)
      (current : State) (frame : RootReplayFrame current work parents)
      (context : current.RegistrationFrame work)
      : RootReplayFrame
          (more.foldl (fun next batch => (next.handleGraphEvents batch).1) current)
          work parents := by
    induction more generalizing current with
    | nil => exact frame
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (frame.handleGraphEvents generated context canonical batch (fun _ member =>
            matching _ (List.mem_flatten.mpr ⟨batch, included List.mem_cons_self, member⟩)))
          (context.handleGraphEvents batch (fun _ member =>
            matching _ (List.mem_flatten.mpr ⟨batch, included List.mem_cons_self, member⟩))).1
  have final := loop batches (List.Subset.refl _) _ (initialRootReplayFrame generated canonical)
    (State.initialize_registrationFrame generated.declarations)
  rw [← State.runNormalized_stateFold] at final
  exact ⟨parents, canonical, final.live, final.retired⟩

/-- Every active root in actual matched batch replay retains a live group record. -/
theorem ExecutedWork.runNormalized_rootsPresent {work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.RootGroupsPresent := by
  obtain ⟨_, _, frame, _⟩ := generated.runNormalized_liveRootFrame batches matching
  exact frame.present

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
