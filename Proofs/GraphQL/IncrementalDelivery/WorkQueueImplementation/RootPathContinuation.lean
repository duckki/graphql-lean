import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActualSourceFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorCoverageReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay

/-! Existing root paths persist or permanently retire through cached startup. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An earlier covered ref retains a live root path or is permanently retired. -/
def State.RootCoveredOrRetired (queue : State) (target : NodeRef) : Prop :=
  (∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
  ∨ queue.RetiredGroup target

private theorem covered_registered {queue : State} {target}
    (live : queue.LiveGroupsRegistered)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    : target ∈ queue.registeredGroups := by
  obtain ⟨_, _, path⟩ := covered
  obtain ⟨node, found⟩ := path.target_present
  exact State.groupNode?_ref found ▸ live node (List.mem_of_find?_eq_some found)

/-- Cache exposure preserves existing group paths and permanent retirement. -/
theorem State.RootCoveredOrRetired.cacheTaskFailures {queue target}
    (prior : State.RootCoveredOrRetired queue target)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).RootCoveredOrRetired target := by
  rcases prior with ⟨root, active, path⟩ | retired
  · have roots : (queue.cacheTaskFailures available).rootGroups = queue.rootGroups := by
      have frame := congrArg State.rootGroups (queue.cacheTaskFailures_frame available)
      exact frame
    exact .inl ⟨root, roots.symm ▸ active,
      State.LiveDescendant.of_groupNodes_eq (queue.cacheTaskFailures_groupNodes available) path⟩
  · exact .inr (retired.cacheTaskFailures available)

/-- A termination flag has no effect on root paths or retirement. -/
theorem State.RootCoveredOrRetired.withTerminated {queue target}
    (prior : State.RootCoveredOrRetired queue target) (terminated : Bool)
    : ({ queue with terminated } : State).RootCoveredOrRetired target := by
  rcases prior with ⟨root, active, path⟩ | retired
  · exact .inl ⟨root, active, State.LiveDescendant.of_groupNodes_eq (queue := queue)
      (next := { queue with terminated }) rfl path⟩
  · exact .inr retired

/-- Updating the pending notice FIFO does not change an existing root path. -/
theorem State.RootCoveredOrRetired.withGroupFailures {queue target}
    (prior : State.RootCoveredOrRetired queue target)
    (groupFailureEvents : List GroupFailureEvent)
    : ({ queue with groupFailureEvents } : State).RootCoveredOrRetired target := by
  rcases prior with ⟨root, active, path⟩ | retired
  · exact .inl ⟨root, active, State.LiveDescendant.of_groupNodes_eq (queue := queue)
      (next := { queue with groupFailureEvents }) rfl path⟩
  · exact .inr retired

/-- Item integration preserves an old path when its target survives; otherwise it retires. -/
theorem ParentCutFrame.integrateStreamItem_rootCoveredOrRetired
    {queue work parents target stream items item}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items) (prior : queue.RootCoveredOrRetired target)
    (available : List (Occurrence × Nat))
    : (queue.integrateStreamItem item available).RootCoveredOrRetired target := by
  rcases prior with covered | retired
  · have registered := covered_registered frame.live covered
    cases found : (queue.integrateStreamItem item available).groupNode? target with
    | none => exact .inr (.of_lookup_none
        ((queue.integrateStreamItem_registration frame.live frame.tasks matching member
          frame.registration available).2.2 registered) found)
    | some node =>
        have forest := State.RemovalForest.of_generated generated
          (frame.children.maybeIntegrateWork item.work)
          (frame.links.maybeIntegrateWork item.work
            (fun _ included => matching.streamItem_childGroups_parentCanonical canonical member
              included))
          (frame.records.maybeIntegrateWork item.work
            (fun _ included => matching.streamItem_childGroups_recordAt member included)) canonical
        exact .inl (State.integrateStreamItem_old_root_coverage frame.keys frame.live item forest
          covered available ⟨node, found⟩)
  · exact .inr
      (((retired.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available)

private theorem ParentCutFrame.handler_oldRootCoverage {queue work parents target}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    (available : List (Occurrence × Nat))
    (survives
      : ∃ node, (queue.handleGraphEvent event available).1.groupNode? target = some node)
    : ∃ root ∈ (queue.handleGraphEvent event available).1.rootGroups,
        (queue.handleGraphEvent event available).1.LiveDescendant root target := by
  let current := queue.cacheTaskFailures available
  have cached := frame.cacheTaskFailures available
  have currentCoverage : ∃ root ∈ current.rootGroups, current.LiveDescendant root target := by
    obtain ⟨root, active, path⟩ := covered
    have roots : current.rootGroups = queue.rootGroups := by
      have same := congrArg State.rootGroups (queue.cacheTaskFailures_frame available)
      exact same
    exact ⟨root, roots.symm ▸ active,
      State.LiveDescendant.of_groupNodes_eq (queue.cacheTaskFailures_groupNodes available) path⟩
  have forest := State.RemovalForest.of_generated generated cached.children cached.links
    cached.records canonical
  cases event with
  | taskSuccess occurrence result =>
      change ∃ node, (current.taskSuccess occurrence result available).1.groupNode? target
        = some node at survives
      change ∃ root ∈ (current.taskSuccess occurrence result available).1.rootGroups,
        (current.taskSuccess occurrence result available).1.LiveDescendant root target
      cases found : current.taskNode? occurrence with
      | none => simpa only [State.taskSuccess, found] using currentCoverage
      | some node =>
          let stored := current.putTaskNode { node with value := some result.value }
          have storedChildren : stored.ChildGroupsUnique := cached.children
          have storedLinks : stored.ChildLinksCanonical parents := cached.links
          have storedRecords : stored.GroupNodesMatchWork work := cached.records
          obtain ⟨root, active, path⟩ := currentCoverage
          apply State.taskSuccess_integrated_root_coverage cached.keys found result available
          · exact State.RemovalForest.of_generated generated
              (storedChildren.maybeIntegrateWork result.work (some occurrence))
              (storedLinks.maybeIntegrateWork result.work
                (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
                (some occurrence))
              (storedRecords.maybeIntegrateWork result.work
                (fun _ member => matching.taskChildGroups_recordAt member) (some occurrence))
              canonical
          · refine ⟨root, ?_, ?_⟩
            · rwa [State.maybeIntegrateWork_rootGroups]
            · exact (State.LiveDescendant.of_groupNodes_eq (queue := current) (next := stored)
                rfl path).maybeIntegrateWork cached.keys result.work (some occurrence)
          · exact survives
  | taskFailure occurrence errors =>
      exact State.taskFailure_root_coverage cached.keys forest occurrence errors currentCoverage
        survives
  | streamItems stream items =>
      have prepared := State.preparedStreamItems_preserves
        (fun next => ParentCutFrame next work parents ∧ next.RootCoveredOrRetired target)
        ⟨cached, .inl currentCoverage⟩ items available
        (fun next item member prior =>
          ⟨prior.1.integrateStreamItem generated canonical matching member available,
            prior.1.integrateStreamItem_rootCoveredOrRetired generated canonical matching member
              prior.2 available⟩)
      change ∃ root ∈ (current.streamItems stream items available).1.rootGroups,
        (current.streamItems stream items available).1.LiveDescendant root target
      change ∃ node, (current.streamItems stream items available).1.groupNode? target = some node
        at survives
      rw [current.streamItems_eq stream items available] at survives ⊢
      split at survives
      · rename_i inactive
        simpa only [inactive, ↓reduceIte] using currentCoverage
      · rename_i active
        simp only [active]
        rcases prepared.2 with path | retired
        · exact State.drainReadyGroups_root_coverage prepared.1.keys
            (State.RemovalForest.of_generated generated prepared.1.children prepared.1.links
              prepared.1.records canonical) available target path survives
        · obtain ⟨node, found⟩ := survives
          change ((current.preparedStreamItems items available).drainReadyGroups
            available).1.groupNode? target = some node at found
          rw [(retired.drainReadyGroups available).lookup_none] at found
          contradiction
  | streamSuccess stream =>
      obtain ⟨root, active, path⟩ := currentCoverage
      change ∃ root ∈ (current.streamSuccess stream).1.rootGroups,
        (current.streamSuccess stream).1.LiveDescendant root target
      unfold State.streamSuccess
      split <;> exact ⟨root, active, State.LiveDescendant.of_groupNodes_eq
        (queue := current) rfl path⟩
  | streamFailure stream errors =>
      obtain ⟨root, active, path⟩ := currentCoverage
      change ∃ root ∈ (current.streamFailure stream errors).1.rootGroups,
        (current.streamFailure stream errors).1.LiveDescendant root target
      unfold State.streamFailure
      split <;> exact ⟨root, active, State.LiveDescendant.of_groupNodes_eq
        (queue := current) rfl path⟩
  | groupFailure notice =>
      obtain ⟨root, active, path⟩ := currentCoverage
      change ∃ root ∈ (current.groupFailure notice).1.rootGroups,
        (current.groupFailure notice).1.LiveDescendant root target
      unfold State.groupFailure
      split
      · exact ⟨root, active, path⟩
      · split <;> exact ⟨root, active, State.LiveDescendant.of_groupNodes_eq
          (queue := current) rfl path⟩

/-- Each matched source handler retains an old root path or permanently retires its target. -/
theorem ParentCutFrame.handleGraphEvent_rootCoveredOrRetired {queue work parents target}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (prior : queue.RootCoveredOrRetired target) (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.RootCoveredOrRetired target := by
  rcases prior with covered | retired
  · cases found : (queue.handleGraphEvent event available).1.groupNode? target with
    | none =>
        exact .inr (.of_lookup_none
          ((queue.handleGraphEvent_registration frame.live frame.tasks event matching
            frame.registration available).2.2 (covered_registered frame.live covered)) found)
    | some node =>
        exact .inl (frame.handler_oldRootCoverage generated canonical event matching
          covered available ⟨node, found⟩)
  · exact .inr (retired.handleGraphEvent event available)

/-- Fixed-snapshot FIFO continuation transports both the structural frame and old path. -/
theorem ParentCutFrame.replayGraphEvents_rootCoveredOrRetired {queue work parents target}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (prior : queue.RootCoveredOrRetired target) (available : List (Occurrence × Nat))
    : ParentCutFrame (queue.replayGraphEvents events available) work parents
      ∧ (queue.replayGraphEvents events available).RootCoveredOrRetired target := by
  induction events generalizing queue with
  | nil => exact ⟨frame, prior⟩
  | cons event rest ih =>
      have next := frame.handleGraphEvent_rootCoveredOrRetired generated canonical event
        (matching _ List.mem_cons_self) prior available
      have dispatched : (queue.dispatchGraphEvent event available).1.RootCoveredOrRetired target := by
        exact next.withGroupFailures _
      exact ih
        (frame.dispatchGraphEvent generated canonical event
          (matching _ List.mem_cons_self) available)
        (fun next member => matching next (List.mem_cons_of_mem _ member)) dispatched

/-- Complete host batches preserve old-path accounting, including terminal flag updates. -/
theorem ParentCutFrame.handleGraphEvents_rootCoveredOrRetired {queue work parents target}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (prior : queue.RootCoveredOrRetired target)
    : ParentCutFrame (queue.handleGraphEvents events).1 work parents
      ∧ (queue.handleGraphEvents events).1.RootCoveredOrRetired target := by
  cases running : queue.terminated with
  | true =>
      simpa only [State.handleGraphEvents, running, ↓reduceIte] using And.intro frame prior
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      have next := frame.replayGraphEvents_rootCoveredOrRetired generated canonical events matching
        prior (GraphEvent.availableFailures events)
      rw [same]
      exact ⟨⟨next.1.safe, next.1.keys, next.1.records, next.1.links, next.1.children,
        next.1.live, next.1.tasks, next.1.closed, next.1.fields, next.1.complete,
        next.1.cancelled, next.1.registration.withTerminated _⟩,
        next.2.withTerminated terminal⟩

/-- Actual batch continuation preserves root-path accounting under each batch's own snapshot. -/
theorem ParentCutFrame.rawBatches_rootCoveredOrRetired {queue work parents target}
    (frame : ParentCutFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    (prior : queue.RootCoveredOrRetired target)
    : ParentCutFrame (queue.rawBatches batches).1 work parents
      ∧ (queue.rawBatches batches).1.RootCoveredOrRetired target := by
  induction batches generalizing queue with
  | nil => exact ⟨frame, prior⟩
  | cons batch rest ih =>
      have next := frame.handleGraphEvents_rootCoveredOrRetired generated canonical batch
        (fun event member => matching event (List.mem_append_left _ member)) prior
      exact ih next.1 (fun event member => matching event (List.mem_append_right _ member)) next.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
