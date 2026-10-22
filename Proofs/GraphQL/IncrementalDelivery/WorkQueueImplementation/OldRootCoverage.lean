import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorCoverageReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredFailureReports
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseHealth

/-! Previously covered live groups remain root-covered, including failed latent groups. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Structural facts needed to transport an existing root path through actual handlers.
This proof frame contains no health, output-admission, or terminal-reporting assumption.
-/
private structure CoverageFrame (queue : State) (work : Execution.Work)
    (parents : NodeRef → NodeRefs)
    : Prop where
  refs : queue.GroupRefsUnique
  live : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  records : queue.GroupNodesMatchWork work
  children : queue.ChildGroupsUnique
  links : queue.ChildLinksCanonical parents

/-- Matched event processing retains the independently proved structural frame.
Witness: the existing per-handler metadata and permanent-registration theorems.
-/
private theorem CoverageFrame.handleGraphEvent {queue : State} {work parents}
    (frame : CoverageFrame queue work parents) (event : GraphEvent)
    (matching : event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : CoverageFrame (queue.handleGraphEvent event).1 work parents := by
  have registered := queue.handleGraphEvent_registration frame.live frame.tasks event matching
  exact ⟨frame.refs.handleGraphEvent event, registered.1, registered.2.1,
    frame.records.handleGraphEvent event matching, frame.children.handleGraphEvent event,
    frame.links.handleGraphEvent event matching canonical⟩

/-- A matched item integration retains the same structural frame.
Witness: integration, fresh pruning, and activation preserve each field independently.
-/
private theorem CoverageFrame.integrateStreamItem {queue : State}
    {work parents stream items} (frame : CoverageFrame queue work parents)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {item : StreamItem} (member : item ∈ items)
    : CoverageFrame (queue.integrateStreamItem item) work parents := by
  have registered := queue.integrateStreamItem_registration frame.live frame.tasks matching member
  exact ⟨((frame.refs.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
    registered.1, registered.2.1,
    ((frame.records.maybeIntegrateWork item.work
      (fun _ included => matching.streamItem_childGroups_recordAt member included)).pruneEmptyGroups
        _).startNewWork _,
    ((frame.children.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
    ((frame.links.maybeIntegrateWork item.work
      (fun _ included => matching.streamItem_childGroups_parentCanonical canonical member included)).pruneEmptyGroups
        _).startNewWork _⟩

-----------------------------------------------------------------------------------------
-- Transport old paths without requiring semantic health
-----------------------------------------------------------------------------------------

/-- An old covered group that survives a matched handler still has an active-root path.
Witness: successful inputs preserve integrated paths through the actual owner fold;
failures preserve surviving subtrees; item preparation retains every earlier path.
In particular, a latent cached failure does not need to be semantically healthy.
-/
private theorem CoverageFrame.oldRootCoverage {queue : State} {work parents target}
    (frame : CoverageFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    (survives : ∃ node, (queue.handleGraphEvent event).1.groupNode? target = some node)
    : ∃ root ∈ (queue.handleGraphEvent event).1.rootGroups,
        (queue.handleGraphEvent event).1.LiveDescendant root target := by
  have forest := State.RemovalForest.of_generated generated frame.children frame.links
    frame.records canonical
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa [State.handleGraphEvent, State.taskSuccess, found] using covered
      | some node =>
          let stored := queue.putTaskNode { node with value := some result.value }
          have refs : stored.GroupRefsUnique := frame.refs
          have children : stored.ChildGroupsUnique := frame.children
          have links : stored.ChildLinksCanonical parents := frame.links
          have records : stored.GroupNodesMatchWork work := frame.records
          obtain ⟨root, active, path⟩ := covered
          apply State.taskSuccess_integrated_root_coverage frame.refs found result
          · exact State.RemovalForest.of_generated generated
              (children.maybeIntegrateWork result.work (some occurrence))
              (links.maybeIntegrateWork result.work
                (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
                (some occurrence))
              (records.maybeIntegrateWork result.work
                (fun _ member => matching.taskChildGroups_recordAt member)
                (some occurrence)) canonical
          · refine ⟨root, ?_, ?_⟩
            · rwa [State.maybeIntegrateWork_rootGroups]
            · exact (State.LiveDescendant.of_groupNodes_eq (queue := queue) (next := stored)
                rfl path).maybeIntegrateWork refs
                result.work (some occurrence)
          · exact survives
  | taskFailure occurrence errors =>
      exact State.taskFailure_root_coverage frame.refs forest occurrence errors covered survives
  | streamItems stream items =>
      have prepared := State.preparedStreamItems_preserves
        (fun current => CoverageFrame current work parents
          ∧ ∃ root ∈ current.rootGroups, current.LiveDescendant root target)
        ⟨frame, covered⟩ items
        (fun current item member prior =>
          ⟨prior.1.integrateStreamItem matching canonical member,
            State.integrateStreamItem_old_root_coverage prior.1.refs prior.1.live item prior.2⟩)
      change ∃ root ∈ (queue.streamItems stream items).1.rootGroups,
        (queue.streamItems stream items).1.LiveDescendant root target
      change ∃ node, (queue.streamItems stream items).1.groupNode? target = some node at survives
      rw [queue.streamItems_eq stream items] at survives ⊢
      split at survives
      · rename_i inactive
        simp only [inactive, ↓reduceIte]
        exact covered
      · rename_i active
        simp only [active]
        exact State.drainReadyGroups_root_coverage prepared.1.refs
          (State.RemovalForest.of_generated generated prepared.1.children prepared.1.links
            prepared.1.records canonical) target prepared.2 survives
  | streamSuccess stream =>
      obtain ⟨root, active, path⟩ := covered
      change ∃ root ∈ (queue.streamSuccess stream).1.rootGroups,
        (queue.streamSuccess stream).1.LiveDescendant root target
      unfold State.streamSuccess
      split <;> exact ⟨root, active, State.LiveDescendant.of_groupNodes_eq (queue := queue) rfl path⟩
  | streamFailure stream errors =>
      obtain ⟨root, active, path⟩ := covered
      change ∃ root ∈ (queue.streamFailure stream errors).1.rootGroups,
        (queue.streamFailure stream errors).1.LiveDescendant root target
      unfold State.streamFailure
      split <;> exact ⟨root, active, State.LiveDescendant.of_groupNodes_eq (queue := queue) rfl path⟩

-----------------------------------------------------------------------------------------
-- Old covered refs cannot strand at a later terminal source boundary
-----------------------------------------------------------------------------------------

/-- Matched finite replay retains the structural path-transport frame.
Witness: source-order induction through existing metadata and registration preservation.
-/
private theorem CoverageFrame.replayGraphEvents {queue : State} {work parents}
    (frame : CoverageFrame queue work parents) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : CoverageFrame (queue.replayGraphEvents events) work parents := by
  induction events generalizing queue with
  | nil => exact frame
  | cons event rest ih =>
      exact ih (frame.handleGraphEvent event (matching event List.mem_cons_self) canonical)
        (fun later member => matching later (List.mem_cons_of_mem _ member))

/-- A previously covered ref still has a root path if it survives a finite continuation.
Witness: permanent registration excludes revival of a ref removed at an intermediate
boundary; each remaining handler transports its established path without a health premise.
-/
private theorem CoverageFrame.oldRootContinuation {queue : State} {work parents target}
    (frame : CoverageFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    (survives : ∃ node, (queue.replayGraphEvents events).groupNode? target = some node)
    : ∃ root ∈ (queue.replayGraphEvents events).rootGroups,
        (queue.replayGraphEvents events).LiveDescendant root target := by
  induction events generalizing queue with
  | nil => exact covered
  | cons event rest ih =>
      have source := matching event List.mem_cons_self
      have nextFrame := frame.handleGraphEvent event source canonical
      have nextLive : ∃ node, (queue.handleGraphEvent event).1.groupNode? target = some node := by
        cases found : (queue.handleGraphEvent event).1.groupNode? target with
        | some node => exact ⟨node, rfl⟩
        | none =>
            obtain ⟨root, _, path⟩ := covered
            obtain ⟨node, nodeFound⟩ := path.target_present
            have registered : target ∈ queue.registeredGroups :=
              State.groupNode?_ref nodeFound ▸ frame.live node
                (List.mem_of_find?_eq_some nodeFound)
            have nextRegistered := (queue.handleGraphEvent_registration frame.live frame.tasks
              event source).2.2 registered
            have retired := State.RetiredGroup.replayGraphEvents
              (State.RetiredGroup.of_lookup_none nextRegistered found) rest
            obtain ⟨final, finalFound⟩ := survives
            change ((queue.handleGraphEvent event).1.replayGraphEvents rest).groupNode? target
              = some final at finalFound
            rw [retired.lookup_none] at finalFound
            contradiction
      exact ih nextFrame
        (fun later member => matching later (List.mem_cons_of_mem _ member))
        (frame.oldRootCoverage generated canonical event source covered nextLive) survives

/-- Every matched initial replay supplies the structural frame for path continuation.
Witness: canonical generated parent records and initialization bookkeeping, then replay.
-/
private theorem initialCoverageFrame {work : Execution.Work} {parents}
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : CoverageFrame (State.initialize (Work.fromExecution work)) work parents := by
  have registered := createWorkQueue_registration work
  exact ⟨createWorkQueue_groupRefsUnique _, registered.1, registered.2,
    createWorkQueue_groupNodesMatchWork work, createWorkQueue_childGroupsUnique _,
    createWorkQueue_childLinksCanonical _ parents
      (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)⟩

/-- An earlier root-covered group cannot remain live after concrete termination.
Witness: matched continuation preserves an established path even for a failed group;
terminal root exhaustion contradicts that path. Permanent registration prevents revival.
No terminal reporting or semantic health assumption is used.
-/
theorem ExecutedWork.terminal_oldRootCovered_absent {work : Execution.Work}
    {inputs before after target} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (splitInputs : inputs.flatten = before ++ after)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (covered
      : let initial := State.initialize (Work.fromExecution work)
        ∃ root ∈ (initial.replayGraphEvents before).rootGroups,
          (initial.replayGraphEvents before).LiveDescendant root target)
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.groupNode?
        target
      = none := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := (initialCoverageFrame canonical).replayGraphEvents before
    (fun event member => valid.eachMatches (splitInputs ▸ List.mem_append_left after member))
    canonical
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  change ((State.initialize (Work.fromExecution work)).replayGraphEvents inputs.flatten).groupNode?
    target = none
  cases found
        : ((State.initialize (Work.fromExecution work)).replayGraphEvents
            inputs.flatten).groupNode?
            target with
  | none => rfl
  | some node =>
      have survives : ∃ final,
          (((State.initialize (Work.fromExecution work)).replayGraphEvents before).replayGraphEvents
            after).groupNode? target = some final := by
        have together : ((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).replayGraphEvents after
            = (State.initialize (Work.fromExecution work)).replayGraphEvents inputs.flatten := by
          simp only [splitInputs, State.replayGraphEvents, List.foldl_append]
        rw [together]
        exact ⟨node, found⟩
      obtain ⟨root, active, path⟩ := frame.oldRootContinuation generated canonical after
        (fun event member => valid.eachMatches (splitInputs ▸ List.mem_append_right before member))
        covered survives
      have roots := (createWorkQueue_replayGraphEvents_terminalRoots started ended).1
      have together : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).replayGraphEvents after
          = (State.initialize (Work.fromExecution work)).replayGraphEvents inputs.flatten := by
        simp only [splitInputs, State.replayGraphEvents, List.foldl_append]
      rw [together, roots] at active
      cases active

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
