import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.UnsettledTaskRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SuccessFoldRetention

/-! Generated accepted registration constructs the exact unsettled/decrement evidence
needed by the success fold and mixed drain. The resulting task-owner classification
mentions only actual records and emitted failure paths, never desired abort effects.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode WorkQueueEvent)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Derive the next handler's exact accounting from the actual started prefix
-----------------------------------------------------------------------------------------

/-- The alternative's current kernel has the original all-owner ledger before the next
started input. Terminal erasure is excluded by that same start premise, not a new law.
-/
theorem generatedReplay_nextAccounting {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : ((State.initialize work).runNormalized inputs).1.queue.PendingAccounting work
        (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) := by
  obtain ⟨raw, _, accepted⟩ := generatedReplay_beforeNext generated valid started
  obtain ⟨prior, _, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  rw [raw]
  exact (ReferenceWorkQueue.createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated inputs.flatten prior accepted

/-- Matching item work preserves the pending lower bound at actual pre-drain preparation. -/
theorem preparedStreamItems_pendingBound {queue : Kernel} {work settled stream items}
    (accounted : queue.PendingAccounting work settled)
    (matching : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.preparedStreamItems items).PendingBound (fun _ => True) settled := by
  let invariant (current : Kernel) := current.PendingBound (fun _ => True) settled
    ∧ current.GroupRefsUnique ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
  suffices invariant (queue.preparedStreamItems items) from this.1
  apply ReferenceWorkQueue.State.preparedStreamItems_preserves invariant
    ⟨accounted.pending, accounted.refs, accounted.liveGroups, accounted.taskGroups⟩ items
  intro current item member prior
  have registered := current.maybeIntegrateWork_registration prior.2.2.1 prior.2.2.2
    item.work (matching.streamItem_childTasksCovered member)
  have pruned := ReferenceWorkQueue.State.pruneEmptyGroups_registration registered.1 registered.2.1
    (current.maybeIntegrateWork item.work).2.newGroups
  exact ⟨((prior.1.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _,
    ((prior.2.1.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _,
    ReferenceWorkQueue.State.startNewWork_registration pruned.1 pruned.2.1 _⟩

-----------------------------------------------------------------------------------------
-- Classify each still-unsettled task owner across the complete actual handler
-----------------------------------------------------------------------------------------

/-- Every live registration owner of a task still unsettled after the input survives the
actual generated handler or lies below its emitted failure in the exact cleanup view.
Membership links, counters, decrement debt and topology are constructed from the original
generated/source/start premises. The same-run unsettledness predicate defines the domain;
no native acquisition, desired endpoint, or cleanup operation is assumed.
-/
def GeneratedUnsettledTaskOwnerProgress : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (task : Task),
        let before := ((State.initialize work).runNormalized inputs).1.queue
        let snapshot := registrationSnapshot before event
        let reduced := before.handleGraphEvent event
        task ∈ snapshot.tasks
        → task.occurrence
          ∉ event.recordTaskOutcome
              (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten)
        → ∀ key ∈ task.groups.map DeliveryNode.ref,
            key ∈ snapshot.groupNodes.map (fun node => node.group.node.ref)
            → key ∈ reduced.1.groupNodes.map (fun node => node.group.node.ref)
              ∨ ∃ root ∈ failureRoots reduced.2,
                  (failurePruningView before event reduced.2).LiveDescendant root key

/-- Construct all five handler cases through real registration, settlement and draining,
including existing/incoming unstarted tasks and latent failed owners.
-/
theorem GeneratedUnsettledTaskOwnerProgress_holds
    : GeneratedUnsettledTaskOwnerProgress := by
  intro work inputs event generated valid started task
  dsimp only
  intro registered pending key contributes present
  let before := ((State.initialize work).runNormalized inputs).1.queue
  let snapshot := registrationSnapshot before event
  let settled := ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten
  change task ∈ snapshot.tasks at registered
  change key ∈ (before.handleGraphEvent event).1.groupNodes.map (fun node => node.group.node.ref)
    ∨ ∃ root ∈ failureRoots (before.handleGraphEvent event).2,
      (failurePruningView before event (before.handleGraphEvent event).2).LiveDescendant root key
  obtain ⟨_, priorStarted, _⟩ := generatedReplay_beforeNext generated valid started
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have accounted := generatedReplay_nextAccounting generated valid started
  have frame := GeneratedSnapshotTaskEvidence_holds work inputs event generated valid priorStarted
  obtain ⟨parents, forest, _⟩ := generatedSnapshot_removalForest generated valid priorStarted
  have projection := generatedSnapshot_projection generated valid priorStarted
  have dispatch := generatedReplay_dispatchProjection generated valid started
  have notSettled : task.occurrence ∉ settled := by
    intro processed
    apply pending
    cases event with
    | taskSuccess | taskFailure => exact List.mem_cons_of_mem _ processed
    | streamItems | streamSuccess | streamFailure => exact processed
  have links := generatedSnapshot_unsettledLinks generated valid started task registered notSettled
  change SnapshotTaskEvidence snapshot work at frame
  change snapshot.RemovalForest parents at forest
  change snapshot.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref) at links
  change key ∈ snapshot.groupNodes.map (fun node => node.group.node.ref) at present
  cases event with
  | taskSuccess incoming result =>
      cases inputFound : before.taskNode? incoming with
      | none =>
          simp only [snapshot, registrationSnapshot, inputFound] at present
          exact Or.inl
            (by simpa only [ReferenceWorkQueue.State.handleGraphEvent,
              ReferenceWorkQueue.State.taskSuccess, inputFound] using present)
      | some input =>
          have inputFresh : incoming ∉ settled := by
            intro processed
            exact fresh.2.2.1 incoming List.mem_cons_self
              (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities _ processed)
          have childFresh : task.occurrence ∉ incoming :: settled := pending
          have debt := taskSuccess_registrationDebt accounted matching inputFound inputFresh
          have ownersUnique := accounted.matching.contributorsNodup generated
            (accounted.started input (List.mem_of_find?_eq_some inputFound))
          have folded := successGroupFold_unsettledOwners frame.keys links childFresh input.task.groups
            ownersUnique debt
          let native : State := { queue := before }
          let stored : State :=
            { native with queue := before.putTaskNode { input with value := some result.value } }
          let integrated := stored.maybeIntegrateWork result.work (some incoming)
          let released := input.task.groups.foldl ReferenceWorkQueue.successGroupStep (snapshot, [], {})
          let starting : State := { integrated.1 with queue := released.1 }
          let initial := (starting.startNewWork released.2.2 integrated.2).1.queue
          obtain ⟨foldFrame, foldForest, foldEdges, foldClosures⟩ :=
            successGroupFold_releaseEvidence frame forest input.task.groups
          have initialPresent : key ∈ initial.groupNodes.map (fun node => node.group.node.ref) := by
            rw [State.startNewWork_groupNodes]
            exact folded.2.1 key contributes present
          have initialEdges : initial.GroupEdgesFrom snapshot := by
            intro key candidate lookup
            rw [ReferenceWorkQueue.State.groupNode?,
              State.startNewWork_groupNodes] at lookup
            exact foldEdges key candidate lookup
          have handler : before.handleGraphEvent (.taskSuccess incoming result)
              = (initial.drainReadyGroups.1, released.2.1 ++ initial.drainReadyGroups.2) := by
            have prepared : snapshot = integrated.1.queue := by
              simp only [snapshot, registrationSnapshot, inputFound]
              rfl
            let active := starting.startNewWork released.2.2 integrated.2
            have raw : before = (ReferenceWorkQueue.State.initialize
                (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents inputs.flatten :=
              (generatedReplay_beforeNext generated valid started).1
            have accepted := (generatedReplay_beforeNext generated valid started).2.2
            have sourceFound : ReferenceWorkQueue.State.taskNode?
                ((ReferenceWorkQueue.State.initialize
                  (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents inputs.flatten)
                incoming = some input := by rw [← raw]; exact inputFound
            have phase : active.1.queue = referenceTaskSuccessReady before incoming result input := by
              have actual : active.1.queue = (taskSuccessReadyPhase native incoming result input).1.queue := by
                simp only [taskSuccessReadyPhase]
                rw [← prepared]
              rw [actual]
              change (taskSuccessReadyPhase { queue := before } incoming result input).1.queue = _
              rw [raw]
              exact referencePrefix_taskSuccess_readyProjection generated inputs.flatten
                incoming result valid accepted input sourceFound
            obtain ⟨readyParents, readyFrame, readyForest⟩ := referencePrefix_taskSuccess_drainFrames
              generated inputs.flatten incoming result valid accepted input sourceFound
            rw [← raw] at readyFrame readyForest
            have actualFrame : active.1.queue.TaskOwnerFrame work := by rw [phase]; exact readyFrame
            have actualForest : active.1.queue.RemovalForest readyParents := by rw [phase]; exact readyForest
            have running : active.1.stopped = false :=
              (State.startNewWork_stopped starting released.2.2 integrated.2 []).trans
                (stored.maybeIntegrateWork_stopped result.work (some incoming))
            have drain := active.1.drainReadyGroups_projection running actualFrame actualForest active.2
            rw [← dispatch]
            rw [generatedReplay_beforeNextState generated valid started]
            change ((native.taskSuccess incoming result).1.queue,
              (native.taskSuccess incoming result).2.1) = _
            rw [State.taskSuccess_eq native incoming result input inputFound]
            dsimp only
            rw [← prepared]
            exact congrArg (fun pair => (pair.1, released.2.1 ++ pair.2)) drain
          rw [handler]
          have groupCore : initial.groupNodes = released.1.groupNodes :=
            State.startNewWork_groupNodes starting released.2.2 integrated.2
          have initialLinks : initial.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref) := by
            simpa only [ReferenceWorkQueue.State.TaskLinkedOn, groupCore] using folded.1
          have initialBound : initial.PendingBound (fun _ => True) (incoming :: settled) := by
            simpa only [ReferenceWorkQueue.State.PendingBound, groupCore] using folded.2.2
          rcases drain_unsettledTask_ownerCut (foldFrame.startAlternative (state := starting) _ _)
              (removalForest_startAlternative (state := starting) foldForest _ _) initialEdges
              (foldClosures.post (fun _ retired => retiredGroup_startAlternative
                (state := starting) retired released.2.2 integrated.2))
              initialLinks initialBound
              childFresh initial.groupNodes.length contributes initialPresent with kept | cut
          · exact Or.inl kept
          · obtain ⟨root, failed, path⟩ := cut
            refine Or.inr ⟨root, ?_, path⟩
            rw [failureRoots, List.filterMap_append]
            exact List.mem_append_right _ failed
  | streamItems stream items =>
      cases active : before.rootStreams.contains stream.ref with
      | false =>
          simp only [snapshot, registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] at present
          exact Or.inl
            (by
              simpa only [ReferenceWorkQueue.State.handleGraphEvent,
                ReferenceWorkQueue.State.streamItems, active, Bool.not_false, ↓reduceIte]
                using present)
      | true =>
          have counts : snapshot.PendingBound (fun _ => True) settled := by
            change (registrationSnapshot before (.streamItems stream items)).PendingBound (fun _ => True) settled
            rw [registrationSnapshot_streamItems before stream items projection active]
            exact preparedStreamItems_pendingBound accounted matching
          let prepared := items.foldl ReferenceWorkQueue.streamItemStep (before, [], [], [])
          let notice := WorkQueueEvent.streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1
          have same : snapshot = prepared.1 := registrationSnapshot_streamItems before stream items projection active
          have handler : before.handleGraphEvent (.streamItems stream items)
              = (snapshot.drainReadyGroups.1, notice :: snapshot.drainReadyGroups.2) := by
            simp only [ReferenceWorkQueue.State.handleGraphEvent,
              before.streamItems_eq stream items, active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [← same]
          have closures : ReferenceWorkQueue.GroupClosureAccounting snapshot (snapshot, [notice]) := by
            refine ⟨?_, ?_, fun _ retired => retired, ?_⟩
            · simp [notice, ReferenceWorkQueue.rawGroupClosureRefs]
            · simp [notice, ReferenceWorkQueue.rawGroupClosureRefs]
            · simp [notice, ReferenceWorkQueue.rawGroupClosureRefs]
          rw [handler]
          rcases drain_unsettledTask_ownerCut frame forest (.refl snapshot) closures links counts
              notSettled snapshot.groupNodes.length contributes present with kept | cut
          · exact Or.inl kept
          · obtain ⟨root, failed, path⟩ := cut
            refine Or.inr ⟨root, ?_, ?_⟩
            · simpa only [failureRoots, notice, List.filterMap_cons,
                ReferenceWorkQueue.State.drainReadyGroups] using failed
            · simpa only [List.singleton_append, ReferenceWorkQueue.State.drainReadyGroups] using path
  | taskFailure failed errors =>
      have unpublished : publicationRoots (before.taskFailure failed errors).2 = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro key member
        obtain ⟨group, groups, streams, emitted, _⟩ := mem_publicationRoots.mp member
        exact before.taskFailure_noGroupSuccess failed errors group groups streams emitted
      by_cases cut : ∃ root ∈ failureRoots (before.taskFailure failed errors).2,
          (failurePruningView before (.taskFailure failed errors)
            (before.taskFailure failed errors).2).LiveDescendant root key
      · exact Or.inr cut
      · have beforePresent : key ∈ before.groupNodes.map (fun node => node.group.node.ref) := present
        have live : ∃ node, before.groupNode? key = some node := by
          cases found : before.groupNode? key with
          | some node => exact ⟨node, rfl⟩
          | none =>
              exact False.elim ((before.groupNode?_eq_none_iff key).mp found beforePresent)
        have retained := taskFailure_outside_survives frame.keys forest failed errors live (by
          intro root emitted path
          apply cut
          refine ⟨root, emitted, ?_⟩
          exact failurePruningView_pathFrom (.refl before) path (by intros; simp [unpublished]))
        obtain ⟨node, found⟩ := retained
        exact Or.inl (List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found,
          ReferenceWorkQueue.State.groupNode?_ref found⟩)
  | streamSuccess stream =>
      change key ∈ before.groupNodes.map (fun node => node.group.node.ref) at present
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamSuccess]
      split <;> exact Or.inl present
  | streamFailure stream errors =>
      change key ∈ before.groupNodes.map (fun node => node.group.node.ref) at present
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamFailure]
      split <;> exact Or.inl present

-----------------------------------------------------------------------------------------
-- Accepted incoming tasks instantiate the more general unsettled-task classification
-----------------------------------------------------------------------------------------

/-- Every live registration owner of an accepted incoming task survives the actual handler
or lies below an emitted failure in its exact cleanup view.
-/
def GeneratedIncomingTaskOwnerProgress : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (task : Task),
        let before := ((State.initialize work).runNormalized inputs).1.queue
        let snapshot := registrationSnapshot before event
        let reduced := before.handleGraphEvent event
        task ∈ acceptedChildTasks before event
        → ∀ key ∈ task.groups.map DeliveryNode.ref,
            key ∈ snapshot.groupNodes.map (fun node => node.group.node.ref)
            → key ∈ reduced.1.groupNodes.map (fun node => node.group.node.ref)
              ∨ ∃ root ∈ failureRoots reduced.2,
                  (failurePruningView before event reduced.2).LiveDescendant root key

/-- Structural producer freshness supplies the unsettled domain without caller invariants. -/
theorem GeneratedIncomingTaskOwnerProgress_holds
    : GeneratedIncomingTaskOwnerProgress := by
  intro work inputs event generated valid started task
  dsimp only
  intro returned
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have notSettled : task.occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten := by
    intro processed
    exact acceptedChildTask_unsettled matching prior fresh returned
      (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities _ processed)
  have notRecorded : task.occurrence ∉ event.recordTaskOutcome
      (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) := by
    have child := acceptedChildTasks_subset _ _ returned
    cases event with
    | taskSuccess incoming result =>
        intro member
        rcases List.mem_cons.mp member with same | old
        · exact matching.childTasks_not_success child
            (by simp only [ReferenceWorkQueue.GraphEvent.successes, List.mem_singleton]; exact same)
        · exact notSettled old
    | streamItems => exact notSettled
    | taskFailure | streamSuccess | streamFailure => cases child
  exact GeneratedUnsettledTaskOwnerProgress_holds work inputs event generated valid
    started task (registrationSnapshot_acceptedTask_registered returned) notRecorded

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
