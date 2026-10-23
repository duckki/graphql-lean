import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IncomingTaskRegistration
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
  exact generatedReplay_pendingAccounting generated valid started

/-- Matching item work preserves the pending lower bound at actual pre-drain preparation. -/
theorem preparedStreamItems_pendingBound {queue : Kernel} {work settled stream items}
    (accounted : queue.PendingAccounting work settled)
    (matching : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.preparedStreamItems items available).PendingBound (fun _ => True)
        settled := by
  let invariant (current : Kernel) := current.PendingBound (fun _ => True) settled
    ∧ current.GroupRefsUnique ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
  suffices invariant (queue.preparedStreamItems items available) from this.1
  apply ReferenceWorkQueue.State.preparedStreamItems_preserves invariant
    ⟨accounted.pending, accounted.refs, accounted.liveGroups, accounted.taskGroups⟩ items
    available
  intro current item member prior
  have registered := current.maybeIntegrateWork_registration prior.2.2.1 prior.2.2.2
    item.work (by
      intro task listed ref contributes
      exact .inr (matching.streamItem_childTasksCovered accounted.registration.source
        member task listed ref contributes))
  have pruned := ReferenceWorkQueue.State.pruneEmptyGroups_registration registered.1 registered.2.1
    (current.maybeIntegrateWork item.work).2.newGroups
  exact ⟨
    ((prior.1.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available,
    ((prior.2.1.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _
      available,
    ReferenceWorkQueue.State.startNewWork_registration pruned.1 pruned.2.1 _ available
  ⟩

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
              ∨ ∃ root ∈
                  failureRoots reduced.2.1
                  ++ reduced.2.2.map (fun failure => failure.group.ref),
                  (failurePruningView before event reduced.2.1).LiveDescendant root key

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
  let eager := eagerRegistrationSnapshot before event
  let settled := ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten
  change key ∈ (before.handleGraphEvent event).1.groupNodes.map (fun node => node.group.node.ref)
    ∨ ∃ root ∈ failureRoots (before.handleGraphEvent event).2.1
        ++ (before.handleGraphEvent event).2.2.map (fun failure => failure.group.ref),
      (failurePruningView before event (before.handleGraphEvent event).2.1).LiveDescendant root key
  obtain ⟨_, priorStarted, _⟩ := generatedReplay_beforeNext generated valid started
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have accounted := generatedReplay_pendingAccounting generated valid started
  have projection := generatedSnapshot_projection generated valid priorStarted
  have frame := generatedEagerSnapshot_taskEvidence generated valid priorStarted
  obtain ⟨parents, forest, _⟩ := generatedSnapshot_removalForest generated valid priorStarted
  have notSettled : task.occurrence ∉ settled := by
    intro processed
    apply pending
    cases event with
    | taskSuccess | taskFailure => exact List.mem_cons_of_mem _ processed
    | streamItems | groupFailure | streamSuccess | streamFailure => exact processed
  have actualLinks := generatedSnapshot_unsettledLinks generated valid started task registered
    notSettled
  change snapshot.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref) at actualLinks
  have groups := congrArg ReferenceWorkQueue.State.groupNodes projection.core
  change snapshot.groupNodes = eager.groupNodes at groups
  have registry := congrArg ReferenceWorkQueue.State.registeredGroups projection.core
  change snapshot.registeredGroups = eager.registeredGroups at registry
  have links : eager.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref) := by
    simpa only [ReferenceWorkQueue.State.TaskLinkedOn, groups] using actualLinks
  have eagerForest : eager.RemovalForest parents :=
    forest.of_subset (by rw [← groups]; exact List.Subset.refl _)
  have eagerEdges : eager.GroupEdgesFrom snapshot := by
    intro key node lookup
    exact ⟨node, by simpa only [ReferenceWorkQueue.State.groupNode?, groups] using lookup, rfl⟩
  have eagerClosures : ReferenceWorkQueue.GroupClosureAccounting snapshot (eager, []) :=
    .silent
      (fun _ retired => by
        simpa only [ReferenceWorkQueue.State.RetiredGroup, groups, registry]
          using retired)
  have eagerPresent : key ∈ eager.groupNodes.map (fun node => node.group.node.ref) := by
    rwa [← groups]
  cases event with
  | taskSuccess incoming result =>
      cases found : before.taskNode? incoming with
      | none =>
          have beforePresent : key ∈ before.groupNodes.map (fun node => node.group.node.ref) := by
            simpa only [eager, eagerRegistrationSnapshot, found] using eagerPresent
          simp only [ReferenceWorkQueue.State.handleGraphEvent,
            ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
            ReferenceWorkQueue.State.taskSuccess, found]
          exact .inl beforePresent
      | some input =>
          have inputFresh : incoming ∉ settled := fun processed => fresh.2.2.1 incoming
            List.mem_cons_self (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities
              _ processed)
          have debt := taskSuccess_registrationDebt accounted matching found inputFresh
          change snapshot.PendingDebtBound (fun _ => True) (incoming :: settled)
            (input.task.groups.map DeliveryNode.ref) at debt
          have eagerDebt : eager.PendingDebtBound (fun _ => True) (incoming :: settled)
              (input.task.groups.map DeliveryNode.ref) := by
            simpa only [ReferenceWorkQueue.State.PendingDebtBound, groups] using debt
          have childFresh : task.occurrence ∉ incoming :: settled := pending
          have ownersUnique := accounted.matching.contributorsNodup generated
            (accounted.started input (List.mem_of_find?_eq_some found))
          have foldOwners := successGroupFold_unsettledOwners frame.keys links childFresh
            input.task.groups ownersUnique eagerDebt
          let folded := input.task.groups.foldl ReferenceWorkQueue.successGroupStep (eager, [], {})
          let startup := folded.1.startNewWork folded.2.2
          let drained := startup.1.drainReadyGroups
          obtain ⟨foldFrame, foldForest, foldEdges, foldClosures⟩ :=
            successGroupFold_releaseEvidence frame eagerForest input.task.groups
          have foldPresent := foldOwners.2.1 key contributes eagerPresent
          have foldLookup : ∃ owner, folded.1.groupNode? key = some owner := by
            cases lookup : folded.1.groupNode? key with
            | some owner => exact ⟨owner, rfl⟩
            | none =>
                exact False.elim (((folded.1.groupNode?_eq_none_iff key).mp lookup) foldPresent)
          have actualEdges := foldEdges.trans eagerEdges
          have actualClosures : ReferenceWorkQueue.GroupClosureAccounting snapshot
              (folded.1, folded.2.1) := by
            simpa only [List.nil_append] using eagerClosures.append foldClosures
          have handler : before.handleGraphEvent (.taskSuccess incoming result)
              = (drained.1, folded.2.1 ++ drained.2.1, startup.2 ++ drained.2.2) := by
            simp only [ReferenceWorkQueue.State.handleGraphEvent,
              ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
            rw [ReferenceWorkQueue.State.taskSuccess_eq incoming result input found]
            simp only [folded, startup, drained, eager, eagerRegistrationSnapshot, found]
          rcases ReferenceWorkQueue.State.startNewWork_ownerCut foldForest folded.2.2
              foldLookup with kept | cut
          · obtain ⟨owner, lookup⟩ := kept
            have startupPresent : key ∈ startup.1.groupNodes.map (fun node =>
              node.group.node.ref) :=
              List.mem_map.mpr ⟨owner, List.mem_of_find?_eq_some lookup,
                ReferenceWorkQueue.State.groupNode?_ref lookup⟩
            have startupEdges := (ReferenceWorkQueue.State.startNewWork_groupEdgesFrom
              folded.1 folded.2.2).trans actualEdges
            have startupClosures := actualClosures.post
              (fun _ retired => retired.startNewWork folded.2.2)
            rcases drain_unsettledTask_ownerCut (foldFrame.startNewWork folded.2.2)
                (foldForest.startNewWork folded.2.2) startupEdges startupClosures
                (foldOwners.1.startNewWork folded.2.2) (foldOwners.2.2.startNewWork folded.2.2)
                childFresh startup.1.groupNodes.length contributes startupPresent with retained
                  | cut
            · rw [handler]; exact .inl retained
            · obtain ⟨failure, queued, path⟩ := cut
              refine .inr ⟨failure.group.ref, ?_, ?_⟩
              · rw [handler]
                apply List.mem_append_right
                rw [List.map_append]
                exact List.mem_append_right _ (List.mem_map_of_mem queued)
              · rw [handler]; exact path
          · obtain ⟨failure, queued, path⟩ := cut
            refine .inr ⟨failure.group.ref, ?_, ?_⟩
            · rw [handler]
              apply List.mem_append_right
              rw [List.map_append]
              exact List.mem_append_left _ (List.mem_map_of_mem queued)
            · rw [handler]
              exact startupFailureBoundary_path folded.2.2 foldForest actualEdges actualClosures
                startup.1.groupNodes.length queued path
  | streamItems stream items =>
      cases active : before.rootStreams.contains stream.ref with
      | false =>
          have beforePresent : key ∈ before.groupNodes.map (fun node => node.group.node.ref) := by
            simpa only [eager, eagerRegistrationSnapshot, active, Bool.false_eq_true,
              ↓reduceIte]
              using eagerPresent
          simp only [ReferenceWorkQueue.State.handleGraphEvent,
            ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
            ReferenceWorkQueue.State.streamItems, active, Bool.not_false, ↓reduceIte]
          exact .inl beforePresent
      | true =>
          have counts : eager.PendingBound (fun _ => True) settled := by
            rw [show eager = before.preparedStreamItems items from
              eagerRegistrationSnapshot_streamItems before stream items active]
            exact preparedStreamItems_pendingBound accounted matching
          let prepared := items.foldl ReferenceWorkQueue.streamItemStep (before, [], [], [], [])
          let notice := WorkQueueEvent.streamValues stream prepared.2.2.2.1 prepared.2.1
            prepared.2.2.1
          have same : eager = prepared.1 := by
            simp only [eager, eagerRegistrationSnapshot, active, ↓reduceIte]; rfl
          have handler : before.handleGraphEvent (.streamItems stream items)
              = (eager.drainReadyGroups.1, notice :: eager.drainReadyGroups.2.1,
                  prepared.2.2.2.2 ++ eager.drainReadyGroups.2.2) := by
            simp only [ReferenceWorkQueue.State.handleGraphEvent,
              ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
              before.streamItems_eq stream items, active, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte]
            rw [← same]
          have closures : ReferenceWorkQueue.GroupClosureAccounting eager (eager, [notice]) := by
            refine ⟨?_, ?_, fun _ retired => retired, ?_⟩ <;>
              simp [notice, ReferenceWorkQueue.rawGroupClosureRefs]
          have actualClosures : ReferenceWorkQueue.GroupClosureAccounting snapshot
              (eager, [notice]) := by
            simpa only [List.nil_append] using eagerClosures.append closures
          rcases drain_unsettledTask_ownerCut frame eagerForest eagerEdges actualClosures links
            counts
              notSettled eager.groupNodes.length contributes eagerPresent with kept | cut
          · rw [handler]; exact .inl kept
          · obtain ⟨failure, queued, path⟩ := cut
            refine .inr ⟨failure.group.ref, ?_, ?_⟩
            · rw [handler]
              apply List.mem_append_right
              rw [List.map_append]
              exact List.mem_append_right _ (List.mem_map_of_mem queued)
            · rw [handler]; exact path
  | taskFailure failed errors =>
      have beforePresent : key ∈ before.groupNodes.map (fun node => node.group.node.ref) := by
        simpa only [eager, eagerRegistrationSnapshot] using eagerPresent
      have beforeForest : before.RemovalForest parents := by
        simpa only [eager, eagerRegistrationSnapshot] using eagerForest
      have handler : before.handleGraphEvent (.taskFailure failed errors)
          = ((before.taskFailure failed errors).1, (before.taskFailure failed errors).2, []) := by
        simp only [ReferenceWorkQueue.State.handleGraphEvent,
          ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
      have unpublished : publicationRoots (before.taskFailure failed errors).2 = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro key member
        obtain ⟨group, groups, streams, emitted, _⟩ := mem_publicationRoots.mp member
        exact before.taskFailure_noGroupSuccess failed errors group groups streams emitted
      by_cases cut : ∃ root ∈ failureRoots (before.taskFailure failed errors).2,
          (failurePruningView before (.taskFailure failed errors)
            (before.taskFailure failed errors).2).LiveDescendant root key
      · rw [handler]
        simpa only [List.map_nil, List.append_nil] using Or.inr cut
      · have live : ∃ node, before.groupNode? key = some node := by
          cases found : before.groupNode? key with
          | some node => exact ⟨node, rfl⟩
          | none =>
              exact False.elim ((before.groupNode?_eq_none_iff key).mp found beforePresent)
        have keys : before.GroupRefsUnique := by
          simpa only [eager, eagerRegistrationSnapshot] using frame.keys
        obtain ⟨node, found⟩ := taskFailure_outside_survives keys beforeForest failed errors live
          (by intro root emitted path
              exact cut ⟨root, emitted, failurePruningView_pathFrom (.refl before) path
                (by intros; simp [unpublished])⟩)
        rw [handler]
        exact .inl (List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found,
          ReferenceWorkQueue.State.groupNode?_ref found⟩)
  | groupFailure failure =>
      have beforePresent : key ∈ before.groupNodes.map (fun node => node.group.node.ref) := by
        simpa only [eager, eagerRegistrationSnapshot] using eagerPresent
      apply Or.inl
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
        ReferenceWorkQueue.State.groupFailure]
      split
      · exact beforePresent
      · split <;> exact beforePresent
  | streamSuccess stream =>
      have beforePresent : key ∈ before.groupNodes.map (fun node => node.group.node.ref) := by
        simpa only [eager, eagerRegistrationSnapshot] using eagerPresent
      apply Or.inl
      cases active : before.rootStreams.contains stream.ref
      <;> simpa only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
        ReferenceWorkQueue.State.streamSuccess, active, Bool.false_eq_true, ↓reduceIte]
        using beforePresent
  | streamFailure stream errors =>
      have beforePresent : key ∈ before.groupNodes.map (fun node => node.group.node.ref) := by
        simpa only [eager, eagerRegistrationSnapshot] using eagerPresent
      apply Or.inl
      cases active : before.rootStreams.contains stream.ref
      <;> simpa only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
        ReferenceWorkQueue.State.streamFailure, active, Bool.false_eq_true, ↓reduceIte]
        using beforePresent

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
              ∨ ∃ root ∈
                  failureRoots reduced.2.1
                  ++ reduced.2.2.map (fun failure => failure.group.ref),
                  (failurePruningView before event reduced.2.1).LiveDescendant root key

/-- Structural producer freshness supplies the unsettled domain without caller invariants. -/
theorem GeneratedIncomingTaskOwnerProgress_holds
    : GeneratedIncomingTaskOwnerProgress := by
  intro work inputs event generated valid started task
  dsimp only
  intro returned
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have notSettled : task.occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements
    inputs.flatten := by
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
    | taskFailure | groupFailure | streamSuccess | streamFailure => cases child
  exact GeneratedUnsettledTaskOwnerProgress_holds work inputs event generated valid
    started task (registrationSnapshot_acceptedTask_registered returned) notRecorded

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
