import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IncomingTaskOwners
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskFailureProgress

/-! Generated task-resource progress follows the actual registration, settlement and drain
phases. Pending accounting and exact descriptors are derived from the unchanged source laws.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)
open ReferenceWorkQueue (Task)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

private theorem registeredTask_exact {queue : ReferenceWorkQueue.State} {work task}
    (matching : queue.RegisteredTasksMatch work) (member : task ∈ queue.tasks)
    : queue.task? task.occurrence = some task := by
  cases found : queue.task? task.occurrence with
  | none => exact False.elim ((List.find?_eq_none.mp found task member)
      ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mpr rfl))
  | some canonical =>
      have same : canonical.occurrence = task.occurrence :=
        (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp
          (List.find?_some (p := fun candidate : Task => candidate.occurrence == task.occurrence) found)
      have groups := (matching canonical (List.mem_of_find?_eq_some found)).2
      rw [same] at groups
      have sameGroups := Option.some.inj (groups.symm.trans (matching task member).2)
      have equal : canonical = task := by
        cases canonical; cases task; cases same; cases sameGroups; rfl
      exact congrArg some equal

private theorem taskRepresented {queue : ReferenceWorkQueue.State} {task : Task}
    (links : queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref))
    (owned : ∃ owner ∈ task.groups, ∃ group, queue.groupNode? owner.ref = some group)
    (prior : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    : RecordTargetRepresented queue (.task task.occurrence) := by
  obtain ⟨owner, member, group, found⟩ := owned
  exact .task found (links group (List.mem_of_find?_eq_some found)
    (List.mem_map.mpr ⟨owner, member, (ReferenceWorkQueue.State.groupNode?_ref found).symm⟩)) prior.unrejected_lookup

private theorem ownerFromKey {queue : ReferenceWorkQueue.State} {key : Nat}
    (present : key ∈ queue.groupNodes.map (fun group => group.group.node.ref))
    : ∃ group, queue.groupNode? key = some group := by
  cases found : queue.groupNode? key with
  | some group => exact ⟨group, rfl⟩
  | none => exact False.elim ((queue.groupNode?_eq_none_iff key).mp found present)

private theorem cleanupTask_effect {effects : List HostEffect} {occurrence}
    (listed : CleanupTarget.task occurrence ∈ effects.filterMap HostEffect.cleanupStart?)
    : .abortTask occurrence ∈ effects := by
  obtain ⟨effect, emitted, identifies⟩ := List.mem_filterMap.mp listed
  cases effect with
  | abortTask other =>
      cases CleanupTarget.task.inj (Option.some.inj identifies); exact emitted
  | adopt | acknowledge | cancelSource | abortStreamQueue | responseFinished =>
      cases identifies

-----------------------------------------------------------------------------------------
-- Construct every actual handler phase from original generated source prefixes
-----------------------------------------------------------------------------------------

/-- Every owned prepared task still unsettled after this input retains a concrete record
or receives an abort from the actual dispatch. Includes incoming and previously registered
tasks, even when no computation node has been created.
-/
theorem generatedPreparedTask_progress {work inputs event task}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    (registered
      : task
        ∈ (registrationSnapshot
            ((State.initialize work).runNormalized inputs).1.queue event).tasks)
    (pending
      : task.occurrence
        ∉ event.recordTaskOutcome
            (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten))
    (owned
      : ∃ owner ∈ task.groups,
          ∃ group,
            (registrationSnapshot
              ((State.initialize work).runNormalized inputs).1.queue event).groupNode?
              owner.ref
            = some group)
    : let before := ((State.initialize work).runNormalized inputs).1
      let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
      RecordTargetRepresented reduced.state.queue (.task task.occurrence)
      ∨ .abortTask task.occurrence ∈ reduced.effects := by
  let before := ((State.initialize work).runNormalized inputs).1
  let queue := before.queue
  let snapshot := registrationSnapshot queue event
  let settled := ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨raw, priorStarted, accepted⟩ := generatedReplay_beforeNext generated valid started
  change queue = _ at raw
  have accounted := generatedReplay_nextAccounting generated valid started
  have evidence := GeneratedSnapshotTaskEvidence_holds work inputs event generated valid priorStarted
  have notSettled : task.occurrence ∉ settled := by
    intro member
    apply pending
    cases event with
    | taskSuccess | taskFailure => exact List.mem_cons_of_mem _ member
    | streamItems | streamSuccess | streamFailure => exact member
  have priorUnrejected : queue.TaskRejectionsSatisfy
      (fun rejected _ => rejected ≠ task.occurrence) := by
    rw [raw]
    exact (ReferenceWorkQueue.createWorkQueue_replay_taskRejections work inputs.flatten).mono
      (fun occurrence _ member same => notSettled (same ▸ member))
  have links := generatedSnapshot_unsettledLinks generated valid started task registered notSettled
  have catalogue := registeredTask_exact evidence.matching registered
  change snapshot.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref) at links
  change snapshot.task? task.occurrence = some task at catalogue
  change ∃ owner ∈ task.groups, ∃ group, snapshot.groupNode? owner.ref = some group at owned
  have canonical := generatedReplay_beforeNextState generated valid started
  change before = { queue := queue } at canonical
  change RecordTargetRepresented (before.handleGraphEvent event).1.queue (.task task.occurrence)
    ∨ .abortTask task.occurrence ∈ (before.handleGraphEvent event).2.2
  rw [canonical]
  cases event with
  | taskSuccess incoming result =>
      cases found : queue.taskNode? incoming with
      | none =>
          simp only [snapshot, registrationSnapshot, found] at links owned
          simp only [State.handleGraphEvent, State.taskSuccess, found]
          exact .inl (taskRepresented links owned priorUnrejected)
      | some input =>
          let native : State := { queue }
          let stored : State := { native with queue := queue.putTaskNode { input with value := some result.value } }
          let integrated := stored.maybeIntegrateWork result.work (some incoming)
          let released := input.task.groups.foldl ReferenceWorkQueue.successGroupStep (integrated.1.queue, [], {})
          let active := taskSuccessReadyPhase native incoming result input
          have prepared : snapshot = integrated.1.queue := by
            simp only [snapshot, registrationSnapshot, found]; rfl
          have inputFresh : incoming ∉ settled := fun member => fresh.2.2.1 incoming
            List.mem_cons_self (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities _ member)
          have debt := taskSuccess_registrationDebt accounted matching found inputFresh
          change snapshot.PendingDebtBound (fun _ => True) (incoming :: settled)
            (input.task.groups.map DeliveryNode.ref) at debt
          have keys : integrated.1.queue.GroupRefsUnique := prepared ▸ evidence.keys
          rw [prepared] at debt links catalogue owned
          have uniqueOwners := accounted.matching.contributorsNodup generated
            (accounted.started input (List.mem_of_find?_eq_some found))
          have folded := successGroupFold_unsettledOwners keys links pending
            input.task.groups uniqueOwners debt
          have groupCore : active.1.queue.groupNodes = released.1.groupNodes :=
            State.startNewWork_groupNodes { integrated.1 with queue := released.1 } released.2.2 integrated.2
          have readyLinks : active.1.queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref) := by
            simpa only [ReferenceWorkQueue.State.TaskLinkedOn, groupCore] using folded.1
          have readyBound : active.1.queue.PendingBound (fun _ => True) (incoming :: settled) := by
            simpa only [ReferenceWorkQueue.State.PendingBound, groupCore,
              ReferenceWorkQueue.GraphEvent.recordTaskOutcome]
              using folded.2.2
          have readyOwned : ∃ owner ∈ task.groups, ∃ group, active.1.queue.groupNode? owner.ref = some group := by
            obtain ⟨owner, member, group, lookup⟩ := owned
            refine ⟨owner, member, ?_⟩
            apply ownerFromKey
            rw [groupCore]
            exact folded.2.1 owner.ref (List.mem_map_of_mem member)
              (List.mem_map.mpr ⟨group, List.mem_of_find?_eq_some lookup,
                ReferenceWorkQueue.State.groupNode?_ref lookup⟩)
          have readyCatalogue : active.1.queue.task? task.occurrence = some task := by
            change (({ integrated.1 with queue := released.1 }).startNewWork
              released.2.2 integrated.2).1.queue.tasks.find? _ = some task
            rw [(State.startNewWork_catalogues { integrated.1 with queue := released.1 }
              released.2.2 integrated.2).1, successGroupFold_tasks]
            exact catalogue
          have sourceFound : ReferenceWorkQueue.State.taskNode?
              ((ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents inputs.flatten)
              incoming = some input := by rw [← raw]; exact found
          have phase : active.1.queue = referenceTaskSuccessReady queue incoming result input := by
            change (taskSuccessReadyPhase { queue } incoming result input).1.queue = _
            rw [raw]
            exact referencePrefix_taskSuccess_readyProjection generated inputs.flatten incoming result valid accepted input sourceFound
          obtain ⟨parents, frame, forest⟩ := referencePrefix_taskSuccess_drainFrames
            generated inputs.flatten incoming result valid accepted input sourceFound
          rw [← raw, ← phase] at frame forest
          have running : active.1.stopped = false := taskSuccessReadyPhase_stopped native incoming result input
          have unique : active.2.2.Nodup := State.startNewWork_targets_nodup _ _ _ [] List.nodup_nil
          have storedUnrejected : stored.queue.TaskRejectionsSatisfy
              (fun rejected _ => rejected ≠ task.occurrence) :=
            priorUnrejected.putTaskNode _ (priorUnrejected input (List.mem_of_find?_eq_some found))
          have integratedUnrejected := State.maybeIntegrateWork_taskRejections storedUnrejected
            result.work (some incoming)
          have readyUnrejected : active.1.queue.TaskRejectionsSatisfy
              (fun rejected _ => rejected ≠ task.occurrence) :=
            State.startNewWork_taskRejections
              (integratedUnrejected.successGroupFold input.task.groups) _ _ _
          have classified := FusedUnsettledDrainProgress_holds active.1 work parents (incoming :: settled)
            task active.2.2 running frame forest readyCatalogue readyLinks readyBound pending readyOwned unique readyUnrejected
          simp only [State.handleGraphEvent]
          rw [State.taskSuccess_eq native incoming result input found]
          rcases classified with retained | aborted
          · exact .inl retained
          · exact .inr (List.mem_append_right _ aborted)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simp only [snapshot, registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] at links owned
          simp only [State.handleGraphEvent, State.streamItems, active, Bool.not_false, ↓reduceIte]
          exact .inl (taskRepresented links owned priorUnrejected)
      | true =>
          let acc := items.foldl streamRegistrationStep (({ queue } : State), [], [], [], [], [])
          have prepared : snapshot = acc.1.queue := registrationSnapshot_itemFold queue stream items active
          rw [prepared] at links catalogue owned
          have fold := referencePrefix_streamRegistrationFold generated inputs.flatten
            (fun event member => prior.eachMatches member) stream items matching
          have queueEq : acc.1.queue = queue.preparedStreamItems items := by
            change (items.foldl streamRegistrationStep (({ queue } : State), [], [], [], [], [])).1.queue = _
            rw [raw]; exact congrArg Prod.fst fold
          obtain ⟨parents, frame, forest⟩ := referencePrefix_streamItems_drainFrames
            generated inputs.flatten prior accepted stream items matching
          rw [← raw, ← queueEq] at frame forest
          have bounded : acc.1.queue.PendingBound (fun _ => True) settled := by
            rw [queueEq]; exact preparedStreamItems_pendingBound accounted matching
          have running : acc.1.stopped = false := streamRegistrationFold_stopped items _
          have unique := (streamRegistrationFold_cleanupTargets items
            (({ queue } : State), [], [], [], [], []) List.nodup_nil rfl).1
          have readyUnrejected : acc.1.queue.TaskRejectionsSatisfy
              (fun rejected _ => rejected ≠ task.occurrence) := by
            rw [queueEq]
            exact ReferenceWorkQueue.State.preparedStreamItems_preserves
              (fun current => current.TaskRejectionsSatisfy
                (fun rejected _ => rejected ≠ task.occurrence))
              priorUnrejected items
              (fun _ item _ prior =>
                ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
          have classified := FusedUnsettledDrainProgress_holds acc.1 work parents settled task
            acc.2.2.2.2.1 running frame forest catalogue links bounded pending owned unique readyUnrejected
          simp only [State.handleGraphEvent]
          rcases classified with retained | aborted
          · simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact .inl retained
          · apply Or.inr
            apply cleanupTask_effect
            rw [State.streamItems_cleanupStarts_eq { queue } stream items active]
            have listed : CleanupTarget.task task.occurrence ∈
                ((acc.1.drainReadyGroups acc.2.2.2.2.1).2.2.flatMap CleanupTarget.effects).filterMap
                  HostEffect.cleanupStart? :=
              List.mem_filterMap.mpr ⟨HostEffect.abortTask task.occurrence, aborted, rfl⟩
            simpa only [cleanupEffects_starts] using listed
  | taskFailure failed errors =>
      have different : task.occurrence ≠ failed := fun same => pending (same ▸ List.mem_cons_self)
      have frame := generated.replayGraphEvents_taskOwnerFrame inputs.flatten prior accepted
      obtain ⟨parents, forest⟩ := referencePrefix_removalForest generated inputs.flatten
        (fun event member => prior.eachMatches member)
      rw [← raw] at frame forest
      exact State.taskFailure_unsettledTask (state := { queue }) frame forest failed errors task
        different catalogue links owned priorUnrejected
  | streamSuccess stream =>
      simp only [snapshot, registrationSnapshot] at links owned
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.streamSuccess]
      split <;> exact .inl (taskRepresented links owned priorUnrejected)
  | streamFailure stream errors =>
      simp only [snapshot, registrationSnapshot] at links owned
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.streamFailure]
      split <;> exact .inl (taskRepresented links owned priorUnrejected)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
