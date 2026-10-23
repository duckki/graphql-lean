import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.UnsettledTaskProgress

/-! Existing unfinished computation leases retain real records or receive an actual abort.
The domain uses the same observed task-completion history, not completed buffer contents.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Accepted registration retains old descriptors and unfinished live owners
-----------------------------------------------------------------------------------------

/-- Registration only appends permanent task descriptors, across all input kinds. -/
theorem registrationSnapshot_oldTasks_available (queue : Kernel) (event : GraphEvent)
    (available : List (Occurrence × Nat))
    : queue.tasks.Subset (registrationSnapshot queue event available).tasks := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none =>
          simpa only [registrationSnapshot, found]
            using (show queue.tasks.Subset queue.tasks from fun _ member => member)
      | some node =>
          simp only [registrationSnapshot, found,
            State.maybeIntegrateWork_tasks, ReferenceWorkQueue.State.putTaskNode]
          exact fun _ member => List.mem_append_left _ member
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [registrationSnapshot, active, Bool.false_eq_true,
            ↓reduceIte] using (show queue.tasks.Subset queue.tasks from fun _ member => member)
      | true =>
          rw [registrationSnapshot_itemFold queue stream items active available,
            streamRegistrationFold_tasks _ _ available]
          exact List.subset_append_left _ _
  | taskFailure | groupFailure | streamSuccess | streamFailure =>
      exact fun _ member => member

/-- Empty-snapshot specialization for the established eventwise catalogue interface. -/
theorem registrationSnapshot_oldTasks (queue : Kernel) (event : GraphEvent)
    : queue.tasks.Subset (registrationSnapshot queue event).tasks :=
  registrationSnapshot_oldTasks_available queue event []

/-- Registration keeps an old unsettled task owner or emits that task’s actual abort.
The item fold may remove owners during cached startup; its cleanup is retained explicitly.
-/
theorem registrationSnapshot_unsettledTask_progress {queue : Kernel} {work settled task}
    (accounted : queue.PendingAccounting work settled) (registered : task ∈ queue.tasks)
    (pending : task.occurrence ∉ settled)
    (owned : ∃ owner ∈ task.groups, ∃ group, queue.groupNode? owner.ref = some group)
    (rejections : queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    (cached : queue.cacheTaskFailures available = queue := by rfl)
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ settled := by
        intro occurrence errors member; cases member)
    : (∃ owner ∈ task.groups,
        ∃ group,
          (registrationSnapshot queue event available).groupNode? owner.ref = some group)
      ∨ .abortTask task.occurrence
        ∈ (({ queue } : State).handleGraphEvent event available).2.2.1 := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [registrationSnapshot, found] using Or.inl owned
      | some node =>
          left
          obtain ⟨owner, member, group, lookup⟩ := owned
          have present : owner.ref ∈ queue.groupNodes.map (fun node => node.group.node.ref) :=
            List.mem_map.mpr ⟨group, List.mem_of_find?_eq_some lookup,
              ReferenceWorkQueue.State.groupNode?_ref lookup⟩
          have retained : owner.ref ∈ (registrationSnapshot queue
              (.taskSuccess occurrence result) available).groupNodes.map
                (fun node => node.group.node.ref) := by
            simp only [registrationSnapshot, found]
            exact State.maybeIntegrateWork_includesRefs _ result.work (some occurrence) present
          refine ⟨owner, member, ?_⟩
          cases lookup
                : (registrationSnapshot queue (.taskSuccess occurrence result)
                    available).groupNode?
                    owner.ref with
          | some group => exact ⟨group, rfl⟩
          | none =>
              exact False.elim (((ReferenceWorkQueue.State.groupNode?_eq_none_iff _ _).mp lookup)
                retained)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte]
            using Or.inl owned
      | true =>
          have frame : SourceRegistrationFrame queue settled work :=
            ⟨⟨accounted.refs, accounted.liveGroups, accounted.taskGroups, accounted.links⟩,
              accounted.matching, accounted.sound⟩
          have childMatching : ∀ item ∈ items, ∀ task ∈ item.work.tasks,
              ReferenceWorkQueue.TaskMatches work task := by
            intro item member task listed
            obtain ⟨address, payload, same, known⟩ :=
              matching.streamItem_childTask_producer member listed
            exact ⟨⟨address, payload, some item.occurrence, same, known⟩,
              matching.streamItem_childTask_groupsExact member listed⟩
          rcases streamRegistrationFold_existingTask_progress items
              (({ queue } : State), [], [], [], [], [], []) frame
              (fun item member => matching.streamItem_childTasksCovered accounted.registration.source member)
              childMatching registered
              pending owned rejections rfl List.nodup_nil available licensed with kept | requested
          · left
            rwa [registrationSnapshot_itemFold queue stream items active available]
          · right
            simp only [State.handleGraphEvent, cached]
            exact streamItems_target_aborted_available active available requested
  | taskFailure | groupFailure | streamSuccess | streamFailure => exact .inl owned

-----------------------------------------------------------------------------------------
-- Existing pending records progress across every generated handler
-----------------------------------------------------------------------------------------

/-- Existing task records progress at an actual exposed source cut with full-batch failure
exclusions. The consumed ledger still licenses the input's settlement; the larger set only
identifies the tracked computation that must remain unfinished throughout this batch.
-/
theorem sourceFrame_existingTask_progress_available {queue : Kernel}
    {work parents before event excluded occurrence}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (source : ReferenceWorkQueue.UncancelledReplayFrame queue work parents before)
    (accounted
      : queue.PendingAccounting work
          (ReferenceWorkQueue.GraphEvent.taskSettlements before))
    (keys : queue.TaskNodeKeysUnique)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ [event]))
    (included
      : (event.recordTaskOutcome
          (ReferenceWorkQueue.GraphEvent.taskSettlements before)).Subset
          excluded)
    (rejections : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ∈ excluded))
    (available : List (Occurrence × Nat))
    (cached : queue.cacheTaskFailures available = queue)
    (licensed : ∀ rejected errors, (rejected, errors) ∈ available → rejected ∈ excluded)
    (represented : RecordTargetRepresented queue (.task occurrence))
    (pending : occurrence ∉ excluded)
    : let reduced := ({ queue } : State).handleGraphEvent event available
      RecordTargetRepresented reduced.1.queue (.task occurrence)
      ∨ .abortTask occurrence ∈ reduced.2.2.1 := by
  obtain ⟨_, matched, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have earlier
      : (ReferenceWorkQueue.GraphEvent.taskSettlements before).Subset excluded := by
    intro target member
    apply included
    cases event with
    | taskSuccess | taskFailure => exact List.mem_cons_of_mem _ member
    | streamItems | groupFailure | streamSuccess | streamFailure => exact member
  cases represented with
  | @task key occurrence group found linked _ =>
      obtain ⟨task, member, same, contributes⟩ := accounted.sound group
        (List.mem_of_find?_eq_some found) occurrence linked
      have taskFresh : task.occurrence ∉ excluded := by simpa only [← same] using pending
      obtain ⟨owner, ownerMember, ownerKey⟩ := List.mem_map.mp contributes
      have initialOwned : ∃ owner ∈ task.groups, ∃ node,
          queue.groupNode? owner.ref = some node := by
        refine ⟨owner, ownerMember, group, ?_⟩
        rw [ownerKey, ReferenceWorkQueue.State.groupNode?_ref found]
        exact found
      rcases registrationSnapshot_unsettledTask_progress
          (pendingAccounting_weakenSettled accounted earlier) member taskFresh initialOwned
          rejections event matched available cached licensed with owned | aborted
      · have unrejected : queue.TaskRejectionsSatisfy
            (fun rejected _ => rejected ≠ task.occurrence) :=
          rejections.mono (fun rejected _ member same => taskFresh (same ▸ member))
        have inputPending : task.occurrence ∉ event.recordTaskOutcome
            (ReferenceWorkQueue.GraphEvent.taskSettlements before) :=
          fun member => taskFresh (included member)
        have progress := sourceFrame_preparedTask_progress_available generated canonical source
          accounted keys valid available cached unrejected
          (fun rejected errors member same => taskFresh (same ▸ licensed rejected errors member))
          (registrationSnapshot_oldTasks_available queue event available member) inputPending owned
        simpa only [← same] using progress
      · exact .inr (by simpa only [← same] using aborted)

/-- A pre-handler task membership still unsettled after this input is represented at the
actual endpoint or aborted there. Completion history excludes legitimately removed buffers.
-/
def GeneratedRepresentedUnsettledTaskProgress : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ occurrence,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        RecordTargetRepresented before.queue (.task occurrence)
        → occurrence
          ∉ event.recordTaskOutcome
              (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten)
        → RecordTargetRepresented reduced.state.queue (.task occurrence)
          ∨ .abortTask occurrence ∈ reduced.effects

/-- Membership soundness identifies the old descriptor. Registration retains an owner
or emits an abort; the prepared-task theorem completes the owner-preserving branch.
-/
theorem GeneratedRepresentedUnsettledTaskProgress_holds
    : GeneratedRepresentedUnsettledTaskProgress := by
  intro work inputs event generated valid started occurrence
  dsimp only
  intro represented pending
  let before := ((State.initialize work).runNormalized inputs).1
  let queue := before.queue
  let settled := ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have source := generatedReplay_sourceFrame generated canonical valid started
  have accounted := generatedReplay_nextAccounting generated valid started
  have keys : queue.TaskNodeKeysUnique := by
    obtain ⟨raw, _, _⟩ := generatedReplay_beforeNext generated valid started
    change ((State.initialize work).runNormalized inputs).1.queue.TaskNodeKeysUnique
    rw [raw, ← ReferenceWorkQueue.State.runNormalized_replayBatches]
    exact (ReferenceWorkQueue.createWorkQueue_taskNodeKeysUnique
      (ReferenceWorkQueue.Work.fromExecution work)).runNormalized inputs
  have rejections : queue.TaskRejectionsSatisfy
      (fun rejected _ => rejected ∈ event.recordTaskOutcome settled) := by
    refine (generatedReplay_taskRejections generated valid started).mono
      (after := fun rejected _ => rejected ∈ event.recordTaskOutcome settled) ?_
    intro rejected errors member
    cases event with
    | taskSuccess | taskFailure => exact List.mem_cons_of_mem _ member
    | streamItems | groupFailure | streamSuccess | streamFailure => exact member
  have canonicalState := generatedReplay_beforeNextState generated valid started
  change before = { queue := queue } at canonicalState
  change let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
    RecordTargetRepresented reduced.state.queue (.task occurrence)
      ∨ .abortTask occurrence ∈ reduced.effects
  rw [canonicalState]
  have progress := sourceFrame_existingTask_progress_available generated canonical source accounted
    keys valid (List.Subset.refl _) rejections [] rfl
    (by intro rejected errors member; cases member) represented pending
  dsimp only [GraphBatchResult.handleGraphEvent]
  rcases progress with retained | aborted
  · exact .inl (retained.withGroupFailures _)
  · exact .inr (List.mem_append_right _ aborted)

-----------------------------------------------------------------------------------------
-- The independent resource observer keeps the same pending completion history
-----------------------------------------------------------------------------------------

/-- Queue-owned computation leases have a current membership and no processed task outcome.
This is a before-state/history invariant, not an endpoint or cleanup-effect assumption.
-/
def TasksPendingRepresented (queue : Kernel) (settled : List Occurrence)
    (resources : ResourceState)
    : Prop :=
  ∀ occurrence,
    resources (.task occurrence) = .owned .queue
    → RecordTargetRepresented queue (.task occurrence) ∧ occurrence ∉ settled

/-- An existing queue lease still owned after dispatch survived normal completion.
Adoption cannot reacquire it under another producer or resurrect a released lease.
-/
theorem ResourceState.observeDispatch_existingQueueOwned_survivesCompletion
    (resources : ResourceState) (inventories : ProducerInventories) (before : State)
    (event : GraphEvent) (target : CleanupTarget)
    (initial : resources target = .owned .queue)
    (owned
      : (resources.observeDispatch inventories before event).1 target = .owned .queue)
    : (resources.observeNormalCompletion before.queue event).1 target
      = .owned .queue := by
  obtain ⟨adopted, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ target owned
  rcases ResourceState.observeAdoptions_queueOwned_origin _ _ _ target adopted
      with earlier | transferred
  · exact earlier
  · obtain ⟨producer, _, _, lease⟩ := transferred
    have original := resources.observeNormalCompletion_owned_origin _ _ target
      (.producer producer) lease
    rw [initial] at original
    cases original

/-- A task still owned after normal completion cannot be this input's settled identity.
Together with prior unsettledness this updates the same history invariant for all inputs.
-/
theorem ResourceState.observeNormalCompletion_taskUnsettled (resources : ResourceState)
    (before : Kernel) (event : GraphEvent) (occurrence : Occurrence)
    (settled : List Occurrence) (pending : occurrence ∉ settled)
    (owned
      : (resources.observeNormalCompletion before event).1 (.task occurrence)
        = .owned .queue)
    : occurrence ∉ event.recordTaskOutcome settled := by
  cases event with
  | taskSuccess incoming result =>
      intro member
      rcases List.mem_cons.mp member with same | earlier
      · subst incoming
        exact resources.finishQueueTarget_not_owned (.task occurrence) owned
      · exact pending earlier
  | taskFailure failed errors =>
      intro member
      rcases List.mem_cons.mp member with same | earlier
      · subst failed
        exact resources.finishQueueTarget_not_owned (.task occurrence) owned
      · exact pending earlier
  | streamItems | groupFailure | streamSuccess | streamFailure => exact pending

/-- Still-owned existing pending leases retain records; completion/cancellation alternatives
are excluded by the actual observer, not assumed as successful ownership preservation.
-/
def GeneratedDispatchExistingTaskRepresentation : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories) occurrence,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        RecordTargetRepresented before.queue (.task occurrence)
        → occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten
        → resources (.task occurrence) = .owned .queue
        → (resources.observeDispatch inventories before event).1 (.task occurrence)
          = .owned .queue
        → RecordTargetRepresented reduced.state.queue (.task occurrence)

/-- Generated old-record progress and licensed completion/cleanup compose at one dispatch. -/
theorem GeneratedDispatchExistingTaskRepresentation_holds
    : GeneratedDispatchExistingTaskRepresentation := by
  intro work inputs event generated valid started resources inventories occurrence
  dsimp only
  intro represented pending initial owned
  let before := ((State.initialize work).runNormalized inputs).1
  have completed := resources.observeDispatch_existingQueueOwned_survivesCompletion
    inventories before event
    (.task occurrence) initial owned
  have unfinished := resources.observeNormalCompletion_taskUnsettled before.queue event
    occurrence _ pending completed
  rcases GeneratedRepresentedUnsettledTaskProgress_holds work inputs event generated valid started
      occurrence represented unfinished with kept | aborted
  · exact kept
  · obtain ⟨_, absent⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.task occurrence) owned
    exact False.elim (absent (List.mem_filterMap.mpr ⟨.abortTask occurrence, aborted, rfl⟩))

-----------------------------------------------------------------------------------------
-- Construct the dispatch-wide task invariant for old and newly adopted leases
-----------------------------------------------------------------------------------------

/-- Every still-owned task has a real endpoint membership and remains unsettled in the
same input history. Native identity mapping covers incoming leases, not desired coverage.
-/
def GeneratedDispatchTasksPendingRepresented : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories),
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        TasksPendingRepresented before.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) resources
        → ProducerTasksMatchWork work resources inventories
            (graphEffects before.queue event)
        → TasksPendingRepresented reduced.state.queue
            (event.recordTaskOutcome
              (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten))
            (resources.observeDispatch inventories before event).1

/-- Inspect actual ownership origin once, then use old-record or structural incoming-task
construction. This preserves the genuine completion-history invariant without a new law.
-/
theorem GeneratedDispatchTasksPendingRepresented_holds
    : GeneratedDispatchTasksPendingRepresented := by
  intro work inputs event generated valid started resources inventories
  dsimp only
  intro beforeInvariant identities occurrence owned
  let before := ((State.initialize work).runNormalized inputs).1
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨adopted, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.task occurrence) owned
  rcases ResourceState.observeAdoptions_queueOwned_origin _ _ _ (.task occurrence) adopted
      with earlier | transferred
  · have original := resources.observeNormalCompletion_owned_origin _ _ (.task occurrence)
      .queue earlier
    obtain ⟨represented, pending⟩ := beforeInvariant occurrence original
    exact ⟨GeneratedDispatchExistingTaskRepresentation_holds work inputs event
      generated valid started
      resources inventories occurrence represented pending original owned,
      resources.observeNormalCompletion_taskUnsettled before.queue event occurrence
        _ pending earlier⟩
  · obtain ⟨producer, emitted, listed, acquired⟩ := transferred
    have original := resources.observeNormalCompletion_owned_origin _ _ (.task occurrence)
      (.producer producer) acquired
    have represented := GeneratedDispatchIncomingTaskRepresentation_holds work inputs event
      generated valid started
      resources inventories identities producer occurrence emitted listed original owned
    obtain ⟨address, owners, payload, same, known⟩ :=
      identities producer occurrence emitted listed original
    obtain ⟨task, returned, identity⟩ := adoptedTask_returned matching emitted (same ▸ known)
    have childFresh := acceptedChildTask_unsettled matching prior fresh returned
    have unfinished := acceptedChildTask_not_recorded matching returned
      (fun member =>
        childFresh (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities _ member))
    exact ⟨represented, same.symm ▸ identity ▸ unfinished⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
