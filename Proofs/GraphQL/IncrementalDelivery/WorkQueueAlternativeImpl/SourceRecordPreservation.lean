import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableSourceHandlerProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionReplay

/-! Every previously represented source stays represented unless this actual input
completes it or requests cancellation. No native acquisition completeness is inferred.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Generated input freshness retains exact old buffers during accepted registration
-----------------------------------------------------------------------------------------

private theorem streamFold_oldSource (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc) (unique : acc.2.2.2.2.1.Nodup)
    {occurrence node key} (held : key ∈ node.childStreams)
    (safe : acc.1.queue.taskNode? occurrence = some node ∨ .stream key ∈ acc.2.2.2.2.1)
    : (items.foldl streamRegistrationStep acc).1.queue.taskNode? occurrence = some node
      ∨ .stream key ∈ (items.foldl streamRegistrationStep acc).2.2.2.2.1 := by
  induction items generalizing acc with
  | nil => exact safe
  | cons item rest ih =>
      let registered := acc.1.maybeIntegrateWork item.work
      let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
      let current := { registered.1 with queue := pruned.1 }
      let released := { registered.2.newWork with newGroups := pruned.2 }
      have nextUnique : (streamRegistrationStep acc item).2.2.2.2.1.Nodup :=
        State.startNewWork_targets_nodup current released registered.2 _ unique
      apply ih _ nextUnique
      rcases safe with found | requested
      · have integrated := State.maybeIntegrateWork_lookup_other found item.work
        have prunedFound : current.queue.taskNode? occurrence = some node := by
          simpa only [current, pruned, ReferenceWorkQueue.State.taskNode?,
            ReferenceWorkQueue.State.pruneEmptyGroups_taskNodes]
            using integrated
        exact startup_heldSource current released registered.2 acc.2.2.2.2.1 prunedFound
          held
      · apply Or.inr
        exact (State.startNewWork_targets_prefix current released registered.2 _ unique).subset
          requested

/-- Preparation retains an old buffer or requests its held source during actual startup.
The item fold includes cached-failure removal and its inline cleanup.
-/
theorem generatedSnapshot_oldBuffer_or_cancelled {work inputs event occurrence node key}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    (release
      : match event with
        | .taskSuccess _ _ | .streamItems _ _ => True
        | _ => False)
    (found
      : ((State.initialize work).runNormalized inputs).1.queue.taskNode? occurrence
        = some node)
    (stored : node.value.isSome = true) (held : key ∈ node.childStreams)
    : (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
          event).taskNode?
          occurrence
        = some node
      ∨ .cancelSource key
        ∈ (({ state := ((State.initialize work).runNormalized inputs).1 }
            : GraphBatchResult).handleGraphEvent
            event).effects := by
  obtain ⟨_, earlierStarted, _⟩ := generatedReplay_beforeNext generated valid started
  let before := ((State.initialize work).runNormalized inputs).1.queue
  change (registrationSnapshot before event).taskNode? occurrence = some node ∨ _
  cases event with
  | taskSuccess incoming result =>
      apply Or.inl
      have different := generatedReplay_buffered_ne_taskInput generated valid earlierStarted
        found stored List.mem_cons_self
      cases inputFound : before.taskNode? incoming with
      | none => simpa only [registrationSnapshot, inputFound] using found
      | some input =>
          simp only [registrationSnapshot, inputFound]
          exact State.maybeIntegrateWork_lookup_other
            (ReferenceWorkQueue.State.putTaskNode_lookup_other found
              { input with value := some result.value }
              (by
                change input.task.occurrence ≠ occurrence
                rw [(ReferenceWorkQueue.State.taskNode?_some inputFound).2]
                exact Ne.symm different))
            result.work
            (some incoming)
            (by intro same; exact different (Option.some.inj same).symm)
  | streamItems stream items =>
      cases active : before.rootStreams.contains stream.ref with
      | false =>
          apply Or.inl
          simpa only [registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] using found
      | true =>
          let state := ((State.initialize work).runNormalized inputs).1
          let acc := items.foldl streamRegistrationStep (state, [], [], [], [], [], [])
          have running : state.stopped = false := by
            dsimp only [state]
            rw [generatedReplay_beforeNextState generated valid started]
          have stateEq : state = { queue := before } := by
            exact congrArg (fun stopped => ({ queue := before, stopped } : State)) running
          have classified : acc.1.queue.taskNode? occurrence = some node ∨
              .stream key ∈ acc.2.2.2.2.1 := by
            exact streamFold_oldSource items (state, [], [], [], [], [], [])
              List.nodup_nil held (.inl found)
          rcases classified with kept | requested
          · apply Or.inl
            rw [registrationSnapshot_itemFold before stream items active]
            simpa only [acc, stateEq] using kept
          · apply Or.inr
            have tracked := streamRegistrationFold_cleanupTargets items
              (state, [], [], [], [], [], []) List.nodup_nil rfl
            have extending := (State.drainReadyGroups_targets acc.1 acc.2.2.2.2.1 tracked.1).2
            have emitted : .stream key ∈ (state.streamItems stream items).2.2.1.filterMap
                HostEffect.cleanupStart? := by
              rw [State.streamItems_cleanupStarts_eq state stream items active]
              exact extending.subset requested
            obtain ⟨effect, member, same⟩ := List.mem_filterMap.mp emitted
            have cancellation : .cancelSource key ∈ (state.streamItems stream items).2.2.1 := by
              cases effect <;> simp only [HostEffect.cleanupStart?, reduceCtorEq,
                Option.some.injEq, CleanupTarget.stream.injEq] at same
              subst key
              exact member
            simpa only [GraphBatchResult.handleGraphEvent, State.handleGraphEvent,
              ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil, List.nil_append]
              using cancellation
  | taskFailure | groupFailure | streamSuccess | streamFailure => cases release

-----------------------------------------------------------------------------------------
-- Full failure dispatch also retains the exact old record or requests its held sources
-----------------------------------------------------------------------------------------

/-- All old generated buffered sources keep a record or enter actual task-failure cleanup.
The forest, links, catalogue, contributor existence and settler exclusion are derived here.
-/
theorem generatedTaskFailure_sourceProgress
    {work inputs failed errors occurrence node key}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work
          (inputs.flatten ++ [.taskFailure failed errors]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    (found
      : ((State.initialize work).runNormalized inputs).1.queue.taskNode? occurrence
        = some node)
    (stored : node.value.isSome = true) (held : key ∈ node.childStreams)
    : let before := ((State.initialize work).runNormalized inputs).1
      let reduced :=
        ({ state := before } : GraphBatchResult).handleGraphEvent
          (.taskFailure failed errors)
      RecordTargetRepresented reduced.state.queue (.stream key)
      ∨ .cancelSource key ∈ reduced.effects := by
  dsimp only
  let before := ((State.initialize work).runNormalized inputs).1
  let event : GraphEvent := .taskFailure failed errors
  let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
  by_cases retained : reduced.state.queue.taskNode? occurrence = some node
  · exact Or.inl (.bufferedStream retained stored held)
  · have different := generatedReplay_buffered_ne_taskInput generated valid started found stored
      List.mem_cons_self
    exact .inr (taskFailure_lostBufferedSource before failed errors different found held retained)

-----------------------------------------------------------------------------------------
-- Existing active and held records cover all five graph input kinds
-----------------------------------------------------------------------------------------

/-- Every source with a pre-handler record is represented afterwards, normally completed,
or cancelled by the same actual dispatch. No endpoint law is assumed.
-/
def GeneratedRepresentedSourceProgress : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ key,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        RecordTargetRepresented before.queue (.stream key)
        → RecordTargetRepresented reduced.state.queue (.stream key)
          ∨ normalCompletionTarget? before.queue event = some (.stream key)
          ∨ .cancelSource key ∈ reduced.effects

/-- Generated replay discharges every represented-source handler case. -/
theorem GeneratedRepresentedSourceProgress_holds
    : GeneratedRepresentedSourceProgress := by
  intro work inputs event generated valid started key
  dsimp only
  intro represented
  let before := ((State.initialize work).runNormalized inputs).1
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have source := generatedReplay_sourceFrame generated canonical valid started
  obtain ⟨raw, _, _⟩ := generatedReplay_beforeNext generated valid started
  have keys : before.queue.TaskNodeKeysUnique := by
    change ((State.initialize work).runNormalized inputs).1.queue.TaskNodeKeysUnique
    rw [raw, ← ReferenceWorkQueue.State.runNormalized_replayBatches]
    exact ReferenceWorkQueue.createWorkQueue_runNormalized_taskNodeKeysUnique
      (ReferenceWorkQueue.Work.fromExecution work) inputs
  have inventory : before.queue.ChildStreamInventory := by
    change ((State.initialize work).runNormalized inputs).1.queue.ChildStreamInventory
    rw [raw, ← ReferenceWorkQueue.State.runNormalized_replayBatches]
    exact ReferenceWorkQueue.createWorkQueue_runNormalized_childStreamInventory
      (ReferenceWorkQueue.Work.fromExecution work) inputs
  have progress := sourceFrame_existingSource_progress_available generated canonical source keys
    inventory valid [] rfl represented
  have running := generatedReplay_beforeNextState generated valid started
  change before = { queue := before.queue } at running
  simp only [GraphBatchResult.handleGraphEvent, List.nil_append]
  change RecordTargetRepresented (((before.handleGraphEvent event).1.queue).enqueueGroupFailures
    (before.handleGraphEvent event).2.2.2) (.stream key)
    ∨ normalCompletionTarget? before.queue event = some (.stream key)
    ∨ .cancelSource key ∈ (before.handleGraphEvent event).2.2.1
  rw [running]
  rcases progress with retained | completed | cancelled
  · apply Or.inl
    cases retained with
    | activeStream active => exact .activeStream active
    | bufferedStream found stored held => exact .bufferedStream found stored held
  · exact .inr (.inl completed)
  · exact .inr (.inr cancelled)

-----------------------------------------------------------------------------------------
-- The same resource observer excludes both ways of leaving source ownership
-----------------------------------------------------------------------------------------

/-- Finishing a queue target never leaves that same identity queue-owned. Foreign leases
are not stolen, so the assertion does not require an initially queue-owned premise.
-/
theorem ResourceState.finishQueueTarget_not_owned (resources : ResourceState)
    (target : CleanupTarget)
    : (resources.finishQueueTarget target).1 target ≠ .owned .queue := by
  by_cases owned : resources target = .owned .queue
  · rw [resources.finishQueueTarget_owned target owned]
    intro impossible
    cases impossible
  · rw [resources.finishQueueTarget_foreign target owned]
    exact owned

/-- An actual source-exhaustion input cannot leave its completed source queue-owned.
It has no adoption label: acknowledgement or completion is not reacquisition.
-/
theorem ResourceState.observeDispatch_completedSource_not_owned_available
    (resources : ResourceState) (inventories : ProducerInventories) (before : State)
    (event : GraphEvent) (key : Nat)
    (completed : normalCompletionTarget? before.queue event = some (.stream key))
    (available : List (Occurrence × Nat))
    : (resources.observeDispatch inventories before event available).1 (.stream key)
      ≠ .owned .queue := by
  intro owned
  obtain ⟨earlier, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.stream key) owned
  cases event with
  | taskSuccess | taskFailure | groupFailure | streamItems | streamFailure =>
      cases completed
  | streamSuccess stream =>
      simp only [normalCompletionTarget?] at completed
      split at completed
      · rename_i active
        have same : stream.ref = key := by cases completed; rfl
        change ((resources.observeNormalCompletion before.queue (.streamSuccess
          stream)).1.observeAdoptions
          inventories (graphEffects before.queue (.streamSuccess stream))).1 (.stream key) =
            .owned .queue
          at earlier
        simp only [graphEffects, ResourceState.observeAdoptions,
          ResourceState.observeNormalCompletion,
          normalCompletionTarget?] at earlier
        simp only [active, ↓reduceIte] at earlier
        exact resources.finishQueueTarget_not_owned (.stream stream.ref) (same.symm ▸ earlier)
      · cases completed

/-- Empty-snapshot interface for normal source-completion ownership. -/
theorem ResourceState.observeDispatch_completedSource_not_owned
    (resources : ResourceState) (inventories : ProducerInventories) (before : State)
    (event : GraphEvent) (key : Nat)
    (completed : normalCompletionTarget? before.queue event = some (.stream key))
    : (resources.observeDispatch inventories before event).1 (.stream key)
      ≠ .owned .queue :=
  resources.observeDispatch_completedSource_not_owned_available inventories before event
    key completed []

/-- Still-queue-owned sources with old record locations retain current locations after any
generated graph input. This is preservation of existing leases, not acquisition completeness.
-/
def GeneratedDispatchExistingSourceRepresentation : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories) key,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        RecordTargetRepresented before.queue (.stream key)
        → (resources.observeDispatch inventories before event).1 (.stream key)
          = .owned .queue
        → RecordTargetRepresented reduced.state.queue (.stream key)

/-- Checked composition: generated record progress plus the same observer's completion and
cleanup phases prove endpoint representation, without assuming a no-forgotten-source law.
-/
theorem GeneratedDispatchExistingSourceRepresentation_of_progress
    (progress : GeneratedRepresentedSourceProgress)
    : GeneratedDispatchExistingSourceRepresentation := by
  intro work inputs event generated valid started resources inventories key
  dsimp only
  intro represented owned
  rcases progress work inputs event generated valid started key represented with
    retained | completed | cancelled
  · exact retained
  · exact False.elim (resources.observeDispatch_completedSource_not_owned inventories _ _ _
    completed owned)
  · obtain ⟨_, absent⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.stream key) owned
    exact False.elim (absent (List.mem_filterMap.mpr ⟨.cancelSource key, cancelled, rfl⟩))

/-- All five generated input handlers preserve still-owned existing source representation. -/
theorem GeneratedDispatchExistingSourceRepresentation_holds
    : GeneratedDispatchExistingSourceRepresentation :=
  GeneratedDispatchExistingSourceRepresentation_of_progress
    GeneratedRepresentedSourceProgress_holds

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
