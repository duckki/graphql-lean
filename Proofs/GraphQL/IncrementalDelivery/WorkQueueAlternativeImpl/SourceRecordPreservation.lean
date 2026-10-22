import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordProgress
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

/-- Success/item preparation cannot overwrite a previously stored generated task.
This follows the actual per-item fold, not a replay with an independently chosen snapshot.
-/
theorem generatedSnapshot_oldBuffer {work inputs event occurrence node}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    (release
      : match event with
        | .taskSuccess _ _ | .streamItems _ _ => True
        | _ => False)
    (found
      : ((State.initialize work).runNormalized inputs).1.queue.taskNode? occurrence
        = some node)
    (stored : node.value.isSome = true)
    : (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
        event).taskNode?
        occurrence
      = some node := by
  let before := ((State.initialize work).runNormalized inputs).1.queue
  change (registrationSnapshot before event).taskNode? occurrence = some node
  cases event with
  | taskSuccess incoming result =>
      have different := generatedReplay_buffered_ne_taskInput generated valid started found stored List.mem_cons_self
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
          simpa only [registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] using found
      | true =>
          rw [(generatedSnapshot_projection generated valid started).items stream items rfl]
          change (eagerRegistrationSnapshot before (.streamItems stream items)).taskNode? occurrence = some node
          simp only [eagerRegistrationSnapshot, active, ↓reduceIte]
          apply before.preparedStreamItems_preserves
            (fun queue => queue.taskNode? occurrence = some node) found items
          intro current item _ prior
          have integrated := ReferenceWorkQueue.State.maybeIntegrateWork_lookup_other prior item.work
          have pruned :
              ((current.maybeIntegrateWork item.work).1.pruneEmptyGroups
                (current.maybeIntegrateWork item.work).2.newGroups).1.taskNode? occurrence
                = some node := by
            simpa only [ReferenceWorkQueue.State.taskNode?,
              ReferenceWorkQueue.State.pruneEmptyGroups_taskNodes]
              using integrated
          exact ReferenceWorkQueue.State.startNewWork_lookup_existing pruned _
  | taskFailure | streamSuccess | streamFailure => cases release

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

private theorem activeSource_progress (before : State) (event : GraphEvent) {key}
    (projection
      : ((before.handleGraphEvent event).1.queue, (before.handleGraphEvent event).2.1)
        = before.queue.handleGraphEvent event)
    (active : key ∈ before.queue.rootStreams)
    : RecordTargetRepresented
        (({ state := before } : GraphBatchResult).handleGraphEvent event).state.queue
        (.stream key)
      ∨ normalCompletionTarget? before.queue event = some (.stream key)
      ∨ .cancelSource key
        ∈ (({ state := before } : GraphBatchResult).handleGraphEvent event).effects := by
  cases event with
  | taskSuccess occurrence result =>
      apply Or.inl
      apply RecordTargetRepresented.activeStream
      change key ∈ (before.handleGraphEvent (.taskSuccess occurrence result)).1.queue.rootStreams
      rw [congrArg (fun pair => pair.1.rootStreams) projection]
      exact before.queue.taskSuccess_streamRoots_cover occurrence result (List.mem_append_left _ active)
  | taskFailure occurrence errors =>
      apply Or.inl
      apply RecordTargetRepresented.activeStream
      change key ∈ (before.handleGraphEvent (.taskFailure occurrence errors)).1.queue.rootStreams
      rw [congrArg (fun pair => pair.1.rootStreams) projection]
      rwa [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.taskFailure_rootStreams]
  | streamItems stream items =>
      apply Or.inl
      apply RecordTargetRepresented.activeStream
      change key ∈ (before.handleGraphEvent (.streamItems stream items)).1.queue.rootStreams
      rw [congrArg (fun pair => pair.1.rootStreams) projection]
      exact before.queue.streamItems_streamRoots_cover stream items (List.mem_append_left _ active)
  | streamSuccess stream =>
      by_cases same : key = stream.ref
      · exact Or.inr (Or.inl (by simp [normalCompletionTarget?, ← same, active]))
      · apply Or.inl
        apply RecordTargetRepresented.activeStream
        simp only [GraphBatchResult.handleGraphEvent, State.handleGraphEvent,
          ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamSuccess]
        split
        · exact List.mem_filter.mpr ⟨active, by simpa using same⟩
        · exact active
  | streamFailure stream errors =>
      by_cases same : key = stream.ref
      · subst key
        exact Or.inr (Or.inr (by
          simp [GraphBatchResult.handleGraphEvent, State.handleGraphEvent, active]))
      · apply Or.inl
        apply RecordTargetRepresented.activeStream
        simp only [GraphBatchResult.handleGraphEvent, State.handleGraphEvent,
          ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamFailure]
        split
        · exact List.mem_filter.mpr ⟨active, by simpa using same⟩
        · exact active

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
  obtain ⟨_, earlierStarted, _⟩ := generatedReplay_beforeNext generated valid started
  cases represented with
  | activeStream active =>
      exact activeSource_progress _ _
        (generatedReplay_dispatchProjection generated valid started) active
  | @bufferedStream occurrence node key found stored held =>
      cases event with
      | taskSuccess | streamItems =>
          have snapshot := generatedSnapshot_oldBuffer generated valid earlierStarted trivial found stored
          rcases GeneratedPreparedSourceProgress_holds work inputs _ generated valid started
              trivial occurrence node key snapshot stored held with retained | cancelled
          · exact Or.inl retained
          · exact Or.inr (Or.inr cancelled)
      | taskFailure failed errors =>
          rcases generatedTaskFailure_sourceProgress generated valid earlierStarted found stored held
            with retained | cancelled
          · exact Or.inl retained
          · exact Or.inr (Or.inr cancelled)
      | streamSuccess stream =>
          apply Or.inl
          apply RecordTargetRepresented.bufferedStream (occurrence := occurrence) (node := node) _ stored held
          simp only [GraphBatchResult.handleGraphEvent, State.handleGraphEvent,
            ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamSuccess]
          split <;> exact found
      | streamFailure stream errors =>
          apply Or.inl
          apply RecordTargetRepresented.bufferedStream (occurrence := occurrence) (node := node) _ stored held
          simp only [GraphBatchResult.handleGraphEvent, State.handleGraphEvent,
            ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamFailure]
          split <;> exact found

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
theorem ResourceState.observeDispatch_completedSource_not_owned
    (resources : ResourceState) (inventories : ProducerInventories) (before : State)
    (event : GraphEvent) (key : Nat)
    (completed : normalCompletionTarget? before.queue event = some (.stream key))
    : (resources.observeDispatch inventories before event).1 (.stream key)
      ≠ .owned .queue := by
  intro owned
  obtain ⟨earlier, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.stream key) owned
  cases event with
  | taskSuccess | taskFailure | streamItems | streamFailure => cases completed
  | streamSuccess stream =>
      simp only [normalCompletionTarget?] at completed
      split at completed
      · rename_i active
        have same : stream.ref = key := by cases completed; rfl
        change ((resources.observeNormalCompletion before.queue (.streamSuccess stream)).1.observeAdoptions
          inventories (graphEffects before.queue (.streamSuccess stream))).1 (.stream key) = .owned .queue
          at earlier
        simp only [graphEffects, ResourceState.observeAdoptions, ResourceState.observeNormalCompletion,
          normalCompletionTarget?] at earlier
        simp only [active, ↓reduceIte] at earlier
        exact resources.finishQueueTarget_not_owned (.stream stream.ref) (same.symm ▸ earlier)
      · cases completed

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
  · exact False.elim (resources.observeDispatch_completedSource_not_owned inventories _ _ _ completed owned)
  · obtain ⟨_, absent⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.stream key) owned
    exact False.elim (absent (List.mem_filterMap.mpr ⟨.cancelSource key, cancelled, rfl⟩))

/-- All five generated input handlers preserve still-owned existing source representation. -/
theorem GeneratedDispatchExistingSourceRepresentation_holds
    : GeneratedDispatchExistingSourceRepresentation :=
  GeneratedDispatchExistingSourceRepresentation_of_progress
    GeneratedRepresentedSourceProgress_holds

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
