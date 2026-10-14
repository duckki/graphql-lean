import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailureHandlerPruning

/-! Observe normal task/source completion separately from requested asynchronous cleanup.
These are proof-side native completion observations, not new public host operations.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Operational task settlement is distinct from GraphQL success and cleanup settlement
-----------------------------------------------------------------------------------------

/-- A task input settles its computation, including a bubbling execution error. Source
exhaustion finishes an active source; source failure instead follows emitted cancelSource.
Late inputs cannot release an already requested lease through the observer below.
-/
def normalCompletionTarget? (before : ReferenceWorkQueue.State)
    : GraphEvent → Option CleanupTarget
  | .taskSuccess occurrence _ | .taskFailure occurrence _ => some (.task occurrence)
  | .streamSuccess stream =>
      if before.rootStreams.contains stream.ref then some (.stream stream.ref) else none
  | _ => none

/-- Finish only a queue-owned resource. Do not acquire a missing lease, steal producer
ownership, or mistake a requested asynchronous cleanup for a normally completed resource.
-/
def ResourceState.finishQueueTarget (resources : ResourceState) (target : CleanupTarget)
    : ResourceState × List ResourceAction :=
  if resources target = .owned .queue then
    (resources.set target .released, [.finishNormally target])
  else
    (resources, [])

/-- One actual completion identity constructs a legal resource history. -/
theorem ResourceState.finishQueueTarget_replay (resources : ResourceState)
    (target : CleanupTarget)
    : ResourceReplay resources (resources.finishQueueTarget target).2
        (resources.finishQueueTarget target).1 := by
  unfold ResourceState.finishQueueTarget
  split
  · exact .cons (.finish _ _ .queue (by assumption)) (.nil _)
  · exact .nil _

/-- A completed owned lease is released, not merely requested. -/
theorem ResourceState.finishQueueTarget_owned (resources : ResourceState)
    (target : CleanupTarget) (owned : resources target = .owned .queue)
    : (resources.finishQueueTarget target).1 target = .released := by
  simp [ResourceState.finishQueueTarget, ResourceState.set, owned]

/-- Every other identity is unchanged, irrespective of acquisition or ownership status. -/
theorem ResourceState.finishQueueTarget_other (resources : ResourceState)
    (target other : CleanupTarget) (different : other ≠ target)
    : (resources.finishQueueTarget target).1 other = resources other := by
  simp only [ResourceState.finishQueueTarget]
  split
  · simp [ResourceState.set, different]
  · rfl

/-- Requested cleanup, released resources, and producer-owned suffixes are untouched. -/
theorem ResourceState.finishQueueTarget_foreign (resources : ResourceState)
    (target : CleanupTarget) (foreign : resources target ≠ .owned .queue)
    : resources.finishQueueTarget target = (resources, []) := by
  simp [ResourceState.finishQueueTarget, foreign]

/-- Observe the completion carried by this input, without reconstructing acquisitions. -/
def ResourceState.observeNormalCompletion (resources : ResourceState)
    (before : ReferenceWorkQueue.State) (event : GraphEvent)
    : ResourceState × List ResourceAction :=
  match normalCompletionTarget? before event with
  | none => (resources, [])
  | some target => resources.finishQueueTarget target

/-- Normal completion constructs a legal history licensed by the actual input. -/
theorem ResourceState.observeNormalCompletion_replay (resources : ResourceState)
    (before : ReferenceWorkQueue.State) (event : GraphEvent)
    : ResourceReplay resources (resources.observeNormalCompletion before event).2
        (resources.observeNormalCompletion before event).1 := by
  unfold ResourceState.observeNormalCompletion
  split
  · exact .nil _
  · exact resources.finishQueueTarget_replay _

/-- Every normal-release action names exactly this input's completion identity. -/
theorem ResourceState.observeNormalCompletion_actions (resources : ResourceState)
    (before : ReferenceWorkQueue.State) (event : GraphEvent)
    : ∀ action ∈ (resources.observeNormalCompletion before event).2,
        ∃ target,
          normalCompletionTarget? before event = some target
          ∧ action = .finishNormally target := by
  unfold ResourceState.observeNormalCompletion
  split
  · simp
  · rename_i target selected
    unfold ResourceState.finishQueueTarget
    split
    · intro action member
      exact ⟨target, selected, List.mem_singleton.mp member⟩
    · simp

-----------------------------------------------------------------------------------------
-- Compose normal completion with the same dispatch's actual cleanup operations
-----------------------------------------------------------------------------------------

/-- Observe completed identities, then cleanup starts in the actual single-event dispatch.
Adoption is deliberately separate: its independently acquired producer inventory must be
supplied at the accepting registration site. This does not claim full handler ownership.
-/
def ResourceState.observeCompletionAndCleanup (resources : ResourceState)
    (before : State) (event : GraphEvent)
    : ResourceState × List ResourceAction :=
  let completed := resources.observeNormalCompletion before.queue event
  let effects := (({ state := before } : GraphBatchResult).handleGraphEvent event).effects
  let requested :=
    completed.1.requestQueueCleanup (effects.filterMap HostEffect.cleanupStart?)
  (requested.1, completed.2 ++ requested.2)

/-- Completion and cleanup use one compatible resource history, in actual dispatch order. -/
theorem ResourceState.observeCompletionAndCleanup_replay (resources : ResourceState)
    (before : State) (event : GraphEvent)
    : ResourceReplay resources (resources.observeCompletionAndCleanup before event).2
        (resources.observeCompletionAndCleanup before event).1 :=
  (resources.observeNormalCompletion_replay _ _).append
    ((resources.observeNormalCompletion before.queue event).1.requestQueueCleanup_replay
      _)

/-- All constructed actions are licensed by this input or this same dispatch's effects. -/
theorem ResourceState.observeCompletionAndCleanup_actions (resources : ResourceState)
    (before : State) (event : GraphEvent)
    : ∀ action ∈ (resources.observeCompletionAndCleanup before event).2,
        (∃ target,
          normalCompletionTarget? before.queue event = some target
          ∧ action = .finishNormally target)
        ∨ (∃ effect ∈
            (({ state := before } : GraphBatchResult).handleGraphEvent event).effects,
            ∃ target,
              effect.cleanupStart? = some target ∧ action = .requestCleanup target) := by
  intro action member
  rcases List.mem_append.mp member with completed | requested
  · exact Or.inl (resources.observeNormalCompletion_actions _ _ _ completed)
  · obtain ⟨target, listed, same⟩ :=
      (resources.observeNormalCompletion before.queue event).1.requestQueueCleanup_actions _ _ requested
    obtain ⟨effect, emitted, identifies⟩ := List.mem_filterMap.mp listed
    exact Or.inr ⟨effect, emitted, target, identifies, same⟩

/-- Task failure first finishes the settler, then uses the actual pruning cleanup targets. -/
theorem ResourceState.observeCompletionAndCleanup_taskFailure (resources : ResourceState)
    (before : State) (failed : WorkQueueSemantics.Occurrence) (errors : Nat)
    : let completed := resources.finishQueueTarget (.task failed)
      let requested :=
        completed.1.observeHandlerCleanup before (.taskFailure failed errors)
      resources.observeCompletionAndCleanup before (.taskFailure failed errors)
      = (requested.1, completed.2 ++ requested.2) := by
  simp only [ResourceState.observeCompletionAndCleanup, ResourceState.observeNormalCompletion,
    normalCompletionTarget?, GraphBatchResult.handleGraphEvent, State.handleGraphEvent,
    List.nil_append, ResourceState.observeHandlerCleanup]

/-- The input's completed queue-owned identity stays released through all cleanup starts. -/
theorem ResourceState.observeCompletionAndCleanup_finishedTarget
    (resources : ResourceState) (before : State) (event : GraphEvent)
    (target : CleanupTarget)
    (selected : normalCompletionTarget? before.queue event = some target)
    (owned : resources target = .owned .queue)
    : (resources.observeCompletionAndCleanup before event).1 target = .released := by
  have completed : (resources.observeNormalCompletion before.queue event).1 target = .released := by
    simp only [ResourceState.observeNormalCompletion, selected]
    exact resources.finishQueueTarget_owned target owned
  change ((resources.observeNormalCompletion before.queue event).1.requestQueueCleanup _).1 target = _
  rw [ResourceState.requestQueueCleanup_foreign]
  · exact completed
  · rw [completed]; simp

/-- The completed failed task cannot remain queue-owned after its handler's cleanup pass. -/
theorem ResourceState.observeCompletionAndCleanup_finishedTask (resources : ResourceState)
    (before : State) (failed : WorkQueueSemantics.Occurrence) (errors : Nat)
    (owned : resources (.task failed) = .owned .queue)
    : (resources.observeCompletionAndCleanup before (.taskFailure failed errors)).1
        (.task failed)
      = .released :=
  resources.observeCompletionAndCleanup_finishedTarget before (.taskFailure failed errors)
    (.task failed) rfl owned

-----------------------------------------------------------------------------------------
-- Generated full failure disposal also retires the finished computation's lease
-----------------------------------------------------------------------------------------

/-- One generated failure observation finishes its task and requests dropped held sources.
Complete native acquisition/adoption inventories and async settlement are still separate.
-/
def GeneratedTaskFailureResourceCompletion : Prop :=
  ∀ work inputs failed errors,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work
        (inputs.flatten ++ [.taskFailure failed errors])
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → ∀ resources : ResourceState,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced :=
          ({ state := before } : GraphBatchResult).handleGraphEvent
            (.taskFailure failed errors)
        let observed :=
          resources.observeCompletionAndCleanup before (.taskFailure failed errors)
        ResourceReplay resources observed.2 observed.1
        ∧ (resources (.task failed) = .owned .queue
            → observed.1 (.task failed) = .released)
        ∧ ∀ occurrence node key,
            before.queue.taskNode? occurrence = some node
            → node.value.isSome = true
            → (∃ owner ∈ node.task.groups,
                ∃ group, before.queue.groupNode? owner.ref = some group)
            → key ∈ node.childStreams
            → reduced.state.queue.taskNode? occurrence = none
            → resources (.stream key) = .owned .queue
            → .cancelSource key ∈ reduced.effects
              ∧ observed.1 (.stream key) = .cleanupRequested .queue

/-- Compose the existing generated failure witness with licensed normal task completion. -/
theorem GeneratedTaskFailureResourceCompletion_holds
    : GeneratedTaskFailureResourceCompletion := by
  intro work inputs failed errors generated valid started resources
  let before := ((State.initialize work).runNormalized inputs).1
  let completed := resources.finishQueueTarget (.task failed)
  have covered := GeneratedTaskFailureDisposal_holds work inputs failed errors generated valid started completed.1
  refine ⟨resources.observeCompletionAndCleanup_replay _ _,
    resources.observeCompletionAndCleanup_finishedTask _ _ _, ?_⟩
  intro occurrence node key found stored owned held dropped lease
  have unchanged : completed.1 (.stream key) = resources (.stream key) :=
    resources.finishQueueTarget_other (.task failed) (.stream key) (by intro impossible; cases impossible)
  have target := covered.2 occurrence node key found stored owned held dropped
  refine ⟨target.1, ?_⟩
  rw [resources.observeCompletionAndCleanup_taskFailure]
  exact target.2 (unchanged.trans lease)

/-- Normal completion preserves every identity other than the input's completion target. -/
theorem ResourceState.observeNormalCompletion_other (resources : ResourceState)
    (before : ReferenceWorkQueue.State) (event : GraphEvent) (target : CleanupTarget)
    (different : normalCompletionTarget? before event ≠ some target)
    : (resources.observeNormalCompletion before event).1 target = resources target := by
  unfold ResourceState.observeNormalCompletion
  cases selected : normalCompletionTarget? before event with
  | none => rfl
  | some completed =>
      apply resources.finishQueueTarget_other
      intro same
      exact different (same ▸ selected)

/-- An actual cleanup start requests an owned lease after this input's distinct normal
completion. The resulting history is the already-constructed combined observer's history.
-/
theorem ResourceState.observeCompletionAndCleanup_requested (resources : ResourceState)
    (before : State) (event : GraphEvent) (target : CleanupTarget)
    (different : normalCompletionTarget? before.queue event ≠ some target)
    (emitted
      : target
        ∈ (({ state := before } : GraphBatchResult).handleGraphEvent
            event).effects.filterMap
            HostEffect.cleanupStart?)
    (owned : resources target = .owned .queue)
    : (resources.observeCompletionAndCleanup before event).1 target
      = .cleanupRequested .queue := by
  apply ResourceState.requestQueueCleanup_owned _ _ _ emitted
  rw [resources.observeNormalCompletion_other _ _ _ different]
  exact owned

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
