import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedBufferDisposal

/-! Observe whole-work handoff from actual dispatch labels and an independently acquired
producer inventory. Compose adoption, normal completion and disposal in one resource history.
Inventory completeness is checked separately; no acquisition is inferred from queue records.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

-----------------------------------------------------------------------------------------
-- Adoption uses actual effect order and independently supplied producer inventories
-----------------------------------------------------------------------------------------

/-- A native observer supplies the identities acquired by each returning producer.
These lists are audit evidence, not a reconstruction from cleanup targets or task registries.
-/
abbrev ProducerInventories := Occurrence → List CleanupTarget

/-- Interpret only whole-work adoption labels, in order. Unlisted leases stay with their
producer; acknowledgements and cleanup operations cannot manufacture an ownership handoff.
-/
def ResourceState.observeAdoptions (resources : ResourceState)
    (inventories : ProducerInventories)
    : List HostEffect → ResourceState × List ResourceAction
  | [] => (resources, [])
  | .adopt producer :: rest =>
      let next := resources.adopt producer (inventories producer)
      let (final, actions) := next.observeAdoptions inventories rest
      (final, .adopt producer (inventories producer) :: actions)
  | _ :: rest => resources.observeAdoptions inventories rest

/-- Every handoff is one legal transfer of existing leases, not an implicit acquisition. -/
theorem ResourceState.observeAdoptions_replay (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    : ResourceReplay resources (resources.observeAdoptions inventories effects).2
        (resources.observeAdoptions inventories effects).1 := by
  induction effects generalizing resources with
  | nil => exact .nil _
  | cons effect rest ih =>
      cases effect with
      | adopt producer => exact .cons (.adopt _ _ _) (ih _)
      | acknowledge | abortTask | cancelSource | abortStreamQueue | responseFinished =>
          exact ih _

/-- The complete adoption action list is precisely the dispatch's ordered adoption labels. -/
theorem ResourceState.observeAdoptions_actions (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    : (resources.observeAdoptions inventories effects).2
      = effects.filterMap
          (fun effect =>
            match effect with
            | .adopt producer => some (.adopt producer (inventories producer))
            | _ => none) := by
  induction effects generalizing resources with
  | nil => rfl
  | cons effect rest ih =>
      cases effect <;> simp only [ResourceState.observeAdoptions, List.filterMap_cons, ih]

/-- Adoption never introduces a producer-owned lease. -/
theorem ResourceState.adopt_producerOwned_before (resources : ResourceState)
    (producer owner : Occurrence) (inventory : List CleanupTarget)
    (target : CleanupTarget)
    (owned : resources.adopt producer inventory target = .owned (.producer owner))
    : resources target = .owned (.producer owner) := by
  unfold ResourceState.adopt at owned
  split at owned
  · cases owned
  · exact owned

/-- A producer-owned remainder after any adoption prefix was already owned by that producer. -/
theorem ResourceState.observeAdoptions_producerOwned_before (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    (producer : Occurrence) (target : CleanupTarget)
    (owned
      : (resources.observeAdoptions inventories effects).1 target
        = .owned (.producer producer))
    : resources target = .owned (.producer producer) := by
  induction effects generalizing resources with
  | nil => exact owned
  | cons effect rest ih =>
      cases effect with
      | adopt owner => exact resources.adopt_producerOwned_before _ _ _ _ (ih _ owned)
      | acknowledge | abortTask | cancelSource | abortStreamQueue | responseFinished =>
          exact ih _ owned

/-- A queue-owned lease stays queue-owned through adoption, even when inventories overlap. -/
theorem ResourceState.observeAdoptions_queueOwned (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    (target : CleanupTarget) (owned : resources target = .owned .queue)
    : (resources.observeAdoptions inventories effects).1 target = .owned .queue := by
  induction effects generalizing resources with
  | nil => exact owned
  | cons effect rest ih =>
      cases effect with
      | adopt producer =>
          apply ih
          rw [resources.adopt_unchanged]
          · exact owned
          · rw [owned]; simp
      | acknowledge | abortTask | cancelSource | abortStreamQueue | responseFinished =>
          exact ih _ owned

/-- Listing an identity without an acquired lease cannot create a resource obligation. -/
theorem ResourceState.observeAdoptions_unacquired (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    (target : CleanupTarget) (unacquired : resources target = .unacquired)
    : (resources.observeAdoptions inventories effects).1 target = .unacquired := by
  induction effects generalizing resources with
  | nil => exact unacquired
  | cons effect rest ih =>
      cases effect with
      | adopt producer =>
          apply ih
          rw [resources.adopt_unchanged]
          · exact unacquired
          · rw [unacquired]; simp
      | acknowledge | abortTask | cancelSource | abortStreamQueue | responseFinished =>
          exact ih _ unacquired

/-- An already producer-owned listed identity is transferred by its actual adoption label. -/
theorem ResourceState.observeAdoptions_transfers (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    (producer : Occurrence) (target : CleanupTarget)
    (emitted : .adopt producer ∈ effects) (listed : target ∈ inventories producer)
    (owned : resources target = .owned (.producer producer))
    : (resources.observeAdoptions inventories effects).1 target = .owned .queue := by
  induction effects generalizing resources with
  | nil => cases emitted
  | cons effect rest ih =>
      rcases List.mem_cons.mp emitted with same | later
      · subst effect
        exact (resources.adopt producer (inventories producer)).observeAdoptions_queueOwned
          inventories rest target (resources.adopt_owned producer _ target listed owned)
      · cases effect with
        | adopt owner =>
            by_cases same : owner = producer
            · subst owner
              exact (resources.adopt producer (inventories producer)).observeAdoptions_queueOwned
                inventories rest target (resources.adopt_owned producer _ target listed owned)
            · apply ih _ later
              rw [resources.adopt_unchanged]
              · exact owned
              · rw [owned]; simp [Ne.symm same]
        | acknowledge | abortTask | cancelSource | abortStreamQueue | responseFinished =>
            exact ih _ later owned

/-- Whole-work handoff must list every existing lease of each actually adopted producer.
This is a native inventory-completeness obligation, not an admission/source condition.
-/
def CompleteAdoptionInventories (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    : Prop :=
  ∀ producer,
    .adopt producer ∈ effects
    → ∀ target,
        resources target = .owned (.producer producer) → target ∈ inventories producer

/-- A complete handoff leaves no suffix owned by an actually adopted producer. -/
theorem ResourceState.observeAdoptions_no_producer (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    (complete : CompleteAdoptionInventories resources inventories effects)
    (producer : Occurrence) (emitted : .adopt producer ∈ effects) (target : CleanupTarget)
    : (resources.observeAdoptions inventories effects).1 target
      ≠ .owned (.producer producer) := by
  intro remains
  have before := resources.observeAdoptions_producerOwned_before inventories effects producer target remains
  have transferred := resources.observeAdoptions_transfers inventories effects producer target emitted
    (complete producer emitted target before) before
  rw [transferred] at remains
  cases remains

-----------------------------------------------------------------------------------------
-- One dispatch joins adoption, completion and actual cleanup without changing witnesses
-----------------------------------------------------------------------------------------

/-- First observe the input's completed computation/source. Actual accepting graph labels
then determine which independent inventories are handed off, before this dispatch's cleanup.
No lease is acquired here. Receipt acknowledgements and async settlement remain separate.
-/
def ResourceState.observeDispatch (resources : ResourceState)
    (inventories : ProducerInventories) (before : State) (event : GraphEvent)
    : ResourceState × List ResourceAction :=
  let completed := resources.observeNormalCompletion before.queue event
  let adopted :=
    completed.1.observeAdoptions inventories (graphEffects before.queue event)
  let effects := (({ state := before } : GraphBatchResult).handleGraphEvent event).effects
  let requested :=
    adopted.1.requestQueueCleanup (effects.filterMap HostEffect.cleanupStart?)
  (requested.1, completed.2 ++ adopted.2 ++ requested.2)

/-- One compatible resource history includes the actual handoff and subsequent disposal. -/
theorem ResourceState.observeDispatch_replay (resources : ResourceState)
    (inventories : ProducerInventories) (before : State) (event : GraphEvent)
    : ResourceReplay resources (resources.observeDispatch inventories before event).2
        (resources.observeDispatch inventories before event).1 :=
  ((resources.observeNormalCompletion_replay _ _).append
    ((resources.observeNormalCompletion before.queue event).1.observeAdoptions_replay
      inventories _)).append
    (((resources.observeNormalCompletion before.queue event).1.observeAdoptions
        inventories (graphEffects before.queue event)).1.requestQueueCleanup_replay
      _)

/-- Normal completion changes only queue-owned leases, including at the input identity. -/
theorem ResourceState.observeNormalCompletion_foreign (resources : ResourceState)
    (before : ReferenceWorkQueue.State) (event : GraphEvent) (target : CleanupTarget)
    (foreign : resources target ≠ .owned .queue)
    : (resources.observeNormalCompletion before event).1 target = resources target := by
  unfold ResourceState.observeNormalCompletion
  split
  · rfl
  · rename_i completed selected
    by_cases same : target = completed
    · subst target
      rw [resources.finishQueueTarget_foreign _ foreign]
    · exact resources.finishQueueTarget_other _ _ same

/-- Even a listed identity cannot be acquired implicitly by any part of dispatch. -/
theorem ResourceState.observeDispatch_unacquired (resources : ResourceState)
    (inventories : ProducerInventories) (before : State) (event : GraphEvent)
    (target : CleanupTarget) (unacquired : resources target = .unacquired)
    : (resources.observeDispatch inventories before event).1 target = .unacquired := by
  have completed : (resources.observeNormalCompletion before.queue event).1 target = .unacquired := by
    rw [resources.observeNormalCompletion_foreign _ _ _ (by rw [unacquired]; simp), unacquired]
  have adopted := (resources.observeNormalCompletion before.queue event).1.observeAdoptions_unacquired
    inventories (graphEffects before.queue event) target completed
  change (ResourceState.requestQueueCleanup _ _).1 target = _
  rw [ResourceState.requestQueueCleanup_foreign]
  · exact adopted
  · rw [adopted]; simp

/-- Every action belongs to this input's normal completion, its ordered adoption labels,
or the same dispatch's actual cleanup starts. No acquisition or settlement is invented.
-/
theorem ResourceState.observeDispatch_actions (resources : ResourceState)
    (inventories : ProducerInventories) (before : State) (event : GraphEvent)
    : ∀ action ∈ (resources.observeDispatch inventories before event).2,
        (∃ target,
          normalCompletionTarget? before.queue event = some target
          ∧ action = .finishNormally target)
        ∨ (∃ producer,
            .adopt producer ∈ graphEffects before.queue event
            ∧ action = .adopt producer (inventories producer))
        ∨ (∃ effect ∈
            (({ state := before } : GraphBatchResult).handleGraphEvent event).effects,
            ∃ target,
              effect.cleanupStart? = some target ∧ action = .requestCleanup target) := by
  intro action member
  rcases List.mem_append.mp member with first | requested
  · rcases List.mem_append.mp first with completed | adopted
    · exact Or.inl (resources.observeNormalCompletion_actions _ _ _ completed)
    · rw [ResourceState.observeAdoptions_actions] at adopted
      obtain ⟨effect, emitted, same⟩ := List.mem_filterMap.mp adopted
      cases effect <;> simp only [Option.some.injEq, reduceCtorEq] at same
      exact Or.inr (Or.inl ⟨_, emitted, same.symm⟩)
  · obtain ⟨target, listed, same⟩ := ResourceState.requestQueueCleanup_actions _ _ _ requested
    obtain ⟨effect, emitted, identifies⟩ := List.mem_filterMap.mp listed
    exact Or.inr (Or.inr ⟨effect, emitted, target, identifies, same⟩)

/-- A producer-owned identity distinct from the input's normal completion is transferred
at its adoption label and requested at its actual cleanup operation, in that order.
-/
theorem ResourceState.observeDispatch_adopted_requested (resources : ResourceState)
    (inventories : ProducerInventories) (before : State) (event : GraphEvent)
    (producer : Occurrence) (target : CleanupTarget)
    (different : normalCompletionTarget? before.queue event ≠ some target)
    (emitted : .adopt producer ∈ graphEffects before.queue event)
    (listed : target ∈ inventories producer)
    (owned : resources target = .owned (.producer producer))
    (requested
      : target
        ∈ (({ state := before } : GraphBatchResult).handleGraphEvent
            event).effects.filterMap
            HostEffect.cleanupStart?)
    : (resources.observeDispatch inventories before event).1 target
      = .cleanupRequested .queue := by
  apply ResourceState.requestQueueCleanup_owned _ _ _ requested
  apply ResourceState.observeAdoptions_transfers _ _ _ producer target emitted listed
  rw [resources.observeNormalCompletion_other _ _ _ different]
  exact owned

/-- Composition uses the inventory transferred by this exact handler's adoption effects.
A newly adopted held source dropped in the same generated dispatch is activated or requested;
there is no pre-existing queue-ownership assumption for that source.
-/
def GeneratedDispatchHandoffDisposal : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → (match event with
        | .taskSuccess _ _ | .streamItems _ _ => True
        | _ => False)
    → ∀ resources inventories,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        let snapshot := registrationSnapshot before.queue event
        let observed := resources.observeDispatch inventories before event
        ResourceReplay resources observed.2 observed.1
        ∧ ∀ producer occurrence node key,
            .adopt producer ∈ graphEffects before.queue event
            → .stream key ∈ inventories producer
            → resources (.stream key) = .owned (.producer producer)
            → snapshot.taskNode? occurrence = some node
            → node.value.isSome = true
            → key ∈ node.childStreams
            → reduced.state.queue.taskNode? occurrence = none
            → key ∈ reduced.state.queue.rootStreams
              ∨ (.cancelSource key ∈ reduced.effects
                  ∧ observed.1 (.stream key) = .cleanupRequested .queue)

/-- Checked root: transfer the independently acquired lease, then use the same snapshot's
generated owner/cut/disposal proof, with exactly that transferred resource state.
-/
theorem GeneratedDispatchHandoffDisposal_holds : GeneratedDispatchHandoffDisposal := by
  intro work inputs event generated valid started release resources inventories
  dsimp only
  let before := ((State.initialize work).runNormalized inputs).1
  have covered := GeneratedStoredReleaseDisposal_holds work inputs event generated valid started release resources
  refine ⟨resources.observeDispatch_replay inventories before event, ?_⟩
  intro producer occurrence node key emitted listed owned found stored held dropped
  rcases covered.2 occurrence node key found stored held dropped with active | disposed
  · exact Or.inl active
  · refine Or.inr ⟨disposed.1, resources.observeDispatch_adopted_requested inventories before event
      producer (.stream key) ?_ emitted listed owned ?_⟩
    · cases event <;> simp_all [normalCompletionTarget?]
    · exact List.mem_filterMap.mpr ⟨.cancelSource key, disposed.1, rfl⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
