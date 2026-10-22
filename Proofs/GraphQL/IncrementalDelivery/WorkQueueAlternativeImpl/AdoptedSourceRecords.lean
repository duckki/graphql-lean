import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducedStreamNoticeCoverage

/-! Structural producer identity constructs source locations at the actual handoff.
Native identity/acquisition correspondence is independent of these generated queue proofs.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence NodeAt)

-----------------------------------------------------------------------------------------
-- Accepted structural sources acquire record locations through real registration
-----------------------------------------------------------------------------------------

/-- A source of an actually adopted producer is represented or cancelled by that dispatch.
Structural source/producer identity replaces any assumed prepared or endpoint location.
-/
def GeneratedAdoptedSourceProgress : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ producer source dependencies,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        .adopt producer ∈ graphEffects before.queue event
        → NodeAt work source .stream dependencies (some producer)
        → RecordTargetRepresented reduced.state.queue (.stream source.ref)
          ∨ .cancelSource source.ref ∈ reduced.effects

/-- Generated lowering, fresh registration and actual handler progress construct both
object-held and item-activated source locations. No resource or coverage law is assumed.
-/
theorem GeneratedAdoptedSourceProgress_holds : GeneratedAdoptedSourceProgress := by
  intro work inputs event generated valid started producer source dependencies
  dsimp only
  intro adopted known
  let before := ((State.initialize work).runNormalized inputs).1
  change .adopt producer ∈ graphEffects before.queue event at adopted
  obtain ⟨raw, priorStarted, _⟩ := generatedReplay_beforeNext generated valid started
  have projection := generatedSnapshot_projection generated valid priorStarted
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  cases event with
  | taskSuccess incoming result =>
      cases inputFound : before.queue.taskNode? incoming with
      | none => simp [graphEffects, inputFound] at adopted
      | some input =>
          have same : producer = incoming := by
            simpa only [graphEffects, inputFound, List.mem_singleton,
              HostEffect.adopt.injEq]
              using adopted
          subst producer
          have rawFound := inputFound
          rw [raw] at rawFound
          obtain ⟨node, found, _, value, held⟩ := generated.taskSuccess_prepared_childStream
            prior matching fresh rawFound (matching.taskChildStreams_complete known)
          have prepared :
              (registrationSnapshot before.queue (.taskSuccess incoming result)).taskNode?
                incoming = some node := by
            apply projection.buffered
            · change (eagerRegistrationSnapshot before.queue
                (.taskSuccess incoming result)).taskNode? incoming = some node
              simp only [eagerRegistrationSnapshot, inputFound]
              rw [raw]
              exact found
            · rw [value]; rfl
          exact GeneratedPreparedSourceProgress_holds work inputs _ generated valid
            started trivial incoming node source.ref prepared (by rw [value]; rfl)
            held
  | streamItems stream items =>
      cases active : before.queue.rootStreams.contains stream.ref with
      | false => simp only [graphEffects, active, Bool.false_eq_true, ↓reduceIte,
          List.nil_append, List.mem_singleton, reduceCtorEq] at adopted
      | true =>
          have listed : .adopt producer ∈ items.map (fun item => HostEffect.adopt item.occurrence) := by
            simpa only [graphEffects, active, ↓reduceIte, List.mem_append,
              List.mem_singleton, reduceCtorEq, or_false]
              using adopted
          obtain ⟨item, selected, same⟩ := List.mem_map.mp listed
          have identity : item.occurrence = producer := HostEffect.adopt.inj same
          have rawActive := active
          rw [raw] at rawActive
          have notice := generated.streamItems_child_notice prior matching fresh rawActive
            selected (identity.symm ▸ known)
          rw [← raw] at notice
          have dispatch := generatedReplay_dispatchProjection generated valid started
          apply Or.inl
          apply RecordTargetRepresented.activeStream
          change source.ref ∈ (before.handleGraphEvent (.streamItems stream items)).1.queue.rootStreams
          rw [congrArg (fun pair => pair.1.rootStreams) dispatch]
          exact before.queue.streamItems_streamRoots_cover stream items
            (List.mem_append_right _ notice)
  | taskFailure | streamSuccess => cases adopted
  | streamFailure stream errors =>
      simp only [graphEffects] at adopted
      split at adopted <;> simp at adopted

-----------------------------------------------------------------------------------------
-- Separate source identity correspondence from native inventory completeness
-----------------------------------------------------------------------------------------

/-- Only actual acquired/listed source leases of accepted producers need a structural
identity. This is a native abstraction-map obligation, not an endpoint/cleanup law;
the generated theorem constructs their record locations from this identity.
-/
def ProducerSourcesMatchWork (work : Work) (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    : Prop :=
  ∀ producer key,
    .adopt producer ∈ effects
    → .stream key ∈ inventories producer
    → resources (.stream key) = .owned (.producer producer)
    → ∃ source dependencies,
        source.ref = key ∧ NodeAt work source .stream dependencies (some producer)

/-- Current source-only ownership invariant; task leases and complete acquired inventories
are separate. It describes real record locations rather than computed cleanup targets.
-/
def SourcesRepresented (queue : ReferenceWorkQueue.State) (resources : ResourceState)
    : Prop :=
  ∀ key,
    resources (.stream key) = .owned .queue → RecordTargetRepresented queue (.stream key)

/-- Inspect an adoption fold backwards: a queue-owned lease was already queue-owned,
or one actual listed producer lease was transferred. No acquisition can be hidden here.
-/
theorem ResourceState.observeAdoptions_queueOwned_origin (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    (target : CleanupTarget)
    (owned : (resources.observeAdoptions inventories effects).1 target = .owned .queue)
    : resources target = .owned .queue
      ∨ ∃ producer,
          .adopt producer ∈ effects
          ∧ target ∈ inventories producer
          ∧ resources target = .owned (.producer producer) := by
  induction effects generalizing resources with
  | nil => exact Or.inl owned
  | cons effect rest ih =>
      cases effect with
      | adopt producer =>
          rcases ih (resources.adopt producer (inventories producer)) owned with earlier | transferred
          · unfold ResourceState.adopt at earlier
            split at earlier
            · rename_i selected
              exact Or.inr ⟨producer, List.mem_cons_self, selected.1, selected.2⟩
            · exact Or.inl earlier
          · obtain ⟨owner, emitted, listed, lease⟩ := transferred
            exact Or.inr ⟨owner, List.mem_cons_of_mem _ emitted, listed,
              resources.adopt_producerOwned_before _ _ _ _ lease⟩
      | acknowledge | abortTask | cancelSource | abortStreamQueue | responseFinished =>
          exact (ih resources owned).imp_right (by
            rintro ⟨producer, emitted, listed, lease⟩
            exact ⟨producer, List.mem_cons_of_mem _ emitted, listed, lease⟩)

/-- Normal completion cannot create ownership, and cannot change a producer-owned identity.
This backwards statement supplies the independent pre-handoff lease for source correspondence.
-/
theorem ResourceState.observeNormalCompletion_owned_origin (resources : ResourceState)
    (before : ReferenceWorkQueue.State) (event : GraphEvent) (target : CleanupTarget)
    (owner : ResourceOwner)
    (owned : (resources.observeNormalCompletion before event).1 target = .owned owner)
    : resources target = .owned owner := by
  by_cases initial : resources target = .owned .queue
  · unfold ResourceState.observeNormalCompletion at owned
    split at owned
    · exact owned
    · rename_i completed _
      by_cases same : target = completed
      · subst target
        rw [resources.finishQueueTarget_owned completed initial] at owned
        cases owned
      · rwa [resources.finishQueueTarget_other _ _ same] at owned
  · rwa [resources.observeNormalCompletion_foreign _ _ _ initial] at owned

/-- Generated dispatch preserves the source ownership invariant. The only native leaf is
structural identity of actual incoming producer leases, not their desired record coverage.
-/
def GeneratedDispatchSourcesRepresented : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories),
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        SourcesRepresented before.queue resources
        → ProducerSourcesMatchWork work resources inventories
            (graphEffects before.queue event)
        → SourcesRepresented reduced.state.queue
            (resources.observeDispatch inventories before event).1

/-- Checked invariant composition at the same generated input, resource state and handoff.
Previously owned sources use preservation; transferred sources use structural registration.
-/
theorem GeneratedDispatchSourcesRepresented_of_progress
    (progress : GeneratedAdoptedSourceProgress)
    : GeneratedDispatchSourcesRepresented := by
  intro work inputs event generated valid started resources inventories
  dsimp only
  intro represented identities key owned
  obtain ⟨adopted, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.stream key) owned
  rcases ResourceState.observeAdoptions_queueOwned_origin _ _ _ (.stream key) adopted with
    earlier | transferred
  · have original := resources.observeNormalCompletion_owned_origin _ _ _ .queue earlier
    exact GeneratedDispatchExistingSourceRepresentation_holds work inputs event generated
      valid started resources inventories key (represented key original) owned
  · obtain ⟨producer, emitted, listed, lease⟩ := transferred
    have original := resources.observeNormalCompletion_owned_origin _ _ _ (.producer producer) lease
    obtain ⟨source, dependencies, same, known⟩ := identities producer key emitted listed original
    rcases progress work inputs event generated valid started producer source dependencies emitted known with
      retained | cancelled
    · exact same ▸ retained
    · obtain ⟨_, absent⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.stream key) owned
      exact False.elim (absent (List.mem_filterMap.mpr ⟨.cancelSource key, same ▸ cancelled, rfl⟩))

/-- Universal actual-dispatch source preservation with independent structural identities. -/
theorem GeneratedDispatchSourcesRepresented_holds : GeneratedDispatchSourcesRepresented :=
  GeneratedDispatchSourcesRepresented_of_progress GeneratedAdoptedSourceProgress_holds

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
