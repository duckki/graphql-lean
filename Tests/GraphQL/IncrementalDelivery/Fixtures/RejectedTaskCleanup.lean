import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AdoptedSourceRecords
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.Conformance

/-! Generated regression for task disposal at whole-work adoption. A shared producer
returns an acquired task for an already removed co-owner; registration requests its
cleanup without changing the source/conformance contract. Native acquisition/callback
correspondence remains an independent obligation.
-/

namespace GraphQL.IncrementalDelivery.Tests
open AlternativeWorkQueue AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence TaskAt)

namespace RejectedTaskCleanup

-----------------------------------------------------------------------------------------
-- Reorder the existing generated query: fail G before the shared producer returns
-----------------------------------------------------------------------------------------

def producer : Occurrence := .executionGroup [1, 0]
def child : Occurrence := SharedOwnerFailure.heldProducer

def inputs : List (List GraphEvent) :=
  [[SharedOwnerFailure.failureG], [SharedOwnerFailure.parentSuccess]]

def schedule : EventSource (List GraphEvent) := .ofList inputs

abbrev before :=
  ((State.initialize SharedOwnerFailure.work).runNormalized
    [[SharedOwnerFailure.failureG]]).1

abbrev reduced :=
  ({ state := before } : GraphBatchResult).handleGraphEvent
    SharedOwnerFailure.parentSuccess

private theorem parentKnown
    : TaskAt SharedOwnerFailure.work producer [0, 1] none
        (.object [] (.ok (SharedOwnerFailure.data, 0))) := by
  refine ⟨[{ node := SharedOwnerFailure.groupG }, { node := SharedOwnerFailure.groupH }], [],
    .ok (SharedOwnerFailure.data, 0), SharedOwnerFailure.childWork, [], ?_, rfl, rfl⟩
  rw [SharedOwnerFailure.work_shape]
  rfl

private theorem failedKnown
    : TaskAt SharedOwnerFailure.work (.executionGroup [1, 1, 0]) [0] none
        (.object [] (.error 1)) := by
  refine ⟨[{ node := SharedOwnerFailure.groupG }], [], .error 1, .empty, [], ?_, rfl, rfl⟩
  rw [SharedOwnerFailure.work_shape]
  rfl

/-- The acquired child belongs to this exact structural producer, not an unrelated identity. -/
theorem childKnown
    : TaskAt SharedOwnerFailure.work child [0] (some producer)
        (.object [.field "box"] (.ok ([("values", .list [])], 0))) := by
  refine ⟨[{ node := SharedOwnerFailure.groupG }], [.field "box"],
    .ok ([("values", .list [])], 0), SharedOwnerFailure.streamWork, [0, 1], ?_, rfl, rfl⟩
  rw [SharedOwnerFailure.work_shape]
  rfl

/-- Same exact outcomes, fresh identities and producer readiness, with no cleanup premise. -/
theorem valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work inputs.flatten := by
  have first : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work [SharedOwnerFailure.failureG] :=
    .append .nil SharedOwnerFailure.failureG_matches
      (by simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities,
        SharedOwnerFailure.failureG])
      ⟨[0], none, _, failedKnown, by intro parent impossible; cases impossible⟩
  exact .append first SharedOwnerFailure.parent_success_matches
    (by
      simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities,
        SharedOwnerFailure.failureG, SharedOwnerFailure.parentSuccess])
    ⟨[0, 1], none, _, parentKnown, by intro parent impossible; cases impossible⟩

/-- Both inputs are actually started; H keeps the shared producer alive after G fails. -/
theorem started
    : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work inputs = true := by
  rw [SharedOwnerFailure.work_shape]
  cbv

/-- The finite source obeys exactly the reference contract at all its prefixes. -/
theorem sourceValid : schedule.ValidFor SharedOwnerFailure.work := by
  refine ⟨rfl, List.nil_prefix, ?_, ?_⟩
  · intro earlier later earlierPrefix admitted
    exact earlierPrefix.trans admitted
  · intro batches admitted
    have length : batches.length ≤ 2 := admitted.length_le
    have same := List.prefix_iff_eq_take.mp admitted
    have cases : batches.length = 0 ∨ batches.length = 1 ∨ batches.length = 2 := by omega
    rcases cases with zero | one | two
    · have empty : batches = [] := by simpa [zero] using same
      subst batches
      exact ⟨.nil, rfl⟩
    · have first : batches = [[SharedOwnerFailure.failureG]] := by simpa [one, inputs] using same
      subst batches
      exact ⟨valid.prefix ⟨[SharedOwnerFailure.parentSuccess], rfl⟩,
        by rw [SharedOwnerFailure.work_shape]; cbv⟩
    · have all : batches = inputs := by simpa [two, inputs] using same
      subst batches
      exact ⟨valid, started⟩

theorem conforms
    : Execution.WorkQueue.Conforms
        (createWorkQueueForSchedule SharedOwnerFailure.work schedule)
        SharedOwnerFailure.work :=
  createWorkQueueForScheduleConforms_holds SharedOwnerFailure.work schedule
    SharedOwnerFailure.executed SharedOwnerFailure.nonempty sourceValid

-----------------------------------------------------------------------------------------
-- Complete actual handoff and rejected-registration cleanup share one resource history
-----------------------------------------------------------------------------------------

/-- Possible early acquired computation inventory; not inferred from queue or stop records.
Connecting this observation to a particular native execution remains an independent audit.
-/
def acquired : ResourceState :=
  ResourceState.empty.set (.task child) (.owned (.producer producer))

def inventories : ProducerInventories := fun _ => [.task child]

abbrev observed :=
  acquired.observeDispatch inventories before SharedOwnerFailure.parentSuccess

/-- The pre-dispatch queue-owned resource invariant holds; this is not an inherited orphan. -/
theorem beforeRepresented : ResourcesRepresented before.queue acquired := by
  intro target owned
  by_cases selected : target = .task child
  · simp [acquired, ResourceState.set, selected] at owned
  · simp [acquired, ResourceState.set, ResourceState.empty, selected] at owned

theorem labels
    : graphEffects before.queue SharedOwnerFailure.parentSuccess = [.adopt producer] := by
  dsimp only [before]
  rw [SharedOwnerFailure.work_shape]
  cbv

theorem complete
    : CompleteAdoptionInventories acquired inventories
        (graphEffects before.queue SharedOwnerFailure.parentSuccess) := by
  rw [labels]
  intro owner emitted target owned
  have same : owner = producer := HostEffect.adopt.inj (List.mem_singleton.mp emitted)
  subst owner
  by_cases selected : target = .task child
  · simp [inventories, selected]
  · simp [acquired, ResourceState.set, ResourceState.empty, selected] at owned

theorem handoff
    : ResourceReplay ResourceState.empty
        ([.acquire (.task child) (.producer producer)] ++ observed.2) observed.1 :=
  (ResourceReplay.cons (.acquire _ _ _ rfl) (.nil _)).append
    (acquired.observeDispatch_replay inventories before SharedOwnerFailure.parentSuccess)

/-- The same complete handoff still transfers the rejected child; it is not silently omitted. -/
theorem transferred
    : (acquired.observeAdoptions inventories
        (graphEffects before.queue SharedOwnerFailure.parentSuccess)).1
        (.task child)
      = .owned .queue := by
  dsimp only [before]
  rw [SharedOwnerFailure.work_shape]
  cbv

theorem targets : reduced.effects.filterMap HostEffect.cleanupStart? = [.task child] := by
  dsimp only [reduced, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

/-- Registration requests the rejected child in the same accepted success dispatch. -/
theorem effects : reduced.effects = [.adopt producer, .abortTask child] := by
  dsimp only [reduced, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

/-- Requesting cleanup is not asynchronous settlement. -/
theorem requested : observed.1 (.task child) = .cleanupRequested .queue := by
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

/-- Registration refuses the child task's already removed owner; no live membership remains. -/
theorem unrepresented : ¬RecordTargetRepresented reduced.state.queue (.task child) := by
  intro represented
  cases represented with
  | task found linked =>
      have excludes : reduced.state.queue.groupNodes.all
          (fun group => !group.tasks.contains child) = true := by
        dsimp only [reduced, before]
        rw [SharedOwnerFailure.work_shape]
        cbv
      have absent := List.all_eq_true.mp excludes _ (List.mem_of_find?_eq_some found)
      rw [List.contains_iff_mem.mpr linked] at absent
      cases absent

/-- A later stop neither loses nor requests the already pending cleanup again. -/
theorem stoppedRequested
    : (observed.1.observeStop reduced.state).1 (.task child)
      = .cleanupRequested .queue := by
  dsimp only [observed, reduced, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

/-- Requested cleanup leaves no queue-owned lease; unacquired identities remain so. -/
theorem noQueueOwned : ∀ target, observed.1 target ≠ .owned .queue := by
  intro target owned
  by_cases selected : target = .task child
  · subst target
    rw [requested] at owned
    cases owned
  · have unchanged := acquired.observeDispatch_unacquired inventories before
      SharedOwnerFailure.parentSuccess target
      (by simp [acquired, ResourceState.set, ResourceState.empty, selected])
    rw [unchanged] at owned
    cases owned

theorem represented : ResourcesRepresented reduced.state.queue observed.1 :=
  fun target owned => False.elim (noQueueOwned target owned)

theorem covered : StopCoverage reduced.state observed.1 :=
  fun target owned => False.elim (noQueueOwned target owned)

end RejectedTaskCleanup
end GraphQL.IncrementalDelivery.Tests
