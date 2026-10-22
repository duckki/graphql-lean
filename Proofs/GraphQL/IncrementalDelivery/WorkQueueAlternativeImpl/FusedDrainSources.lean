import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedDrainProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureResources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedCleanupTargets
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRequests
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamInventoryReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamReleaseCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredValueRetention

/-! Source progress through actual mixed draining. A successful flush transfers held sources
into active roots; a failed removal returns their real cleanup identities. The same queue,
owner frame, inventory and cumulative target list are carried through every bounded step.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (NodeRefs Occurrence)
open ReferenceWorkQueue (TaskNode)

-----------------------------------------------------------------------------------------
-- Active sources survive the real mixed drain
-----------------------------------------------------------------------------------------

private theorem drain_active {state : State} {work : Work} {parents : Nat → NodeRefs}
    (running : state.stopped = false) (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents) (fuel : Nat)
    (targets : List CleanupTarget) {key : Nat} (active : key ∈ state.queue.rootStreams)
    : key ∈ (State.drainReadyGroups.go fuel state targets).1.queue.rootStreams := by
  rw [congrArg (fun result => result.1.rootStreams)
    (state.drainReadyGroups_go_projection running frame forest fuel targets)]
  exact ReferenceWorkQueue.State.drainReadyGroups_go_streamRoots_cover fuel state.queue
    (List.mem_append_left _ active)

private theorem targets_survive (fuel : Nat) (state : State)
    (targets : List CleanupTarget) (unique : targets.Nodup) {target : CleanupTarget}
    (member : target ∈ targets)
    : target ∈ (State.drainReadyGroups.go fuel state targets).2.2 := by
  obtain ⟨suffix, same⟩ := (state.drainReadyGroups_go_targets fuel targets unique).2
  rw [← same]
  exact List.mem_append_left _ member

-----------------------------------------------------------------------------------------
-- Held records retain, transfer, or enter the actual cleanup accumulator
-----------------------------------------------------------------------------------------

/-- Local bounded source progress on a compatible owner/forest/inventory frame.
No output-scan cleanup algorithm, failure frontier cut or desired endpoint is assumed.
The frames are ordinary implementation invariants, independently derived at generated
prefixes and transported here along the actual transitions.
-/
theorem drain_heldSource {state : State} {work : Work} {parents : Nat → NodeRefs}
    (running : state.stopped = false) (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents)
    (inventory : state.queue.ChildStreamInventory) (fuel : Nat)
    (targets : List CleanupTarget) (unique : targets.Nodup) {occurrence : Occurrence}
    {node : TaskNode} {key : Nat} (found : state.queue.taskNode? occurrence = some node)
    (held : key ∈ node.childStreams)
    : let reduced := State.drainReadyGroups.go fuel state targets
      reduced.1.queue.taskNode? occurrence = some node
      ∨ key ∈ reduced.1.queue.rootStreams
      ∨ .stream key ∈ reduced.2.2 := by
  induction fuel generalizing state targets with
  | zero => exact .inl found
  | succ fuel ih =>
      rw [State.drainReadyGroups_go_eq]
      cases selected : fusedReadyGroup state.queue with
      | none => exact .inl found
      | some group =>
          simp only
          cases cached : state.queue.rejectedTask? group with
          | some rejection =>
              obtain ⟨failed, errors⟩ := rejection
              simp only
              let reduced := state.taskFailure failed errors targets
              have projection := state.taskFailure_projection frame forest failed errors targets
              have same : reduced.1.queue = (state.queue.taskFailure failed errors).1 :=
                congrArg Prod.fst projection
              have nextFrame : reduced.1.queue.TaskOwnerFrame work := by
                rw [same]; exact frame.taskFailure failed errors
              have nextForest : reduced.1.queue.RemovalForest parents := by
                rw [same]
                exact forest.of_subset (state.queue.taskFailure_groupNodes_sublist failed errors).subset
              have nextInventory : reduced.1.queue.ChildStreamInventory := by
                rw [same]; exact inventory.taskFailure failed errors
              have nextUnique := (state.taskFailure_targets failed errors targets unique).1
              have nextRunning := (state.taskFailure_stopped failed errors targets).trans running
              have unchanged : occurrence ≠ failed ∨ node.rejection = some errors := by
                by_cases sameOccurrence : occurrence = failed
                · subst occurrence
                  obtain ⟨_, task, lookup, rejected⟩ := ReferenceWorkQueue.State.rejectedTask?_sound cached
                  have identical : task = node := Option.some.inj (lookup.symm.trans found)
                  exact .inr (identical ▸ rejected)
                · exact .inl sameOccurrence
              rcases state.taskFailure_heldSource_targets failed errors targets unchanged
                  found held with kept | requested
              · exact ih nextRunning nextFrame nextForest nextInventory reduced.2.2 nextUnique kept
              · exact .inr (.inr
                  (targets_survive fuel reduced.1 reduced.2.2 nextUnique requested))
          | none =>
              simp only
              let released := state.queue.finishGroupSuccess group
              let started := ({ state with queue := released.1 }).startNewWork released.2.2 {} targets
              have same : started.1.queue = released.1.startNewWork released.2.2 := by
                simpa only [List.foldl_nil]
                  using State.startNewWork_queue
                    { state with queue := released.1 } released.2.2 {} targets running
              have nextFrame : started.1.queue.TaskOwnerFrame work := by
                rw [same]; exact (frame.finishGroupSuccess group (fusedReadyGroup_member selected)).startNewWork _
              have nextForest : started.1.queue.RemovalForest parents := by
                rw [same]; exact (forest.finishGroupSuccess group).startNewWork _
              have nextInventory : started.1.queue.ChildStreamInventory := by
                rw [same]; exact (inventory.finishGroupSuccess group).startNewWork _
              have nextRunning := (State.startNewWork_stopped
                { state with queue := released.1 } released.2.2 {} targets).trans running
              have nextUnique := State.startNewWork_targets_nodup
                { state with queue := released.1 } released.2.2 {} targets unique
              by_cases listed : occurrence ∈ group.tasks
              · have transferred : key ∈ started.1.queue.rootStreams := by
                  rw [same]
                  have releasedKey := inventory.finishGroupSuccess_childRef_covered group listed found held
                  have noticed := state.queue.finishGroupSuccess_streamNotices group ▸ releasedKey
                  exact state.queue.finishGroupSuccess_streamRoots_cover group
                    (List.mem_append_right _ noticed)
                exact .inr (.inl (drain_active nextRunning nextFrame nextForest fuel started.2 transferred))
              · have retained : started.1.queue.taskNode? occurrence = some node := by
                  rw [same]
                  apply ReferenceWorkQueue.State.startNewWork_lookup_existing _ released.2.2
                  exact (state.queue.finishGroupSuccess_lookup_unselected group listed).trans found
                exact ih nextRunning nextFrame nextForest nextInventory started.2 nextUnique retained

/-- Named exact local source-progress target for actual mixed draining. -/
def FusedDrainSourceProgress : Prop :=
  ∀ (state : State) (work : Work) (parents : Nat → NodeRefs)
    (targets : List CleanupTarget),
    state.stopped = false
    → state.queue.TaskOwnerFrame work
    → state.queue.RemovalForest parents
    → state.queue.ChildStreamInventory
    → targets.Nodup
    → ∀ occurrence node key,
        state.queue.taskNode? occurrence = some node
        → key ∈ node.childStreams
        → let reduced := state.drainReadyGroups targets
          reduced.1.queue.taskNode? occurrence = some node
          ∨ key ∈ reduced.1.queue.rootStreams
          ∨ .stream key ∈ reduced.2.2

theorem FusedDrainSourceProgress_holds : FusedDrainSourceProgress := by
  intro state work parents targets running frame forest inventory unique occurrence node key found held
  exact drain_heldSource running frame forest inventory _ targets unique found held

-----------------------------------------------------------------------------------------
-- Construct generated frames and a compatible acquired-resource request history
-----------------------------------------------------------------------------------------

/-- Generated reference-prefix target: all local frames are constructed from the original
source contract, not exported as new caller premises. The transition is the actual
alternative drain starting at that prefix.
-/
def GeneratedReferenceDrainSourceProgress : Prop :=
  ∀ (work : Work) (batches : List (List GraphEvent)),
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work batches.flatten
    → ReferenceWorkQueue.inputsStarted work batches = true
    → ∀ (targets : List CleanupTarget),
        targets.Nodup
        → let queue :=
            ((ReferenceWorkQueue.State.initialize
                (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
              batches).1
          ∀ occurrence node key,
            queue.taskNode? occurrence = some node
            → key ∈ node.childStreams
            → let reduced := ({ queue } : State).drainReadyGroups targets
              reduced.1.queue.taskNode? occurrence = some node
              ∨ key ∈ reduced.1.queue.rootStreams
              ∨ .stream key ∈ reduced.2.2

theorem GeneratedReferenceDrainSourceProgress_holds
    : GeneratedReferenceDrainSourceProgress := by
  intro work batches generated valid started targets unique
  obtain ⟨parents, forest⟩ := generated.runNormalized_removalForest batches valid
  have frame := generated.runNormalized_taskOwnerFrame batches valid started
  have inventory := ReferenceWorkQueue.createWorkQueue_runNormalized_childStreamInventory
    (ReferenceWorkQueue.Work.fromExecution work) batches
  let queue := ((ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).runNormalized batches).1
  exact FusedDrainSourceProgress_holds { queue } work parents targets rfl frame forest inventory unique

/-- Observe the actual cumulative drain targets. A handler emitting only a new suffix must
separately account for its earlier target prefix; this observer does not infer that boundary.
-/
def ResourceState.observeReadyDrain (resources : ResourceState) (state : State)
    (targets : List CleanupTarget)
    : ResourceState × List ResourceAction :=
  resources.requestQueueCleanup (state.drainReadyGroups targets).2.2

/-- The same actual mixed-drain endpoint and resource history retain a held record, activate
its source, or request its queue-owned lease. No native acquisitions or async settlement
are manufactured. FusedTaskSources and FusedStreamSources compose the handler bridges.
-/
theorem readyDrain_resourceSafety {state : State} {work : Work} {parents : Nat → NodeRefs}
    (running : state.stopped = false) (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents)
    (inventory : state.queue.ChildStreamInventory) (targets : List CleanupTarget)
    (unique : targets.Nodup) (resources : ResourceState)
    : let reduced := state.drainReadyGroups targets
      let observed := resources.observeReadyDrain state targets
      ResourceReplay resources observed.2 observed.1
      ∧ (∀ action ∈ observed.2,
          ∃ effect ∈ reduced.2.2.flatMap CleanupTarget.effects,
            ∃ target,
              effect.cleanupStart? = some target ∧ action = .requestCleanup target)
      ∧ ∀ occurrence node key,
          state.queue.taskNode? occurrence = some node
          → key ∈ node.childStreams
          → resources (.stream key) = .owned .queue
          → reduced.1.queue.taskNode? occurrence = some node
            ∨ key ∈ reduced.1.queue.rootStreams
            ∨ observed.1 (.stream key) = .cleanupRequested .queue := by
  refine ⟨resources.requestQueueCleanup_replay _, ?_, ?_⟩
  · intro action member
    obtain ⟨target, listed, same⟩ := resources.requestQueueCleanup_actions _ _ member
    have identified : target ∈ ((state.drainReadyGroups targets).2.2.flatMap
        CleanupTarget.effects).filterMap HostEffect.cleanupStart? := by
      rwa [cleanupEffects_starts]
    obtain ⟨effect, emitted, identifies⟩ := List.mem_filterMap.mp identified
    exact ⟨effect, emitted, target, identifies, same⟩
  · intro occurrence node key found held owned
    rcases FusedDrainSourceProgress_holds state work parents targets running frame forest
        inventory unique occurrence node key found held with retained | active | requested
    · exact .inl retained
    · exact .inr (.inl active)
    · exact .inr (.inr (resources.requestQueueCleanup_owned _ _ requested owned))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
