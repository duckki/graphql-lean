import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedFusedRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalGuards
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainRootCoverage

/-! Actual successful draining projects its queue, immediate output and startup notices.
Inline cleanup remains the alternative's separate returned component.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs Occurrence)

/-- The actual drain selects only a zero-pending active group. -/
def fusedReadyGroup (queue : ReferenceWorkQueue.State)
    : Option ReferenceWorkQueue.GroupNode :=
  queue.rootGroups.findSome?
    fun key => do
      let node ← queue.groupNode? key
      if node.pending == 0 then some node else none

/-- A ready lookup identifies a current live record. -/
theorem fusedReadyGroup_member {queue : ReferenceWorkQueue.State}
    {group : ReferenceWorkQueue.GroupNode} (selected : fusedReadyGroup queue = some group)
    : group ∈ queue.groupNodes := by
  obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
  cases found : queue.groupNode? key with
  | none => simp [found] at choice
  | some node =>
      rw [found] at choice
      change (if node.pending == 0 then some node else none) = some group at choice
      split at choice
      · exact Option.some.inj choice ▸ List.mem_of_find?_eq_some found
      · cases choice

/-- One actual drain step releases success, starts children, then continues with cleanup. -/
theorem State.drainReadyGroups_go_eq (fuel : Nat) (state : State)
    (targets : List CleanupTarget) (available : List (Occurrence × Nat) := [])
    : State.drainReadyGroups.go available (fuel + 1) state targets
      = match fusedReadyGroup state.queue with
        | none => (state, [], targets, [])
        | some node =>
            let released := state.queue.finishGroupSuccess node
            let started :=
              ({ state with queue := released.1 }).startNewWork released.2.2 {}
                targets available
            let later := State.drainReadyGroups.go available fuel started.1 started.2.1
            (
              later.1,
              released.2.1 ++ later.2.1,
              later.2.2.1,
              started.2.2 ++ later.2.2.2
            ) :=
  rfl

private theorem reference_go_eq (fuel : Nat) (queue : ReferenceWorkQueue.State)
    (available : List (Occurrence × Nat))
    : ReferenceWorkQueue.State.drainReadyGroups.go available (fuel + 1) queue
      = match fusedReadyGroup queue with
        | none => (queue, [], [])
        | some node =>
            let released := queue.finishGroupSuccess node
            let started := released.1.startNewWork released.2.2 available
            let later :=
              ReferenceWorkQueue.State.drainReadyGroups.go available fuel started.1
            (later.1, released.2.1 ++ later.2.1, started.2 ++ later.2.2) :=
  rfl

/-- Every bounded actual drain agrees on state, immediate events and queued startup notices.
The concrete pre-startup frames justify fused failure removal inside child activation.
Cleanup targets retain their independently observed order in the actual fourth-tuple result.
-/
theorem State.drainReadyGroups_go_projection {state : State} {work : Work}
    {parents : Nat → NodeRefs} (running : state.stopped = false)
    (frame : state.queue.TaskOwnerFrame work) (forest : state.queue.RemovalForest parents)
    (fuel : Nat) (targets : List CleanupTarget)
    (available : List (Occurrence × Nat) := [])
    : let actual := State.drainReadyGroups.go available fuel state targets
      (actual.1.queue, actual.2.1, actual.2.2.2)
      = ReferenceWorkQueue.State.drainReadyGroups.go available fuel state.queue := by
  induction fuel generalizing state targets with
  | zero => rfl
  | succ fuel ih =>
      rw [State.drainReadyGroups_go_eq fuel state targets available,
        reference_go_eq fuel state.queue available]
      cases selected : fusedReadyGroup state.queue with
      | none => rfl
      | some node =>
          dsimp only
          let released := state.queue.finishGroupSuccess node
          let started := ({ state with queue := released.1 }).startNewWork released.2.2 {}
            targets available
          have releasedFrame := frame.finishGroupSuccess node (fusedReadyGroup_member selected)
          have releasedForest := forest.finishGroupSuccess node
          have same : (started.1.queue, started.2.2)
              = released.1.startNewWork released.2.2 available := by
            simpa only [List.foldl_nil]
              using State.startNewWork_projects { state with queue := released.1 }
                released.2.2 {} targets running available releasedFrame releasedForest
          have queueEq : started.1.queue
              = (released.1.startNewWork released.2.2 available).1 := congrArg Prod.fst same
          have noticesEq : started.2.2
              = (released.1.startNewWork released.2.2 available).2 := congrArg Prod.snd same
          have nextFrame : started.1.queue.TaskOwnerFrame work := by
            rw [queueEq]
            exact releasedFrame.startNewWork _ available
          have nextForest : started.1.queue.RemovalForest parents := by
            rw [queueEq]
            exact releasedForest.startNewWork _ available
          have next := ih ((State.startNewWork_stopped
              { state with queue := released.1 } released.2.2 {} targets available).trans running)
            nextFrame nextForest started.2.1
          rw [queueEq] at next
          change ((State.drainReadyGroups.go available fuel started.1 started.2.1).1.queue,
            released.2.1 ++ (State.drainReadyGroups.go available fuel started.1 started.2.1).2.1,
            started.2.2
              ++ (State.drainReadyGroups.go available fuel started.1 started.2.1).2.2.2) = _
          rw [noticesEq]
          exact congrArg (fun result =>
            (result.1, released.2.1 ++ result.2.1,
              (released.1.startNewWork released.2.2 available).2 ++ result.2.2)) next

/-- Full-budget draining preserves both reference reporting channels at the same snapshot. -/
theorem State.drainReadyGroups_projection {state : State} {work : Work}
    {parents : Nat → NodeRefs} (running : state.stopped = false)
    (frame : state.queue.TaskOwnerFrame work) (forest : state.queue.RemovalForest parents)
    (targets : List CleanupTarget) (available : List (Occurrence × Nat) := [])
    : (
        (state.drainReadyGroups targets available).1.queue,
        (state.drainReadyGroups targets available).2.1,
        (state.drainReadyGroups targets available).2.2.2
      )
      = state.queue.drainReadyGroups available :=
  state.drainReadyGroups_go_projection running frame forest _ targets available

/-- Fused draining preserves a supplied exposed registration-state relation.
Witness: concrete owner/forest certificates give the fused projection, and the reference
recursive drain preserves common cache exposure together with immediate and queued output.
-/
theorem State.drainReadyGroups_projects_after_cache {state : State} {work : Work}
    {parents : Nat → NodeRefs} (running : state.stopped = false)
    (frame : state.queue.TaskOwnerFrame work) (forest : state.queue.RemovalForest parents)
    (targets : List CleanupTarget) (available : List (Occurrence × Nat))
    (unique : state.queue.TaskNodeKeysUnique) (reference : ReferenceWorkQueue.State)
    (referenceUnique : reference.TaskNodeKeysUnique)
    (same
      : state.queue.cacheTaskFailures available = reference.cacheTaskFailures available)
    : (
        (state.drainReadyGroups targets available).1.queue.cacheTaskFailures available,
        (state.drainReadyGroups targets available).2.1,
        (state.drainReadyGroups targets available).2.2.2
      )
      = (
        (reference.drainReadyGroups available).1.cacheTaskFailures available,
        (reference.drainReadyGroups available).2
      ) := by
  have projected := state.drainReadyGroups_projection running frame forest targets available
  have exposed := congrArg
    (fun result : ReferenceWorkQueue.State × List Execution.WorkQueueEvent
        × List ReferenceWorkQueue.GroupFailureEvent =>
      (result.1.cacheTaskFailures available, result.2)) projected
  exact exposed.trans (reference_drainReadyGroups_cache_congr unique referenceUnique available same)

/-- Exact drain projection under its compatible concrete owner and forest frames. -/
def FusedDrainProjection : Prop :=
  ∀ (state : State) (work : Work) (parents : Nat → NodeRefs)
    (targets : List CleanupTarget) (available : List (Occurrence × Nat)),
    state.stopped = false
    → state.queue.TaskOwnerFrame work
    → state.queue.RemovalForest parents
    → (
        (state.drainReadyGroups targets available).1.queue,
        (state.drainReadyGroups targets available).2.1,
        (state.drainReadyGroups targets available).2.2.2
      )
      = state.queue.drainReadyGroups available

/-- The actual fused loop supplies the complete local drain projection. -/
theorem FusedDrainProjection_holds : FusedDrainProjection := by
  intro state work parents targets available running frame forest
  exact state.drainReadyGroups_projection running frame forest targets available

/-- Generated actual replay derives the concrete drain frame before applying projection. -/
def GeneratedReferenceDrainProjection : Prop :=
  ∀ (work : Work) (batches : List (List GraphEvent)),
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work batches.flatten
    → ReferenceWorkQueue.inputsStarted work batches = true
    → ∀ (targets : List CleanupTarget) (available : List (Occurrence × Nat)),
        let queue :=
          ((ReferenceWorkQueue.State.initialize
              (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
            batches).1
        let actual := ({ queue } : State).drainReadyGroups targets available
        (actual.1.queue, actual.2.1, actual.2.2.2) = queue.drainReadyGroups available

/-- Actual generated endpoints supply ownership and finite removal frames independently. -/
theorem GeneratedReferenceDrainProjection_holds : GeneratedReferenceDrainProjection := by
  intro work batches generated valid started targets available
  obtain ⟨parents, forest⟩ := generated.runNormalized_removalForest batches valid
  exact FusedDrainProjection_holds _ work parents targets available rfl
    (generated.runNormalized_taskOwnerFrame batches valid started) forest

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
