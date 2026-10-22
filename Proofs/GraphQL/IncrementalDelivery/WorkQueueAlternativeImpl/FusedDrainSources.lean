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
    : key ∈ (State.drainReadyGroups.go [] fuel state targets).1.queue.rootStreams := by
  rw [congrArg (fun result => result.1.rootStreams)
    (state.drainReadyGroups_go_projection running frame forest fuel targets)]
  exact ReferenceWorkQueue.State.drainReadyGroups_go_streamRoots_cover fuel state.queue []
    (List.mem_append_left _ active)

private theorem targets_survive (fuel : Nat) (state : State)
    (targets : List CleanupTarget) (unique : targets.Nodup) {target : CleanupTarget}
    (member : target ∈ targets)
    : target ∈ (State.drainReadyGroups.go [] fuel state targets).2.2.1 := by
  obtain ⟨suffix, same⟩ := (state.drainReadyGroups_go_targets fuel targets unique).2
  rw [← same]
  exact List.mem_append_left _ member

-----------------------------------------------------------------------------------------
-- Held records retain, transfer, or enter the actual cleanup accumulator
-----------------------------------------------------------------------------------------

private theorem startup_group_safety (state : State) (ref : Nat)
    (targets : List CleanupTarget)
    : targets.Subset (state.startGroup ref targets).2.1
      ∧ ∀ occurrence node key,
          state.queue.taskNode? occurrence = some node
          → key ∈ node.childStreams
          → (state.startGroup ref targets).1.queue.taskNode? occurrence = some node
            ∨ .stream key ∈ (state.startGroup ref targets).2.1 := by
  unfold State.startGroup
  dsimp only
  split
  · exact ⟨List.Subset.refl _, fun _ _ _ found _ => .inl found⟩
  · rename_i group selected
    split
    · refine ⟨List.Subset.refl _, ?_⟩
      intro occurrence node key found held
      apply Or.inl
      have loop (tasks : List Occurrence) (queue : ReferenceWorkQueue.State)
          (known : queue.taskNode? occurrence = some node)
          : (tasks.foldl (fun current task => current.startTask task []) queue).taskNode?
              occurrence = some node := by
        induction tasks generalizing queue with
        | nil => exact known
        | cons task rest ih =>
            exact ih _ (ReferenceWorkQueue.State.startTask_lookup_existing known task)
      exact loop _ _ found
    · have safety := FusedRemovalSafety_holds state group.group.node.ref targets
      exact ⟨safety.1, safety.2.2⟩

/-- Released-group startup either retains a held record or supplies its inline cleanup.
The empty supplied snapshot permits exact record retention; cached group failures still
run their actual removal and extend the same cumulative targets.
-/
theorem startup_heldSource (state : State) (more : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget) {occurrence node key}
    (found : state.queue.taskNode? occurrence = some node)
    (held : key ∈ node.childStreams)
    : (state.startNewWork more integrated targets).1.queue.taskNode? occurrence
        = some node
      ∨ .stream key ∈ (state.startNewWork more integrated targets).2.1 := by
  have groups (refs : NodeRefs)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      (prior : acc.1.queue.taskNode? occurrence = some node ∨ .stream key ∈ acc.2.1)
      : let result := refs.foldl (fun (current, targets, failures) ref =>
          let (next, targets, queued) := current.startGroup ref targets []
          (next, targets, failures ++ queued)) acc
        result.1.queue.taskNode? occurrence = some node ∨ .stream key ∈ result.2.1 := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        have step := startup_group_safety acc.1 ref acc.2.1
        rcases prior with kept | requested
        · exact step.2 occurrence node key kept held
        · exact .inr (step.1 requested)
  have streams (items : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
      (known : queue.taskNode? occurrence = some node)
      : (items.foldl (fun current stream => current.startStream stream.ref) queue).taskNode?
          occurrence = some node := by
    induction items generalizing queue with
    | nil => exact known
    | cons stream rest ih =>
        apply ih
        unfold ReferenceWorkQueue.State.startStream
        dsimp only
        split <;> exact known
  have tasks (more : List ReferenceWorkQueue.Task) (queue : ReferenceWorkQueue.State)
      (known : queue.taskNode? occurrence = some node)
      : (more.foldl (fun current task => current.startTask task.occurrence []) queue).taskNode?
          occurrence = some node := by
    induction more generalizing queue with
    | nil => exact known
    | cons task rest ih =>
        exact ih _ (ReferenceWorkQueue.State.startTask_lookup_existing known task.occurrence)
  unfold State.startNewWork
  split
  · exact .inl found
  · exact groups _ _ (.inl (tasks integrated.activeTasks _ (streams more.newStreams _ found)))

private theorem removal_taskFold_rootStreams (tasks : List Occurrence)
    (acc : State × List CleanupTarget)
    : (tasks.foldl fusedRemovalTaskStep acc).1.queue.rootStreams
      = acc.1.queue.rootStreams := by
  induction tasks generalizing acc with
  | nil => rfl
  | cons task rest ih =>
      rw [List.foldl_cons, ih]
      unfold fusedRemovalTaskStep
      split
      · rfl
      · split <;> rfl

private theorem removal_walk_rootStreams (fuel : Nat) (state : State)
    (pending removed : NodeRefs) (targets : List CleanupTarget)
    : (State.removeGroup.walk fuel state pending removed targets).1.queue.rootStreams
      = state.queue.rootStreams := by
  induction fuel generalizing state pending removed targets with
  | zero => simp only [State.removeGroup.walk]
  | succ fuel ih =>
      induction pending generalizing state removed targets with
      | nil => simp only [State.removeGroup.walk]
      | cons ref rest tailIH =>
          cases found : state.queue.groupNode? ref with
          | none =>
              simpa only [State.removeGroup.walk, found] using tailIH state removed targets
          | some group =>
              rw [State.removeGroup.walk, found]
              let folded := group.tasks.foldl fusedRemovalTaskStep
                (eraseRemovalGroup state ref, targets)
              exact (ih folded.1 (group.childGroups ++ rest) (ref :: removed) folded.2
                ).trans (removal_taskFold_rootStreams group.tasks
                  (eraseRemovalGroup state ref, targets))

/-- Inline group removal preserves independently active source roots. -/
theorem State.removeGroup_rootStreams (state : State) (ref : Nat)
    (targets : List CleanupTarget)
    : (state.removeGroup ref targets).1.queue.rootStreams = state.queue.rootStreams :=
  removal_walk_rootStreams _ state [ref] [] targets

private theorem startup_group_rootStreams (state : State) (ref : Nat)
    (targets : List CleanupTarget) (available : List (Occurrence × Nat))
    : (state.startGroup ref targets available).1.queue.rootStreams
      = state.queue.rootStreams := by
  have tasks (more : List Occurrence) (queue : ReferenceWorkQueue.State)
      : (more.foldl (fun current task => current.startTask task available) queue).rootStreams
        = queue.rootStreams := by
    induction more generalizing queue with
    | nil => rfl
    | cons task rest ih =>
        rw [List.foldl_cons, ih]
        unfold ReferenceWorkQueue.State.startTask
        split
        · rfl
        · split <;> rfl
  have cachedRoots := congrArg ReferenceWorkQueue.State.rootStreams
    (state.queue.cacheTaskFailures_frame available)
  change (state.queue.cacheTaskFailures available).rootStreams = state.queue.rootStreams
    at cachedRoots
  unfold State.startGroup
  dsimp only
  split
  · exact cachedRoots
  · split
    · exact (tasks _ _).trans cachedRoots
    · exact (removal_walk_rootStreams _ _ _ _ _).trans cachedRoots

/-- Released startup activates each registered source and retains old source roots.
Witness: sources start before the group fold; task starts and actual inline failed-group
removal preserve those roots even when they dispose held source records.
-/
theorem startup_streamRoots_available (state : State) (more : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget)
    (running : state.stopped = false)
    (registered
      : more.newStreams.Subset (state.queue.streams.map ReferenceWorkQueue.Stream.node))
    (available : List (Occurrence × Nat))
    : (state.queue.rootStreams ++ more.newStreams.map Execution.DeliveryNode.ref).Subset
        (state.startNewWork more integrated targets available).1.queue.rootStreams := by
  have streams (nodes : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
      (registered : nodes.Subset (queue.streams.map ReferenceWorkQueue.Stream.node))
      : (queue.rootStreams ++ nodes.map Execution.DeliveryNode.ref).Subset
          (nodes.foldl (fun current node => current.startStream node.ref) queue).rootStreams := by
    induction nodes generalizing queue with
    | nil =>
        simp only [List.map_nil, List.append_nil, List.foldl_nil]
        exact fun _ member => member
    | cons node rest ih =>
        have next := ih (queue.startStream node.ref) (by
          rw [ReferenceWorkQueue.State.startStream_streams]
          exact fun _ member => registered (List.mem_cons_of_mem _ member))
        intro key member
        apply next
        rcases List.mem_append.mp member with old | added
        · exact List.mem_append_left _ (queue.startStream_rootStreams_mono node.ref old)
        · rcases List.mem_cons.mp added with same | later
          · exact List.mem_append_left _ (same.symm ▸ ReferenceWorkQueue.State.startStream_active
              (ReferenceWorkQueue.State.stream?_exists_of_registered
                (registered List.mem_cons_self)))
          · exact List.mem_append_right _ later
  have tasks (nodes : List ReferenceWorkQueue.Task) (queue : ReferenceWorkQueue.State)
      : (nodes.foldl (fun current task => current.startTask task.occurrence available)
          queue).rootStreams
        = queue.rootStreams := by
    induction nodes generalizing queue with
    | nil => rfl
    | cons node rest ih =>
        rw [List.foldl_cons, ih]
        unfold ReferenceWorkQueue.State.startTask
        split
        · rfl
        · split <;> rfl
  have groups (refs : NodeRefs)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      : (refs.foldl (fun (current, targets, failures) ref =>
          let (next, targets, queued) := current.startGroup ref targets available
          (next, targets, failures ++ queued)) acc).1.queue.rootStreams
        = acc.1.queue.rootStreams := by
    induction refs generalizing acc with
    | nil => rfl
    | cons ref rest ih =>
        rw [List.foldl_cons, ih]
        exact startup_group_rootStreams acc.1 ref acc.2.1 available
  unfold State.startNewWork
  rw [running]
  simp only [Bool.false_eq_true, ↓reduceIte, groups, tasks]
  exact streams more.newStreams
    { state.queue with rootGroups := state.queue.rootGroups ++
      more.newGroups.map Execution.DeliveryNode.ref } registered

/-- Empty-snapshot specialization of source-root activation and retention. -/
theorem startup_streamRoots (state : State) (more : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget)
    (running : state.stopped = false)
    (registered
      : more.newStreams.Subset (state.queue.streams.map ReferenceWorkQueue.Stream.node))
    : (state.queue.rootStreams ++ more.newStreams.map Execution.DeliveryNode.ref).Subset
        (state.startNewWork more integrated targets).1.queue.rootStreams :=
  startup_streamRoots_available state more integrated targets running registered []

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
    : let reduced := State.drainReadyGroups.go [] fuel state targets
      reduced.1.queue.taskNode? occurrence = some node
      ∨ key ∈ reduced.1.queue.rootStreams
      ∨ .stream key ∈ reduced.2.2.1 := by
  induction fuel generalizing state targets with
  | zero => exact .inl found
  | succ fuel ih =>
      rw [State.drainReadyGroups_go_eq]
      cases selected : fusedReadyGroup state.queue with
      | none => exact .inl found
      | some group =>
          simp only
          let released := state.queue.finishGroupSuccess group
          let started := ({ state with queue := released.1 }).startNewWork released.2.2 {} targets
          have releasedFrame := frame.finishGroupSuccess group (fusedReadyGroup_member selected)
          have releasedForest := forest.finishGroupSuccess group
          have projection := State.startNewWork_projects { state with queue := released.1 }
            released.2.2 {} targets running [] releasedFrame releasedForest
          have same : started.1.queue = (released.1.startNewWork released.2.2).1 := by
            simpa only [List.foldl_nil] using congrArg Prod.fst projection
          have nextFrame : started.1.queue.TaskOwnerFrame work := by
            rw [same]; exact releasedFrame.startNewWork _
          have nextForest : started.1.queue.RemovalForest parents := by
            rw [same]; exact releasedForest.startNewWork _
          have nextInventory : started.1.queue.ChildStreamInventory := by
            rw [same]; exact (inventory.finishGroupSuccess group).startNewWork _
          have nextRunning := (State.startNewWork_stopped
            { state with queue := released.1 } released.2.2 {} targets).trans running
          have nextUnique := State.startNewWork_targets_nodup
            { state with queue := released.1 } released.2.2 {} targets unique
          by_cases listed : occurrence ∈ group.tasks
          · have transferred : key ∈ started.1.queue.rootStreams := by
              rw [same]
              have releasedKey :=
                inventory.finishGroupSuccess_childRef_covered group listed found held
              have noticed := state.queue.finishGroupSuccess_streamNotices group ▸ releasedKey
              exact state.queue.finishGroupSuccess_streamRoots_cover group []
                (List.mem_append_right _ noticed)
            exact .inr (.inl
              (drain_active nextRunning nextFrame nextForest fuel started.2.1 transferred))
          · have retained : released.1.taskNode? occurrence = some node :=
              (state.queue.finishGroupSuccess_lookup_unselected group listed).trans found
            rcases startup_heldSource { state with queue := released.1 } released.2.2 {}
                targets retained held with kept | requested
            · exact ih nextRunning nextFrame nextForest nextInventory started.2.1 nextUnique kept
            · exact .inr (.inr
                (targets_survive fuel started.1 started.2.1 nextUnique requested))

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
          ∨ .stream key ∈ reduced.2.2.1

theorem FusedDrainSourceProgress_holds : FusedDrainSourceProgress := by
  intro state work parents targets running frame forest inventory unique occurrence node key
    found held
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
              ∨ .stream key ∈ reduced.2.2.1

theorem GeneratedReferenceDrainSourceProgress_holds
    : GeneratedReferenceDrainSourceProgress := by
  intro work batches generated valid started targets unique
  obtain ⟨parents, forest⟩ := generated.runNormalized_removalForest batches valid
  have frame := generated.runNormalized_taskOwnerFrame batches valid started
  have inventory := ReferenceWorkQueue.createWorkQueue_runNormalized_childStreamInventory
    (ReferenceWorkQueue.Work.fromExecution work) batches
  let queue := ((ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).runNormalized batches).1
  exact FusedDrainSourceProgress_holds { queue } work parents targets rfl frame forest
    inventory unique

/-- Observe the actual cumulative drain targets. A handler emitting only a new suffix must
separately account for its earlier target prefix; this observer does not infer that boundary.
-/
def ResourceState.observeReadyDrain (resources : ResourceState) (state : State)
    (targets : List CleanupTarget)
    : ResourceState × List ResourceAction :=
  resources.requestQueueCleanup (state.drainReadyGroups targets).2.2.1

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
          ∃ effect ∈ reduced.2.2.1.flatMap CleanupTarget.effects,
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
    have identified : target ∈ ((state.drainReadyGroups targets).2.2.1.flatMap
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
