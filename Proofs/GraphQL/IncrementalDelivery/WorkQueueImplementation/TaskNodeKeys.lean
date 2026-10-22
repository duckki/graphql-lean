import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRejections
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CacheEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks

/-! The concrete task-node map contains one record per computation occurrence. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)

/-- Computation identities are unique in the concrete task-node map. -/
def State.TaskNodeKeysUnique (queue : State) : Prop :=
  (queue.taskNodes.map (fun node => node.task.occurrence)).Nodup

/-- A unique task-node key identifies its exact list member. -/
theorem State.TaskNodeKeysUnique.lookup {queue : State}
    (unique : queue.TaskNodeKeysUnique) {node : TaskNode}
    (member : node ∈ queue.taskNodes)
    : queue.taskNode? node.task.occurrence = some node := by
  have find (nodes : List TaskNode)
      (unique : (nodes.map (fun entry => entry.task.occurrence)).Nodup)
      {node : TaskNode} (member : node ∈ nodes)
      : nodes.find? (fun entry => entry.task.occurrence == node.task.occurrence) = some node := by
    induction nodes with
    | nil => cases member
    | cons first rest ih =>
        simp only [List.map_cons, List.nodup_cons] at unique
        rcases List.mem_cons.mp member with rfl | member
        · simp only [List.find?, (occurrence_beq_iff_eq _ _).mpr rfl]
        · have different : first.task.occurrence ≠ node.task.occurrence := by
            intro same
            exact unique.1 (same ▸ List.mem_map_of_mem member)
          have noMatch : (first.task.occurrence == node.task.occurrence) = false :=
            Bool.eq_false_iff.mpr (fun equal => different ((occurrence_beq_iff_eq _ _).mp equal))
          simp only [List.find?, noMatch]
          exact ih unique.2 member
  exact find queue.taskNodes unique member

/-- Replacing a computation's metadata preserves its occurrence keys. -/
theorem State.TaskNodeKeysUnique.putTaskNode {queue : State}
    (unique : queue.TaskNodeKeysUnique) (updated : TaskNode)
    : (queue.putTaskNode updated).TaskNodeKeysUnique := by
  unfold State.TaskNodeKeysUnique State.putTaskNode
  rw [List.map_map]
  have same : queue.taskNodes.map
      (fun node =>
        (if node.task.occurrence == updated.task.occurrence then updated else node).task.occurrence)
      = queue.taskNodes.map (fun node => node.task.occurrence) := by
    apply List.map_congr_left
    intro node _
    split
    · rename_i equal
      exact ((occurrence_beq_iff_eq _ _).mp equal).symm
    · rfl
  simpa only [Function.comp_def, same]
    using (show (queue.taskNodes.map (fun node => node.task.occurrence)).Nodup from unique)

private theorem append_unstarted {queue : State}
    (unique : queue.TaskNodeKeysUnique) (task : Task)
    (absent : queue.taskNode? task.occurrence = none) (rejection : Option Nat := none)
    : ({ queue with taskNodes := queue.taskNodes ++ [{ task, rejection }] }
        : State).TaskNodeKeysUnique := by
  have fresh : task.occurrence ∉ queue.taskNodes.map (fun node => node.task.occurrence) := by
    intro member
    obtain ⟨node, member, equal⟩ := List.mem_map.mp member
    have rejected := List.find?_eq_none.mp absent node member
    exact rejected ((occurrence_beq_iff_eq _ _).mpr equal)
  change ((queue.taskNodes ++ [({ task, rejection } : TaskNode)]).map
    (fun node => node.task.occurrence)).Nodup
  rw [List.map_append, List.nodup_append]
  refine ⟨unique, by simp, ?_⟩
  intro first member second other same
  have equal : second = task.occurrence := by simpa using other
  exact fresh ((same.trans equal) ▸ member)

private theorem fold_preserves {α β : Type} (property : β → Prop)
    (step : β → α → β) (items : List α)
    (preserved : ∀ state item, property state → property (step state item))
    (state : β) (valid : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact valid
  | cons item rest ih => exact ih _ (preserved state item valid)

theorem State.TaskNodeKeysUnique.putGroupNode {queue : State}
    (unique : queue.TaskNodeKeysUnique) (updated : GroupNode)
    : (queue.putGroupNode updated).TaskNodeKeysUnique :=
  unique

theorem State.TaskNodeKeysUnique.addGroups {queue : State}
    (unique : queue.TaskNodeKeysUnique) (groups : List Group)
    : (queue.addGroups groups).1.TaskNodeKeysUnique := by
  simpa only [State.TaskNodeKeysUnique, State.addGroups_taskNodes] using unique

theorem State.TaskNodeKeysUnique.addTask {queue : State}
    (unique : queue.TaskNodeKeysUnique) (task : Task)
    : (queue.addTask task).TaskNodeKeysUnique := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stable (current : State) (group : Execution.DeliveryNode)
      (valid : current.TaskNodeKeysUnique) : (step current group).TaskNodeKeysUnique := by
    unfold step
    split
    · exact valid
    · split
      · exact valid
      · exact valid.putGroupNode _
  have folded := fold_preserves _ step task.groups stable registered unique
  dsimp only [State.addTask]
  split
  · rename_i starts
    exact append_unstarted folded task (Option.isNone_iff_eq_none.mp
      (Bool.and_eq_true_iff.mp starts).2)
  · exact folded

theorem State.TaskNodeKeysUnique.addStreams {queue : State}
    (unique : queue.TaskNodeKeysUnique) (streams : List Stream)
    (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.TaskNodeKeysUnique := by
  dsimp only [State.addStreams]
  split
  · exact unique
  · split
    · exact unique
    · exact unique.putTaskNode _

theorem State.TaskNodeKeysUnique.maybeIntegrateWork {queue : State}
    (unique : queue.TaskNodeKeysUnique) (more : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork more producer).1.TaskNodeKeysUnique :=
  (fold_preserves (fun current : State => current.TaskNodeKeysUnique)
    State.addTask more.tasks (fun _ task valid => valid.addTask task) _
    (unique.addGroups more.groups)).addStreams
    more.streams producer

theorem State.TaskNodeKeysUnique.pruneEmptyGroups {queue : State}
    (unique : queue.TaskNodeKeysUnique) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.TaskNodeKeysUnique := by
  simpa only [State.TaskNodeKeysUnique, State.pruneEmptyGroups_taskNodes] using unique

theorem State.TaskNodeKeysUnique.startTask {queue : State}
    (unique : queue.TaskNodeKeysUnique) (occurrence : Occurrence)
    (available : List (Occurrence × Nat) := [])
    : (queue.startTask occurrence available).TaskNodeKeysUnique := by
  unfold State.startTask
  split
  · exact unique
  · rename_i unstarted
    split
    · exact unique
    · rename_i task found
      have same : task.occurrence = occurrence :=
        (occurrence_beq_iff_eq _ _).mp (List.find?_some
          (p := fun candidate : Task => candidate.occurrence == occurrence) found)
      apply append_unstarted unique (rejection := available.findSome?
        (fun (other, errors) => if other == occurrence then some errors else none))
      rw [same]
      cases selected : queue.taskNode? occurrence with
      | none => rfl
      | some node => simp [selected] at unstarted

/-- Exposing computation rejections preserves the task-node identity keys. -/
theorem State.TaskNodeKeysUnique.cacheTaskFailures {queue : State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).TaskNodeKeysUnique := by
  unfold State.cacheTaskFailures
  induction available generalizing queue with
  | nil => exact unique
  | cons entry rest ih =>
      apply ih
      dsimp only [List.foldl_cons]
      split
      · exact unique
      · exact unique.putTaskNode _

/-- A group either starts fresh computations or filters existing nodes on failure. -/
theorem State.TaskNodeKeysUnique.startGroup {queue : State}
    (unique : queue.TaskNodeKeysUnique) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.TaskNodeKeysUnique := by
  have cached := unique.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · exact fold_preserves (fun current : State => current.TaskNodeKeysUnique)
        (fun current task => current.startTask task available) _
        (fun _ occurrence prior => prior.startTask occurrence available) _ cached
    · exact (List.filter_sublist.map
        (fun node : TaskNode => node.task.occurrence)).nodup cached

/-- Startup preserves unique computation identities, including immediate failure removal. -/
theorem State.TaskNodeKeysUnique.startNewWork {queue : State}
    (supported : State.TaskNodeKeysUnique queue) (more : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork more available).1.TaskNodeKeysUnique := by
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let (current, failures) := acc
    let (next, queued) := current.startGroup ref available
    (next, failures ++ queued)
  have groups := fold_preserves (fun acc => acc.1.TaskNodeKeysUnique) step
    (more.newGroups.map Execution.DeliveryNode.ref)
    (fun acc ref prior => prior.startGroup ref available)
    ({ queue with rootGroups := queue.rootGroups ++
      more.newGroups.map Execution.DeliveryNode.ref }, []) supported
  have streamStable (current : State) (ref : NodeRef) (valid : current.TaskNodeKeysUnique)
      : (current.startStream ref).TaskNodeKeysUnique := by
    unfold State.startStream
    split <;> exact valid
  exact fold_preserves _ State.startStream _ streamStable _ groups

theorem State.TaskNodeKeysUnique.removeTask {queue : State}
    (unique : queue.TaskNodeKeysUnique) (occurrence : Occurrence)
    : (queue.removeTask occurrence).TaskNodeKeysUnique := by
  unfold State.TaskNodeKeysUnique State.removeTask
  exact (List.filter_sublist.map (fun node : TaskNode => node.task.occurrence)).nodup unique

theorem State.TaskNodeKeysUnique.removeGroup {queue : State}
    (unique : queue.TaskNodeKeysUnique) (ref : NodeRef)
    : (queue.removeGroup ref).TaskNodeKeysUnique := by
  unfold State.TaskNodeKeysUnique State.removeGroup
  exact (List.filter_sublist.map (fun node : TaskNode => node.task.occurrence)).nodup unique

theorem State.TaskNodeKeysUnique.finishGroupSuccess {queue : State}
    (supported : State.TaskNodeKeysUnique queue) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.TaskNodeKeysUnique := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some node =>
        let values := match node.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ node.childStreams)
  have stable (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence)
      (valid : acc.1.TaskNodeKeysUnique)
      : (step acc occurrence).1.TaskNodeKeysUnique := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact valid
    · exact valid.removeTask occurrence
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have prior : flushed.TaskNodeKeysUnique :=
    fold_preserves _ step group.tasks stable (queue, [], []) supported
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have filtered : current.TaskNodeKeysUnique := by
    exact prior
  exact filtered.pruneEmptyGroups _

theorem State.TaskNodeKeysUnique.taskFailure {queue : State}
    (unique : queue.TaskNodeKeysUnique) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.TaskNodeKeysUnique := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using unique
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves (fun current => current.TaskNodeKeysUnique)
        (fun _ ref valid => valid.removeGroup ref) _ _ _ (unique.putTaskNode _)

theorem State.TaskNodeKeysUnique.drainReadyGroups {queue : State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.TaskNodeKeysUnique := by
  apply State.drainReadyGroups_preserves (fun current => current.TaskNodeKeysUnique)
    (available := available) (valid := unique)
  intro current node valid _ _ _
  exact (valid.finishGroupSuccess node).startNewWork _ available

theorem State.TaskNodeKeysUnique.successGroupFold {queue : State}
    (supported : queue.TaskNodeKeysUnique)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl successGroupStep (queue, [], {})).1.TaskNodeKeysUnique := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (prior : acc.1.TaskNodeKeysUnique)
      : (groups.foldl successGroupStep acc).1.TaskNodeKeysUnique := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        simp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ prior
        · rename_i node found
          have updated := prior.putGroupNode { node with pending := node.pending - 1 }
          split
          · exact ih _ (updated.finishGroupSuccess _)
          · exact ih _ updated
  exact loop groups (queue, [], {}) supported

theorem State.TaskNodeKeysUnique.taskSuccess {queue : State}
    (supported : State.TaskNodeKeysUnique queue) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.TaskNodeKeysUnique := by
  let step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode) :=
    let (current, outputs, released) := acc
    match current.groupNode? group.ref with
    | none => (current, outputs, released)
    | some old =>
        let node := { old with pending := old.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.ref && node.pending == 0 then
          let (next, finished, more) := current.finishGroupSuccess node
          (next, outputs ++ finished,
            ⟨released.newGroups ++ more.newGroups, released.newStreams ++ more.newStreams⟩)
        else (current, outputs, released)
  have stable (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (valid : acc.1.TaskNodeKeysUnique)
      : (step acc group).1.TaskNodeKeysUnique := by
    obtain ⟨current, outputs, released⟩ := acc
    dsimp only [step]
    split
    · exact valid
    · rename_i node found
      have updated := valid.putGroupNode { node with pending := node.pending - 1 }
      split
      · exact updated.finishGroupSuccess _
      · exact updated
  unfold State.taskSuccess
  split
  · exact supported
  · rename_i taskNode found
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have before : withValue.TaskNodeKeysUnique :=
      supported.putTaskNode _
    have integrated := before.maybeIntegrateWork result.work (some occurrence)
    have released := fold_preserves _ step taskNode.task.groups stable
      ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {}) integrated
    exact (released.startNewWork _ available).drainReadyGroups available

/-- Stream-item integration and its final drain preserve unique computation keys.
Witness: each item integrates fresh work, prunes, and activates without inventing rejections.
-/
theorem State.TaskNodeKeysUnique.streamItems {queue : State}
    (supported : State.TaskNodeKeysUnique queue)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.TaskNodeKeysUnique := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue × List GroupFailureEvent) (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    let (started, queued) := pruned.startNewWork { more with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ more.newStreams,
      values ++ [item.value], failures ++ queued)
  have stable (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue × List GroupFailureEvent) (item : StreamItem)
      (valid : acc.1.TaskNodeKeysUnique)
      : (step acc item).1.TaskNodeKeysUnique :=
    ((valid.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available
  dsimp only [State.streamItems]
  split
  · exact supported
  · exact (fold_preserves _ step items stable
      (queue, [], [], [], []) supported).drainReadyGroups available

/-- Every host outcome preserves the unique computation map under its cache snapshot. -/
theorem State.TaskNodeKeysUnique.handleGraphEvent {queue : State}
    (unique : queue.TaskNodeKeysUnique) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.TaskNodeKeysUnique := by
  have cached := unique.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result => exact cached.taskSuccess occurrence result available
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.TaskNodeKeysUnique
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | streamItems stream items => exact cached.streamItems stream items available
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact cached
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact cached

/-- A fixed-snapshot FIFO replay retains unique computation keys. -/
theorem State.TaskNodeKeysUnique.replayGraphEvents {queue : State}
    (unique : queue.TaskNodeKeysUnique) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.replayGraphEvents events available).TaskNodeKeysUnique := by
  induction events generalizing queue with
  | nil => exact unique
  | cons event rest ih => exact ih (unique.handleGraphEvent event available)

/-- Whole host batches preserve unique computation keys, including termination updates. -/
theorem State.TaskNodeKeysUnique.handleGraphEvents {queue : State}
    (unique : queue.TaskNodeKeysUnique) (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.TaskNodeKeysUnique := by
  cases running : queue.terminated with
  | true => simpa only [State.handleGraphEvents, running, ↓reduceIte] using unique
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      rw [same]
      exact unique.replayGraphEvents events (GraphEvent.availableFailures events)

/-- The normalized runner retains unique task nodes through its actual batch fold. -/
theorem State.TaskNodeKeysUnique.runNormalized {queue : State}
    (unique : queue.TaskNodeKeysUnique) (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1.TaskNodeKeysUnique := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue with
  | nil => exact unique
  | cons batch rest ih => exact ih (unique.handleGraphEvents batch)

theorem createWorkQueue_taskNodeKeysUnique (input : Work)
    : (State.initialize input).TaskNodeKeysUnique := by
  have empty : ({} : State).TaskNodeKeysUnique := by simp [State.TaskNodeKeysUnique]
  exact ((empty.maybeIntegrateWork input).pruneEmptyGroups _).startNewWork _

/-- Actual normalized queue replay retains one record per computation occurrence. -/
theorem createWorkQueue_runNormalized_taskNodeKeysUnique (input : Work)
    (batches : List (List GraphEvent))
    : ((State.initialize input).runNormalized batches).1.TaskNodeKeysUnique :=
  (createWorkQueue_taskNodeKeysUnique input).runNormalized batches

/-- Cache exposure updates each unique task's rejection by the supplied cache entries.
Witness: a present key identifies its exact task record; repeated entries overwrite only
that rejection slot in their supplied order, without changing values or child streams.
-/
theorem State.TaskNodeKeysUnique.cacheTaskFailures_nodes {queue : State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).taskNodes
      = queue.taskNodes.map
          (fun node =>
            {
              node with
                rejection :=
                  available.foldl
                    (fun prior entry =>
                      if entry.1 == node.task.occurrence then some entry.2 else prior)
                    node.rejection
            }) := by
  induction available generalizing queue with
  | nil => simp [State.cacheTaskFailures]
  | cons entry rest ih =>
      simp only [State.cacheTaskFailures, List.foldl_cons]
      cases found : queue.taskNode? entry.1 with
      | none =>
          change (queue.cacheTaskFailures rest).taskNodes = _
          rw [ih unique]
          apply List.map_congr_left
          intro node member
          have different : entry.1 ≠ node.task.occurrence := by
            intro same
            have skipped := List.find?_eq_none.mp found node member
            exact skipped ((occurrence_beq_iff_eq _ _).mpr same.symm)
          simp only [occurrence_beq_iff_eq, different, ↓reduceIte]
      | some node =>
          have identity := (State.taskNode?_some found).2
          have updated : (queue.putTaskNode { node with rejection := some entry.2 }).taskNodes
              = queue.taskNodes.map (fun old =>
                  { old with
                    rejection :=
                      if entry.1 == old.task.occurrence then some entry.2
                      else old.rejection }) := by
            unfold State.putTaskNode
            apply List.map_congr_left
            intro old member
            by_cases same : old.task.occurrence = entry.1
            · have lookup := unique.lookup member
              rw [same, found] at lookup
              obtain rfl := Option.some.inj lookup
              simp only [same, (occurrence_beq_iff_eq _ _).mpr rfl, ↓reduceIte]
            · have different : entry.1 ≠ old.task.occurrence := Ne.symm same
              simp only [identity, occurrence_beq_iff_eq, same, different, ↓reduceIte]
          change ((queue.putTaskNode { node with rejection := some entry.2 }).cacheTaskFailures
            rest).taskNodes = _
          rw [ih (unique.putTaskNode _), updated, List.map_map]
          apply List.map_congr_left
          intro old member
          rfl

private theorem cacheRejection_eq_of_mem (available : List (Occurrence × Nat))
    (occurrence : Occurrence) (member : occurrence ∈ available.map Prod.fst)
    (first second : Option Nat)
    : available.foldl
        (fun prior entry => if entry.1 == occurrence then some entry.2 else prior) first
      = available.foldl
          (fun prior entry => if entry.1 == occurrence then some entry.2 else prior)
          second := by
  induction available generalizing first second with
  | nil => cases member
  | cons entry rest ih =>
      rcases List.mem_cons.mp member with same | later
      · simp only [List.foldl_cons, same, (occurrence_beq_iff_eq _ _).mpr rfl, ↓reduceIte]
      · exact ih later _ _

private theorem cacheRejection_eq_self_of_not_mem (available : List (Occurrence × Nat))
    (occurrence : Occurrence) (absent : occurrence ∉ available.map Prod.fst)
    (prior : Option Nat)
    : available.foldl
        (fun prior entry => if entry.1 == occurrence then some entry.2 else prior) prior
      = prior := by
  induction available generalizing prior with
  | nil => rfl
  | cons entry rest ih =>
      have different : entry.1 ≠ occurrence := fun same => absent
        (List.mem_cons.mpr (.inl same.symm))
      have missing : occurrence ∉ rest.map Prod.fst := fun member =>
        absent (List.mem_cons_of_mem _ member)
      simpa only [List.foldl_cons, occurrence_beq_iff_eq, different, ↓reduceIte]
        using ih missing prior

private theorem cacheRejection_idempotent (available : List (Occurrence × Nat))
    (occurrence : Occurrence) (prior : Option Nat)
    : let update :=
        fun value =>
          available.foldl
            (fun prior entry => if entry.1 == occurrence then some entry.2 else prior)
            value
      update (update prior) = update prior := by
  classical
  by_cases member : occurrence ∈ available.map Prod.fst
  · exact cacheRejection_eq_of_mem available occurrence member _ _
  · simp only [cacheRejection_eq_self_of_not_mem available occurrence member]

/-- Exposing the same task-failure snapshot twice has the same effect as exposing it once.
Witness: unique keys reduce cache exposure to independent rejection-slot overwrites; each
nonempty key projection is constant and an absent projection leaves its input unchanged.
-/
theorem State.TaskNodeKeysUnique.cacheTaskFailures_idempotent {queue : State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).cacheTaskFailures available
      = queue.cacheTaskFailures available := by
  have nodes := unique.cacheTaskFailures_nodes available
  have double := (unique.cacheTaskFailures available).cacheTaskFailures_nodes available
  rw [nodes, List.map_map] at double
  have sameNodes : ((queue.cacheTaskFailures available).cacheTaskFailures available).taskNodes
      = (queue.cacheTaskFailures available).taskNodes := by
    rw [double, nodes]
    apply List.map_congr_left
    intro node member
    dsimp only [Function.comp_apply]
    congr 1
    exact cacheRejection_idempotent available node.task.occurrence node.rejection
  have frame := (queue.cacheTaskFailures available).cacheTaskFailures_frame available
  calc
    (queue.cacheTaskFailures available).cacheTaskFailures available
        = {
          {
                (queue.cacheTaskFailures available).cacheTaskFailures available with
                  taskNodes := []
              } with
            taskNodes :=
              ((queue.cacheTaskFailures available).cacheTaskFailures available).taskNodes
        } :=
      rfl
    _ = {
          { queue.cacheTaskFailures available with taskNodes := [] } with
            taskNodes := (queue.cacheTaskFailures available).taskNodes
        } := by
      rw [frame, sameNodes]
    _ = queue.cacheTaskFailures available := rfl

/-- Starting a missing task with available failures agrees after the same cache exposure.
Witness: startup can initialize a new rejection slot earlier, but cache exposure overwrites
that slot from the same supplied entries. Existing task records are identical on both sides.
-/
theorem State.TaskNodeKeysUnique.startTask_cacheTaskFailures {queue : State}
    (unique : queue.TaskNodeKeysUnique) (occurrence : Occurrence)
    (available : List (Occurrence × Nat))
    : (queue.startTask occurrence available).cacheTaskFailures available
      = (queue.startTask occurrence).cacheTaskFailures available := by
  have frame : { (queue.startTask occurrence available).cacheTaskFailures available
        with taskNodes := [] }
      = { (queue.startTask occurrence).cacheTaskFailures available with taskNodes := [] } := by
    rw [State.cacheTaskFailures_frame, State.cacheTaskFailures_frame]
    unfold State.startTask
    split
    · rfl
    · split <;> rfl
  have nodes : ((queue.startTask occurrence available).cacheTaskFailures available).taskNodes
      = ((queue.startTask occurrence).cacheTaskFailures available).taskNodes := by
    rw [(unique.startTask occurrence available).cacheTaskFailures_nodes available,
      (unique.startTask occurrence).cacheTaskFailures_nodes available]
    unfold State.startTask
    split
    · rfl
    · split
      · rfl
      · rename_i task known
        have identity : task.occurrence = occurrence :=
          (occurrence_beq_iff_eq _ _).mp
            (List.find?_some
              (p := fun candidate : Task => candidate.occurrence == occurrence) known)
        simp only [List.map_append, List.map_cons, List.map_nil]
        congr 2
        congr 1
        classical
        by_cases member : task.occurrence ∈ available.map Prod.fst
        · exact cacheRejection_eq_of_mem available task.occurrence member _ _
        · have missing : available.findSome?
              (fun entry => if entry.1 == occurrence then some entry.2 else none) = none := by
            apply List.findSome?_eq_none_iff.mpr
            intro entry included
            have different : entry.1 ≠ occurrence := by
              intro same
              exact member (List.mem_map.mpr ⟨entry, included, same.trans identity.symm⟩)
            simp only [occurrence_beq_iff_eq, different, ↓reduceIte]
          rw [missing]
          rfl
  calc
    (queue.startTask occurrence available).cacheTaskFailures available
        = {
          {
                (queue.startTask occurrence available).cacheTaskFailures available with
                  taskNodes := []
              } with
            taskNodes :=
              ((queue.startTask occurrence available).cacheTaskFailures
                available).taskNodes
        } :=
      rfl
    _ = {
          {
                (queue.startTask occurrence).cacheTaskFailures available with
                  taskNodes := []
              } with
            taskNodes :=
              ((queue.startTask occurrence).cacheTaskFailures available).taskNodes
        } := by
      rw [frame, nodes]
    _ = (queue.startTask occurrence).cacheTaskFailures available := rfl

/-- The entire exposed state is its original metadata with independently updated rejections.
Witness: combine the unique-key task-node projection with the unchanged metadata frame.
-/
theorem State.TaskNodeKeysUnique.cacheTaskFailures_eq {queue : State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    : queue.cacheTaskFailures available
      = {
        queue with
          taskNodes :=
            queue.taskNodes.map
              (fun node =>
                {
                  node with
                    rejection :=
                      available.foldl
                        (fun prior entry =>
                          if entry.1 == node.task.occurrence then some entry.2 else prior)
                        node.rejection
                })
      } := by
  calc
    queue.cacheTaskFailures available
        = {
          { queue.cacheTaskFailures available with taskNodes := [] } with
            taskNodes := (queue.cacheTaskFailures available).taskNodes
        } :=
      rfl
    _ = _ := by
      rw [State.cacheTaskFailures_frame, unique.cacheTaskFailures_nodes available]

/-- Starting one task preserves equality after a common cache exposure.
Witness: cache exposure changes neither task eligibility nor the permanent catalogue;
existing slots receive idempotent updates, and new slots are identical on both sides.
-/
theorem State.TaskNodeKeysUnique.cacheTaskFailures_startTask {queue : State}
    (unique : queue.TaskNodeKeysUnique) (occurrence : Occurrence)
    (available : List (Occurrence × Nat))
    : (queue.startTask occurrence available).cacheTaskFailures available
      = ((queue.cacheTaskFailures available).startTask occurrence
          available).cacheTaskFailures
          available := by
  have eligible : ((queue.cacheTaskFailures available).taskNode? occurrence).isSome
      = (queue.taskNode? occurrence).isSome :=
    queue.cacheTaskFailures_acceptsGraphEvent available (.taskFailure occurrence 0)
  have catalogue
      : (queue.cacheTaskFailures available).task? occurrence = queue.task? occurrence := by
    simp only [State.task?, State.cacheTaskFailures_tasks]
  by_cases started : (queue.taskNode? occurrence).isSome = true
  · simp only [State.startTask, eligible, started, ↓reduceIte]
    exact (unique.cacheTaskFailures_idempotent available).symm
  · cases known : queue.task? occurrence with
    | none =>
        simp only [State.startTask, eligible, started, Bool.false_eq_true, ↓reduceIte,
          catalogue, known]
        exact (unique.cacheTaskFailures_idempotent available).symm
    | some task =>
        have left := (unique.startTask occurrence available).cacheTaskFailures_eq available
        have right := ((unique.cacheTaskFailures available).startTask occurrence available
          ).cacheTaskFailures_eq available
        rw [left, right]
        simp only [State.startTask, eligible, started, Bool.false_eq_true, ↓reduceIte,
          catalogue, known]
        rw [unique.cacheTaskFailures_eq available]
        simp only [List.map_append, List.map_cons, List.map_nil, List.map_map]
        congr 1
        congr 1
        apply List.map_congr_left
        intro node member
        dsimp only [Function.comp_apply]
        congr 1
        exact (cacheRejection_idempotent available node.task.occurrence node.rejection).symm

/-- Equal exposed queues stay equal after one task start and the same exposure.
Witness: move each initial exposure before startup, then use equality of those states.
This is a relation between concrete queues, not a premise about their eventual outputs.
-/
theorem State.TaskNodeKeysUnique.startTask_cache_congr {left right : State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (occurrence : Occurrence)
    : (left.startTask occurrence available).cacheTaskFailures available
      = (right.startTask occurrence available).cacheTaskFailures available := by
  rw [leftUnique.cacheTaskFailures_startTask occurrence available,
    rightUnique.cacheTaskFailures_startTask occurrence available, same]

/-- A sequence of cache-aware starts agrees with eager empty-cache starts after exposure.
Witness: independent task-slot updates preserve the exposed-state relation at every step,
including repeated task requests and repeated entries in the supplied failure snapshot.
-/
theorem State.TaskNodeKeysUnique.startTasks_cache_congr {left right : State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (tasks : List Occurrence)
    : (tasks.foldl (fun current task => current.startTask task available)
        left).cacheTaskFailures
        available
      = (tasks.foldl (fun current task => current.startTask task) right).cacheTaskFailures
          available := by
  induction tasks generalizing left right with
  | nil => exact same
  | cons task rest ih =>
      have next := (leftUnique.startTask_cache_congr rightUnique available same task).trans
        (rightUnique.startTask_cacheTaskFailures task available)
      exact ih (leftUnique.startTask task available) (rightUnique.startTask task) next

/-- Cache exposure preserves each first-match task lookup apart from its rejection slot.
Witness: the unique-key node projection keeps occurrence keys, values and held streams.
-/
theorem State.TaskNodeKeysUnique.cacheTaskFailures_lookup {queue : State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    (occurrence : Occurrence)
    : (queue.cacheTaskFailures available).taskNode? occurrence
      = (queue.taskNode? occurrence).map
          (fun node =>
            {
              node with
                rejection :=
                  available.foldl
                    (fun prior entry =>
                      if entry.1 == node.task.occurrence then some entry.2 else prior)
                    node.rejection
            }) := by
  unfold State.taskNode?
  rw [unique.cacheTaskFailures_nodes available, List.find?_map]
  rfl

/-- Task removal commutes with exposing cached failures.
Witness: removal filters occurrence keys and shortens group memberships; cache exposure
updates rejection slots without changing those keys or any group record.
-/
theorem State.TaskNodeKeysUnique.cacheTaskFailures_removeTask {queue : State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    (occurrence : Occurrence)
    : (queue.removeTask occurrence).cacheTaskFailures available
      = (queue.cacheTaskFailures available).removeTask occurrence := by
  rw [(unique.removeTask occurrence).cacheTaskFailures_eq available,
    unique.cacheTaskFailures_eq available]
  unfold State.removeTask
  simp only [List.filter_map, Function.comp_def]

/-- Appending a fresh computation record preserves unique task-node keys.
Witness: the absent first-match lookup excludes its occurrence from every old key.
-/
theorem State.TaskNodeKeysUnique.appendTaskNode {queue : State}
    (unique : queue.TaskNodeKeysUnique) (node : TaskNode)
    (absent : queue.taskNode? node.task.occurrence = none)
    : ({ queue with taskNodes := queue.taskNodes ++ [node] }
        : State).TaskNodeKeysUnique := by
  have appended := append_unstarted unique node.task absent node.rejection
  simpa only [State.TaskNodeKeysUnique, List.map_append, List.map_cons, List.map_nil]
    using appended

/-- Cache exposure of a fresh appended task applies the same independent slot update.
Witness: freshness preserves unique keys, so the full cache projection distributes over
the original store followed by the new record, including its value and held streams.
-/
theorem State.TaskNodeKeysUnique.cacheTaskFailures_appendTaskNode {queue : State}
    (unique : queue.TaskNodeKeysUnique) (node : TaskNode)
    (absent : queue.taskNode? node.task.occurrence = none)
    (available : List (Occurrence × Nat))
    : ({ queue with taskNodes := queue.taskNodes ++ [node] } : State).cacheTaskFailures
        available
      = {
        queue.cacheTaskFailures available with
          taskNodes :=
            (queue.cacheTaskFailures available).taskNodes
            ++ [{
                  node with
                    rejection :=
                      available.foldl
                        (fun prior entry =>
                          if entry.1 == node.task.occurrence then some entry.2 else prior)
                        node.rejection
                }]
      } := by
  rw [(unique.appendTaskNode node absent).cacheTaskFailures_eq available,
    unique.cacheTaskFailures_eq available]
  simp only [List.map_append, List.map_cons, List.map_nil]

/-- Appending the same fresh record preserves equality after common exposure.
Witness: both queues append an identical exposed slot to their already equal stores.
-/
theorem State.TaskNodeKeysUnique.appendTaskNode_cache_congr {left right : State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (node : TaskNode) (leftAbsent : left.taskNode? node.task.occurrence = none)
    (rightAbsent : right.taskNode? node.task.occurrence = none)
    : ({ left with taskNodes := left.taskNodes ++ [node] } : State).cacheTaskFailures
        available
      = ({ right with taskNodes := right.taskNodes ++ [node] } : State).cacheTaskFailures
          available := by
  rw [leftUnique.cacheTaskFailures_appendTaskNode node leftAbsent available,
    rightUnique.cacheTaskFailures_appendTaskNode node rightAbsent available, same]

/-- Replacing a task and exposing failures equals replacing its exposed record.
Witness: the cache projection preserves occurrence keys, so key-based replacement selects
the same positions before or after each independent rejection-slot update.
-/
theorem State.TaskNodeKeysUnique.cacheTaskFailures_putTaskNode {queue : State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    (updated : TaskNode)
    : (queue.putTaskNode updated).cacheTaskFailures available
      = (queue.cacheTaskFailures available).putTaskNode
          {
            updated with
              rejection :=
                available.foldl
                  (fun prior entry =>
                    if entry.1 == updated.task.occurrence then some entry.2 else prior)
                  updated.rejection
          } := by
  rw [(unique.putTaskNode updated).cacheTaskFailures_eq available,
    unique.cacheTaskFailures_eq available]
  unfold State.putTaskNode
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro node member
  dsimp only [Function.comp_apply]
  by_cases same : node.task.occurrence = updated.task.occurrence
  · simp only [occurrence_beq_iff_eq, same, ↓reduceIte]
  · simp only [occurrence_beq_iff_eq, same, ↓reduceIte]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
