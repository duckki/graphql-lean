import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRejections
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
      (fun node => (if node.task.occurrence == updated.task.occurrence then updated else node).task.occurrence)
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
    (absent : queue.taskNode? task.occurrence = none)
    : ({ queue with taskNodes := queue.taskNodes ++ [{ task }] }
        : State).TaskNodeKeysUnique := by
  have fresh : task.occurrence ∉ queue.taskNodes.map (fun node => node.task.occurrence) := by
    intro member
    obtain ⟨node, member, equal⟩ := List.mem_map.mp member
    have rejected := List.find?_eq_none.mp absent node member
    exact rejected ((occurrence_beq_iff_eq _ _).mpr equal)
  change ((queue.taskNodes ++ [({ task } : TaskNode)]).map (fun node => node.task.occurrence)).Nodup
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
    : (queue.startTask occurrence).TaskNodeKeysUnique := by
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
      apply append_unstarted unique
      rw [same]
      cases selected : queue.taskNode? occurrence with
      | none => rfl
      | some node => simp [selected] at unstarted

theorem State.TaskNodeKeysUnique.startNewWork {queue : State}
    (supported : State.TaskNodeKeysUnique queue) (more : NewWork)
    : (queue.startNewWork more).TaskNodeKeysUnique := by
  have groupStable (current : State) (ref : NodeRef)
      (valid : current.TaskNodeKeysUnique)
      : (current.startGroup ref).TaskNodeKeysUnique := by
    unfold State.startGroup
    split
    · exact valid
    · rename_i node found
      exact fold_preserves (fun current : State => current.TaskNodeKeysUnique) State.startTask node.tasks (fun _ occurrence prior => prior.startTask occurrence) current valid
  have streamStable (current : State) (ref : NodeRef)
      (valid : current.TaskNodeKeysUnique)
      : (current.startStream ref).TaskNodeKeysUnique := by
    unfold State.startStream
    split <;> exact valid
  exact fold_preserves _ State.startStream _ streamStable _
    (fold_preserves _ State.startGroup _ groupStable _ supported)

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
    (unique : queue.TaskNodeKeysUnique)
    : queue.drainReadyGroups.1.TaskNodeKeysUnique := by
  apply State.drainReadyGroups_preserves (fun current => current.TaskNodeKeysUnique)
    (valid := unique)
  · intro current node valid _ _ _ _
    exact (valid.finishGroupSuccess node).startNewWork _
  · intro current node occurrence errors valid _ _ _
    exact valid.taskFailure occurrence errors

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
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.TaskNodeKeysUnique := by
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
    exact (released.startNewWork _).drainReadyGroups

/-- Stream-item integration and its final drain preserve rejectiond-failure support.
Witness: each item integrates fresh work, prunes, and activates without inventing rejections.
-/
theorem State.TaskNodeKeysUnique.streamItems {queue : State}
    (supported : State.TaskNodeKeysUnique queue)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : (queue.streamItems stream items).1.TaskNodeKeysUnique := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    (pruned.startNewWork { more with newGroups := nonempty }, groups ++ nonempty,
      streams ++ more.newStreams, values ++ [item.value])
  have stable (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem)
      (valid : acc.1.TaskNodeKeysUnique)
      : (step acc item).1.TaskNodeKeysUnique :=
    ((valid.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
  dsimp only [State.streamItems]
  split
  · exact supported
  · exact (fold_preserves _ step items stable (queue, [], [], []) supported).drainReadyGroups

theorem State.TaskNodeKeysUnique.replayGraphEvents {queue : State}
    (unique : queue.TaskNodeKeysUnique) (events : List GraphEvent)
    : (queue.replayGraphEvents events).TaskNodeKeysUnique := by
  apply fold_preserves (fun current : State => current.TaskNodeKeysUnique)
    (fun current event => (current.handleGraphEvent event).1) events _ queue unique
  intro current event prior
  cases event with
  | taskSuccess occurrence result => exact prior.taskSuccess occurrence result
  | taskFailure occurrence errors => exact prior.taskFailure occurrence errors
  | streamItems stream items => exact prior.streamItems stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact prior
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact prior

theorem createWorkQueue_taskNodeKeysUnique (input : Work)
    : (State.initialize input).TaskNodeKeysUnique := by
  have empty : ({} : State).TaskNodeKeysUnique := by simp [State.TaskNodeKeysUnique]
  exact ((empty.maybeIntegrateWork input).pruneEmptyGroups _).startNewWork _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
