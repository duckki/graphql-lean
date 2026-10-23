import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskSupport

/-! Permanent registration preserves source-derived ref predicates, including empty declarations. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration predicates do not require task-bearing declarations
-----------------------------------------------------------------------------------------

/-- Every candidate ref satisfies a proof-side registration predicate. -/
def Work.GroupsSatisfy (work : Work) (property : Nat → Prop) : Prop :=
  ∀ group ∈ work.groups, property group.node.ref

/-- Conditional task-bearing shape; explicit empty declarations need not satisfy it. -/
def Work.GroupsHaveTasks (work : Work) : Prop :=
  ∀ group ∈ work.groups,
    ∃ task ∈ work.tasks, group.node.ref ∈ task.groups.map Execution.DeliveryNode.ref

/-- Every permanent registration ref satisfies a proof-side predicate.
Declarations can establish this certificate without supplying a task witness. -/
def State.RegistrationsSatisfy (queue : State) (property : Nat → Prop) : Prop :=
  ∀ ref ∈ queue.registeredGroups, property ref

/-- Implication on ref properties preserves registration evidence. -/
theorem State.RegistrationsSatisfy.mono {queue : State} {before after : Nat → Prop}
    (known : queue.RegistrationsSatisfy before) (implies : ∀ ref, before ref → after ref)
    : queue.RegistrationsSatisfy after :=
  fun ref member => implies ref (known ref member)

/-- A preserved state predicate extends through a finite fold.
Witness: induction over inputs, threading the actual accumulator. -/
private theorem fold_preserves {α β : Type} (step : β → α → β) (property : β → Prop)
    (preserved : ∀ state item, property state → property (step state item))
    (items : List α) (state : β) (initial : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact initial
  | cons item rest ih => exact ih (step state item) (preserved state item initial)

/-- Group integration adds no ref outside the old registry and supplied candidates.
Witness: registration only appends a candidate; linking changes neither registry nor tasks.
-/
theorem State.addGroups_registeredGroups_subset (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.registeredGroups.Subset
        (queue.registeredGroups ++ groups.map (fun group => group.node.ref)) := by
  let allowed := queue.registeredGroups ++ groups.map (fun group => group.node.ref)
  apply State.addGroups_preserves (fun current => current.registeredGroups ⊆ allowed) groups
  · intro current group member prior ref registered
    rcases List.mem_append.mp (current.addGroup_registeredGroups_subset group registered) with
      old | new
    · exact prior old
    · cases List.mem_singleton.mp new
      exact List.mem_append_right _ (List.mem_map.mpr ⟨group, member, rfl⟩)
  · exact List.subset_append_left _ _

/-- Registering a task leaves group registration history unchanged.
Witness: every membership update replaces an existing group node. -/
theorem State.addTask_registeredGroups (queue : State) (task : Task)
    : (queue.addTask task).registeredGroups = queue.registeredGroups := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved (current : State) (group : Execution.DeliveryNode)
      (prior : current.registeredGroups = queue.registeredGroups)
      : (step current group).registeredGroups = queue.registeredGroups := by
    unfold step
    split
    · exact prior
    · split <;> exact prior
  let current := task.groups.foldl step registered
  have unchanged : current.registeredGroups = queue.registeredGroups :=
    fold_preserves step (fun state => state.registeredGroups = queue.registeredGroups)
      preserved task.groups registered rfl
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).registeredGroups = queue.registeredGroups
  split <;> exact unchanged

/-- Integrating immediate Work appends precisely its task descriptors. -/
theorem State.maybeIntegrateWork_tasks_append
    (queue : State) (newWork : Work) (parentTask : Option Occurrence)
    : (queue.maybeIntegrateWork newWork parentTask).1.tasks
      = queue.tasks ++ newWork.tasks := by
  have taskFold (more : List Task) :
      ∀ current : State,
        (more.foldl State.addTask current).tasks = current.tasks ++ more := by
    induction more with
    | nil => intro current; simp
    | cons task rest ih =>
        intro current
        rw [List.foldl_cons, ih, State.addTask_tasks]
        simp [List.append_assoc]
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  change (withTasks.addStreams newWork.streams parentTask).1.tasks
      = queue.tasks ++ newWork.tasks
  rw [State.addStreams_tasks, taskFold, State.addGroups_tasks]

/-- Integration registers only old refs or supplied candidate refs.
Witness: group-ref inclusion; task and stream registration retain group history. -/
theorem State.RegistrationsSatisfy.maybeIntegrateWork {queue : State}
    {support : Nat → Prop} (covered : queue.RegistrationsSatisfy support)
    (work : Work) (workCovered : work.GroupsSatisfy support)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.RegistrationsSatisfy support := by
  let grouped := (queue.addGroups work.groups).1
  let tasked := work.tasks.foldl State.addTask grouped
  have taskedSame : tasked.registeredGroups = grouped.registeredGroups :=
    fold_preserves State.addTask
      (fun state => state.registeredGroups = grouped.registeredGroups)
      (fun state task prior => (state.addTask_registeredGroups task).trans prior)
      work.tasks grouped rfl
  have same : (queue.maybeIntegrateWork work parentTask).1.registeredGroups
      = grouped.registeredGroups := by
    change (tasked.addStreams work.streams parentTask).1.registeredGroups = _
    unfold State.addStreams
    split
    · exact taskedSame
    · dsimp
      split <;> exact taskedSame
  intro ref member
  rw [same] at member
  have included := queue.addGroups_registeredGroups_subset work.groups member
  rcases List.mem_append.mp included with old | new
  · exact covered ref old
  · obtain ⟨group, groupMember, sameRef⟩ := List.mem_map.mp new
    exact sameRef ▸ workCovered group groupMember

-----------------------------------------------------------------------------------------
-- Cleanup and activation preserve permanent ref evidence
-----------------------------------------------------------------------------------------

/-- Pruning deletes live nodes, retaining permanent registration evidence.
Witness: induction over the actual pruning traversal. -/
theorem State.RegistrationsSatisfy.pruneEmptyGroups {queue : State}
    {support : Nat → Prop} (covered : queue.RegistrationsSatisfy support)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.RegistrationsSatisfy support := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (prior : current.RegistrationsSatisfy support)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.RegistrationsSatisfy
          support := by
    induction fuel generalizing current remaining kept with
    | zero => exact prior
    | succ fuel ih =>
        cases remaining with
        | nil => exact prior
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ prior
            · split <;> exact ih _ _ _ prior
  exact loop _ queue groups [] covered

/-- Cache exposure preserves both permanent catalogues. -/
theorem State.RegistrationsSatisfy.cacheTaskFailures {queue : State}
    {support : Nat → Prop} (covered : queue.RegistrationsSatisfy support)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).RegistrationsSatisfy support := by
  intro ref member
  rw [State.cacheTaskFailures_registeredGroups] at member
  exact covered ref member

/-- Activation may remove live nodes while preserving both permanent catalogues. -/
theorem State.RegistrationsSatisfy.startNewWork {queue : State}
    {support : Nat → Prop} (covered : queue.RegistrationsSatisfy support)
    (work : NewWork) (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork work available).1.RegistrationsSatisfy support := by
  intro ref member
  rw [State.startNewWork_registeredGroups] at member
  exact covered ref member

/-- Successful publication preserves registration witnesses, including removed tasks.
Witness: the flush removes live task nodes/memberships but retains task definitions. -/
theorem State.RegistrationsSatisfy.finishGroupSuccess {queue : State}
    {support : Nat → Prop} (covered : queue.RegistrationsSatisfy support)
    (group : GroupNode)
    : (queue.finishGroupSuccess group).1.RegistrationsSatisfy support := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (task : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? task with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask task, values, streams ++ taskNode.childStreams)
  have preserved (acc : State × List ExecutionGroupValue × NodeRefs) (task : Occurrence)
      (prior : acc.1.RegistrationsSatisfy support)
      : (step acc task).1.RegistrationsSatisfy support := by
    obtain ⟨current, values, streams⟩ := acc
    unfold step
    dsimp only
    split <;> exact prior
  have flushed := fold_preserves step (fun acc => acc.1.RegistrationsSatisfy support)
    preserved group.tasks (queue, [], []) covered
  let flushedState := (group.tasks.foldl step (queue, [], [])).1
  let current : State :=
    { flushedState with
      groupNodes := flushedState.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushedState.rootGroups.filter (· != group.group.node.ref) }
  have currentCovered : current.RegistrationsSatisfy support := flushed
  exact currentCovered.pruneEmptyGroups _

/-- Retaining task rejections leaves permanent registration witnesses unchanged. -/
theorem State.RegistrationsSatisfy.taskFailure {queue : State}
    {support : Nat → Prop} (covered : queue.RegistrationsSatisfy support)
    (task : Occurrence) (errors : Nat)
    : (queue.taskFailure task errors).1.RegistrationsSatisfy support := by
  cases found : queue.taskNode? task with
  | none => simpa [State.taskFailure, found] using covered
  | some node =>
      rw [queue.taskFailure_eq task errors node found]
      exact failureGroupFold_preserves (fun state => state.RegistrationsSatisfy support)
        (fun _ _ prior => prior) _ _ _ covered

/-- Recursive draining retains the evidence for every permanent registration.
Witness: both closure paths retain the registries, and activation also preserves them.
-/
theorem State.RegistrationsSatisfy.drainReadyGroups {queue : State}
    {support : Nat → Prop} (covered : queue.RegistrationsSatisfy support)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.RegistrationsSatisfy support :=
  State.drainReadyGroups_preserves (fun state => state.RegistrationsSatisfy support)
    (fun _ node prior _ _ _ => (prior.finishGroupSuccess node).startNewWork _ available)
    covered

/-- One successful task preserves permanent registration provenance.
Witness: covered child integration followed by the single-pass contributor fold. -/
theorem State.RegistrationsSatisfy.taskSuccess {queue : State}
    {support : Nat → Prop} (covered : queue.RegistrationsSatisfy support)
    (task : Occurrence) (result : TaskResult)
    (children : result.work.GroupsSatisfy support)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess task result available).1.RegistrationsSatisfy support := by
  cases found : queue.taskNode? task with
  | none => simpa [State.taskSuccess, found] using covered
  | some node =>
      rw [queue.taskSuccess_eq task result node found available]
      have stored : (queue.putTaskNode { node with value := some result.value
          }).RegistrationsSatisfy support := covered
      have integrated := stored.maybeIntegrateWork result.work children (some task)
      have preserved (acc : State × List WorkQueueEvent × NewWork)
          (group : Execution.DeliveryNode) (prior : acc.1.RegistrationsSatisfy support)
          : (successGroupStep acc group).1.RegistrationsSatisfy support := by
        obtain ⟨current, events, released⟩ := acc
        unfold successGroupStep
        dsimp only
        split
        · exact prior
        · rename_i groupNode found
          have updated : (current.putGroupNode
              { groupNode with pending := groupNode.pending - 1 }).RegistrationsSatisfy
                support := prior
          split
          · exact updated.finishGroupSuccess _
          · exact prior
      exact ((fold_preserves successGroupStep
                (fun acc => acc.1.RegistrationsSatisfy support) preserved
                node.task.groups (_, [], {}) integrated).startNewWork
              _ available).drainReadyGroups available

/-- Stream-item child work preserves provenance at each successive integration state.
Witness: induction through integration, pruning, and activation for the actual item fold. -/
theorem State.RegistrationsSatisfy.streamItems {queue : State}
    {support : Nat → Prop} (covered : queue.RegistrationsSatisfy support)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (children : ∀ item ∈ items, item.work.GroupsSatisfy support)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.RegistrationsSatisfy support := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) := pruned.startNewWork { newWork with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (prior : acc.1.RegistrationsSatisfy support)
      : (more.foldl step acc).1.RegistrationsSatisfy support := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
        exact ((prior.maybeIntegrateWork item.work
          (children item (included List.mem_cons_self))).pruneEmptyGroups _).startNewWork
            _ available
  unfold State.streamItems
  split
  · exact covered
  · exact (loop items (fun _ member => member) (queue, [], [], [], [])
      covered).drainReadyGroups available

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
