import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedLookupPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNodeKeys

/-! Whole-scope registration correspondence, retaining stored values and held streams. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

-----------------------------------------------------------------------------------------
-- A proof-facing eager completion of the temporary active projection
-----------------------------------------------------------------------------------------

/-- Insert the exact registered descriptor if its computation node is absent.
This spells the reference's eager insertion, not a new public activation algorithm.
Catalogue provenance will connect it to the public delayed startTask operation.
-/
def activateRegisteredTask (queue : ReferenceWorkQueue.State)
    (task : ReferenceWorkQueue.Task)
    : ReferenceWorkQueue.State :=
  if (queue.taskNode? task.occurrence).isSome then
    queue
  else
    { queue with taskNodes := queue.taskNodes ++ [{ task }] }

/-- Complete a registration's temporary active projection in registration order. -/
def activateRegisteredTasks (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task)
    : ReferenceWorkQueue.State :=
  tasks.foldl activateRegisteredTask queue

/-- Proof-facing spelling of the public scope's task-registration step. -/
def registerTaskStep
    (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
    (task : ReferenceWorkQueue.Task)
    : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task :=
  let next := acc.1.addTask task
  match next.2 with
  | .active => (next.1, acc.2.1 ++ [task], acc.2.2)
  | .registered => (next.1, acc.2.1, acc.2.2)
  | .rejected => (next.1, acc.2.1, acc.2.2 ++ [task])

private theorem classifyOwner_with_taskNodes (task : ReferenceWorkQueue.Task)
    (acc : ReferenceWorkQueue.State × Bool × Bool) (group : Execution.DeliveryNode)
    (nodes : List ReferenceWorkQueue.TaskNode)
    : classifyOwner task ({ acc.1 with taskNodes := nodes }, acc.2) group
      = (
        { (classifyOwner task acc group).1 with taskNodes := nodes },
        (classifyOwner task acc group).2
      ) := by
  unfold classifyOwner
  change (match acc.1.groupNode? group.ref with
      | none => _
      | some node => _) = _
  cases found : acc.1.groupNode? group.ref with
  | none => rfl
  | some node =>
      simp only
      by_cases linked : node.tasks.contains task.occurrence = true
      · simp only [linked, ↓reduceIte]
      · simp only [linked, Bool.false_eq_true, ↓reduceIte]
        rfl

private theorem classifyOwners_with_taskNodes (task : ReferenceWorkQueue.Task)
    (owners : List Execution.DeliveryNode) (acc : ReferenceWorkQueue.State × Bool × Bool)
    (nodes : List ReferenceWorkQueue.TaskNode)
    : owners.foldl (classifyOwner task) ({ acc.1 with taskNodes := nodes }, acc.2)
      = (
        { (owners.foldl (classifyOwner task) acc).1 with taskNodes := nodes },
        (owners.foldl (classifyOwner task) acc).2
      ) := by
  induction owners generalizing acc with
  | nil => rfl
  | cons group rest ih =>
      rw [List.foldl_cons, List.foldl_cons, classifyOwner_with_taskNodes, ih]

/-- Registration decisions ignore computation-node storage, while preserving it exactly.
Witness: the owner traversal reads group records and root membership, never task nodes.
-/
theorem State.addTask_with_taskNodes (state : State) (task : ReferenceWorkQueue.Task)
    (nodes : List ReferenceWorkQueue.TaskNode)
    : ({ state with queue := { state.queue with taskNodes := nodes } }).addTask task
      = (
        {
          (state.addTask task).1 with
            queue := { (state.addTask task).1.queue with taskNodes := nodes }
        },
        (state.addTask task).2
      ) := by
  let initial : ReferenceWorkQueue.State × Bool × Bool :=
    ({ state.queue with tasks := state.queue.tasks ++ [task] }, false, false)
  let finish (acc : ReferenceWorkQueue.State × Bool × Bool) : State × TaskRegistration :=
    ({ state with queue := acc.1 },
      if acc.2.2 then .active else if acc.2.1 then .registered else .rejected)
  change finish (task.groups.foldl (classifyOwner task)
      ({ initial.1 with taskNodes := nodes }, initial.2)) = _
  rw [classifyOwners_with_taskNodes]
  rfl

private theorem addTask_activateRegisteredTask (state : State)
    (incoming active : ReferenceWorkQueue.Task)
    : ({ state with queue := activateRegisteredTask state.queue active }).addTask incoming
      = (
        {
          (state.addTask incoming).1 with
            queue := activateRegisteredTask (state.addTask incoming).1.queue active
        },
        (state.addTask incoming).2
      ) := by
  unfold activateRegisteredTask
  have lookup : (state.addTask incoming).1.queue.taskNode? active.occurrence
      = state.queue.taskNode? active.occurrence := by
    change ((state.addTask incoming).1.queue.taskNodes.find? _) = _
    rw [State.addTask_taskNodes]
    rfl
  rw [lookup]
  split
  · rfl
  · rw [State.addTask_with_taskNodes, State.addTask_taskNodes]

private theorem addTask_activateRegisteredTasks (state : State)
    (incoming : ReferenceWorkQueue.Task) (active : List ReferenceWorkQueue.Task)
    : ({ state with queue := activateRegisteredTasks state.queue active }).addTask
        incoming
      = (
        {
          (state.addTask incoming).1 with
            queue := activateRegisteredTasks (state.addTask incoming).1.queue active
        },
        (state.addTask incoming).2
      ) := by
  induction active generalizing state with
  | nil => rfl
  | cons task rest ih =>
      have tail := ih ({ state with queue := activateRegisteredTask state.queue task })
      rw [addTask_activateRegisteredTask] at tail
      exact tail

private theorem addTask_rootsPresent {state : State}
    (present : state.queue.RootGroupsPresent) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.RootGroupsPresent := by
  intro key member
  rw [State.addTask_rootGroups] at member
  have core := congrArg (fun queue : ReferenceWorkQueue.State =>
    queue.groupNodes.map (fun node => node.group.node.ref))
    (state.addTask_registrationCore task)
  change (state.addTask task).1.queue.groupNodes.map (fun node => node.group.node.ref)
    = (state.queue.addTask task).groupNodes.map (fun node => node.group.node.ref) at core
  rw [core]
  exact ReferenceWorkQueue.State.addTask_includesRefs state.queue task key (present key member)

private theorem activateRegisteredTasks_core (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task)
    : registrationCore (activateRegisteredTasks queue tasks)
      = registrationCore queue := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      rw [activateRegisteredTasks, List.foldl_cons]
      change registrationCore (activateRegisteredTasks (activateRegisteredTask queue task) rest)
        = registrationCore queue
      rw [ih]
      unfold activateRegisteredTask
      split <;> rfl

private theorem addTask_complete_descriptor {state : State}
    (present : state.queue.RootGroupsPresent) (task : ReferenceWorkQueue.Task)
    : state.queue.addTask task
      = if (state.addTask task).2 = .active then
          activateRegisteredTask (state.addTask task).1.queue task
        else
          (state.addTask task).1.queue := by
  have reference : state.queue.addTask task =
      if task.groups.any (fun group => state.queue.rootGroups.contains group.ref)
        && ((state.addTask task).1.queue.taskNode? task.occurrence).isNone then
        { (state.addTask task).1.queue with
          taskNodes := (state.addTask task).1.queue.taskNodes ++ [{ task }] }
      else (state.addTask task).1.queue := by
    rw [State.addTask_ownerState, ← registerOwners_rootGroups task task.groups
      { state.queue with tasks := state.queue.tasks ++ [task] }]
    rfl
  rw [reference]
  by_cases active : (state.addTask task).2 = .active
  · have selected := (state.addTask_active_iff task present).mp active
    simp only [active, selected, ↓reduceIte, Bool.true_and, activateRegisteredTask]
    cases found : (state.addTask task).1.queue.taskNode? task.occurrence <;> rfl
  · have unselected : task.groups.any (fun group => state.queue.rootGroups.contains group.ref)
        = false := by
      cases selected
            : task.groups.any
                (fun group => state.queue.rootGroups.contains group.ref) with
      | false => rfl
      | true => exact (active ((state.addTask_active_iff task present).mpr selected)).elim
    simp only [active, unselected, ↓reduceIte, Bool.false_and, Bool.false_eq_true]

/-- Completing only the returned active subset recovers the whole reference task fold.
Witness: each eager insertion commutes with later registration, without erasing old nodes,
values or child-stream links. Root presence licenses the same activity decisions.
-/
theorem registerTasks_complete (tasks : List ReferenceWorkQueue.Task)
    (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
    (present : acc.1.queue.RootGroupsPresent)
    : activateRegisteredTasks (tasks.foldl registerTaskStep acc).1.queue
        (tasks.foldl registerTaskStep acc).2.1
      = tasks.foldl ReferenceWorkQueue.State.addTask
          (activateRegisteredTasks acc.1.queue acc.2.1) := by
  induction tasks generalizing acc with
  | nil => rfl
  | cons task rest ih =>
      have nextPresent : (registerTaskStep acc task).1.queue.RootGroupsPresent := by
        unfold registerTaskStep
        dsimp only
        split <;> exact addTask_rootsPresent present task
      rw [List.foldl_cons, ih _ nextPresent, List.foldl_cons]
      congr 1
      have completedPresent
          : (activateRegisteredTasks acc.1.queue acc.2.1).RootGroupsPresent := by
        change (registrationCore (activateRegisteredTasks acc.1.queue acc.2.1)).RootGroupsPresent
        rw [activateRegisteredTasks_core]
        exact present
      rw [addTask_complete_descriptor
        (state := { acc.1 with queue := activateRegisteredTasks acc.1.queue acc.2.1 })
        completedPresent, addTask_activateRegisteredTasks]
      cases disposition : (acc.1.addTask task).2 <;>
        simp only [registerTaskStep, disposition, reduceCtorEq, ↓reduceIte,
          activateRegisteredTasks, List.foldl_append,
          List.foldl_cons, List.foldl_nil]

-----------------------------------------------------------------------------------------
-- Completion preserves existing producer attachment, not just accounting fields
-----------------------------------------------------------------------------------------

/-- Completing a task never overwrites an already stored computation node. -/
theorem activateRegisteredTask_lookup {queue : ReferenceWorkQueue.State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (task : ReferenceWorkQueue.Task)
    : (activateRegisteredTask queue task).taskNode? occurrence = some node := by
  unfold activateRegisteredTask
  split
  · exact found
  · change (queue.taskNodes ++ ([{ task := task }] : List ReferenceWorkQueue.TaskNode)).find?
      (fun candidate => candidate.task.occurrence == occurrence) = some node
    change queue.taskNodes.find? (fun candidate => candidate.task.occurrence == occurrence)
      = some node at found
    rw [List.find?_append, found]
    rfl

/-- Completing the active subset retains the exact old producer, value and stream links. -/
theorem activateRegisteredTasks_lookup {queue : ReferenceWorkQueue.State}
    {occurrence node} (found : queue.taskNode? occurrence = some node)
    (tasks : List ReferenceWorkQueue.Task)
    : (activateRegisteredTasks queue tasks).taskNode? occurrence = some node := by
  induction tasks generalizing queue with
  | nil => exact found
  | cons task rest ih => exact ih (activateRegisteredTask_lookup found task)

private theorem putTaskNode_lookup_none {queue : ReferenceWorkQueue.State} {occurrence}
    (absent : queue.taskNode? occurrence = none) (updated : ReferenceWorkQueue.TaskNode)
    : (queue.putTaskNode updated).taskNode? occurrence = none := by
  apply List.find?_eq_none.mpr
  intro candidate member selected
  obtain ⟨old, member, same⟩ := List.mem_map.mp member
  have excluded := List.find?_eq_none.mp absent old member
  by_cases replace : (old.task.occurrence == updated.task.occurrence) = true
  · simp only [replace] at same
    subst candidate
    exact excluded ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mpr
      (((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp replace).trans
        ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp selected)))
  · simp only [replace] at same
    subst candidate
    exact excluded selected

private theorem activateRegisteredTask_putTaskNode {queue : ReferenceWorkQueue.State}
    {occurrence node} (found : queue.taskNode? occurrence = some node)
    (updated : ReferenceWorkQueue.TaskNode) (same : updated.task.occurrence = occurrence)
    (task : ReferenceWorkQueue.Task)
    : activateRegisteredTask (queue.putTaskNode updated) task
      = (activateRegisteredTask queue task).putTaskNode updated := by
  cases active : queue.taskNode? task.occurrence with
  | some present =>
      have next : (queue.putTaskNode updated).taskNode? task.occurrence
          = some (if updated.task.occurrence = task.occurrence then updated else present) := by
        by_cases equal : updated.task.occurrence = task.occurrence
        · simpa only [equal, ↓reduceIte]
            using ReferenceWorkQueue.State.putTaskNode_lookup_same active updated equal
        · simpa only [equal, ↓reduceIte]
            using ReferenceWorkQueue.State.putTaskNode_lookup_other active updated equal
      simp only [activateRegisteredTask, active, next, Option.isSome_some, ↓reduceIte]
  | none =>
      have next := putTaskNode_lookup_none active updated
      have different : task.occurrence ≠ updated.task.occurrence := by
        intro equal
        rw [equal, same, found] at active
        contradiction
      simp only [activateRegisteredTask, active, next, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte]
      simp only [ReferenceWorkQueue.State.putTaskNode,
        List.map_append, List.map_cons, List.map_nil]
      rw [show (task.occurrence == updated.task.occurrence) = false from
        Bool.eq_false_iff.mpr (fun equal => different
          ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp equal))]
      rfl

private theorem activateRegisteredTasks_putTaskNode {queue : ReferenceWorkQueue.State}
    {occurrence node} (found : queue.taskNode? occurrence = some node)
    (updated : ReferenceWorkQueue.TaskNode) (same : updated.task.occurrence = occurrence)
    (tasks : List ReferenceWorkQueue.Task)
    : activateRegisteredTasks (queue.putTaskNode updated) tasks
      = (activateRegisteredTasks queue tasks).putTaskNode updated := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      simp only [activateRegisteredTasks, List.foldl_cons]
      rw [activateRegisteredTask_putTaskNode found updated same task]
      exact ih (activateRegisteredTask_lookup found task)

private theorem activateRegisteredTasks_streams (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (streams : List ReferenceWorkQueue.Stream)
    : activateRegisteredTasks { queue with streams } tasks
      = { activateRegisteredTasks queue tasks with streams } := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      change activateRegisteredTasks (activateRegisteredTask { queue with streams } task) rest
        = { activateRegisteredTasks (activateRegisteredTask queue task) rest with streams }
      have head : activateRegisteredTask { queue with streams } task
          = { activateRegisteredTask queue task with streams } := by
        unfold activateRegisteredTask
        rw [show ({ queue with streams } : ReferenceWorkQueue.State).taskNode? task.occurrence
          = queue.taskNode? task.occurrence from rfl]
        split <;> rfl
      rw [head, ih]

private theorem taskNode?_with_streams (queue : ReferenceWorkQueue.State)
    (streams : List ReferenceWorkQueue.Stream) (occurrence : Occurrence)
    : ({ queue with streams } : ReferenceWorkQueue.State).taskNode? occurrence
      = queue.taskNode? occurrence :=
  rfl

/-- Active completion commutes with stream registration when its producer is already stored.
Witness: exact producer lookup is retained, and stream attachment commutes with appending
new empty nodes. Root stream registration has no producer premise. A missing raw producer
is deliberately excluded: eager completion could manufacture its attachment target.
-/
theorem activateRegisteredTasks_addStreams (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (streams : List ReferenceWorkQueue.Stream)
    (parent : Option Occurrence)
    (ready
      : ∀ occurrence,
          parent = some occurrence → (queue.taskNode? occurrence).isSome = true)
    : (
        activateRegisteredTasks (queue.addStreams streams parent).1 tasks,
        (queue.addStreams streams parent).2
      )
      = (activateRegisteredTasks queue tasks).addStreams streams parent := by
  have core := activateRegisteredTasks_core queue tasks
  have catalog := congrArg ReferenceWorkQueue.State.streams core
  change (activateRegisteredTasks queue tasks).streams = queue.streams at catalog
  have streamLookup (key : Nat) : (activateRegisteredTasks queue tasks).stream? key
      = queue.stream? key := by
    change ((activateRegisteredTasks queue tasks).streams.find? _) = _
    rw [catalog]
    rfl
  simp only [ReferenceWorkQueue.State.addStreams, streamLookup, catalog]
  cases parent with
  | none =>
      exact congrArg (fun current => (current, _))
        (activateRegisteredTasks_streams queue tasks _)
  | some occurrence =>
      cases found : queue.taskNode? occurrence with
      | none =>
          have impossible := ready occurrence rfl
          simp [found] at impossible
      | some node =>
          have retained := activateRegisteredTasks_lookup found tasks
          simp only [taskNode?_with_streams, found, retained]
          let fresh := streams.foldl
            (fun selected stream =>
              if (queue.stream? stream.node.ref).isSome
                  || selected.any (fun known => known.node.ref == stream.node.ref) then
                selected else selected ++ [stream]) []
          let updated : ReferenceWorkQueue.TaskNode :=
            { node with
              childStreams := node.childStreams ++ fresh.map (fun stream => stream.node.ref) }
          let prepared : ReferenceWorkQueue.State :=
            { queue with streams := queue.streams ++ fresh }
          have stored : prepared.taskNode? occurrence = some node := found
          have attached := activateRegisteredTasks_putTaskNode stored updated
            (ReferenceWorkQueue.State.taskNode?_some found).2 tasks
          have stable := activateRegisteredTasks_streams queue tasks (queue.streams ++ fresh)
          exact congrArg (fun current => (current, ([] : List Execution.DeliveryNode)))
            (attached.trans (congrArg (fun current => current.putTaskNode updated) stable))

-----------------------------------------------------------------------------------------
-- Complete scope correspondence and its connection to public delayed activation
-----------------------------------------------------------------------------------------

/-- Completing active registration gives the full reference scope, including held streams.
Witness: commute each exact eager insertion through subsequent registration and through
attachment to the existing producer. No task-node information is erased in this equality.
-/
theorem State.maybeIntegrateWork_complete (state : State) (work : ReferenceWorkQueue.Work)
    (present : state.queue.RootGroupsPresent) (parent : Option Occurrence := none)
    (ready
      : ∀ occurrence,
          parent = some occurrence
          → (state.queue.taskNode? occurrence).isSome = true := by simp)
    : let alternative := state.maybeIntegrateWork work parent
      let reference := state.queue.maybeIntegrateWork work parent
      activateRegisteredTasks alternative.1.queue alternative.2.activeTasks = reference.1
      ∧ alternative.2.newWork = reference.2 := by
  let grouped := (state.queue.addGroups work.groups).1
  let initial : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task :=
    ({ state with queue := grouped }, [], [])
  let registered := work.tasks.foldl registerTaskStep initial
  have groupedPresent : grouped.RootGroupsPresent := by
    intro key member
    rw [ReferenceWorkQueue.State.addGroups_rootGroups] at member
    exact ReferenceWorkQueue.State.addGroups_includesRefs state.queue work.groups key
      (present key member)
  have complete := registerTasks_complete work.tasks initial groupedPresent
  have nodes (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      : (tasks.foldl registerTaskStep acc).1.queue.taskNodes = acc.1.queue.taskNodes := by
    induction tasks generalizing acc with
    | nil => rfl
    | cons task rest ih =>
        rw [List.foldl_cons, ih]
        unfold registerTaskStep
        dsimp only
        split <;> exact acc.1.addTask_taskNodes task
  have retained : registered.1.queue.taskNodes = state.queue.taskNodes :=
    (nodes work.tasks initial).trans
      (ReferenceWorkQueue.State.addGroups_taskNodes state.queue work.groups)
  have registeredReady (occurrence : Occurrence) (same : parent = some occurrence)
      : (registered.1.queue.taskNode? occurrence).isSome = true := by
    change (registered.1.queue.taskNodes.find? _).isSome = true
    rw [retained]
    exact ready occurrence same
  have attached := activateRegisteredTasks_addStreams registered.1.queue registered.2.1
    work.streams parent registeredReady
  change activateRegisteredTasks
        (registered.1.queue.addStreams work.streams parent).1 registered.2.1
      = ((work.tasks.foldl ReferenceWorkQueue.State.addTask grouped).addStreams
          work.streams parent).1
    ∧ (⟨(state.queue.addGroups work.groups).2,
        (registered.1.queue.addStreams work.streams parent).2⟩ : ReferenceWorkQueue.NewWork)
      = ⟨(state.queue.addGroups work.groups).2,
        ((work.tasks.foldl ReferenceWorkQueue.State.addTask grouped).addStreams
          work.streams parent).2⟩
  change activateRegisteredTasks registered.1.queue registered.2.1
    = work.tasks.foldl ReferenceWorkQueue.State.addTask grouped at complete
  rw [complete] at attached
  have streams := congrArg (fun result : ReferenceWorkQueue.State × List Execution.DeliveryNode =>
    result.2) attached
  exact ⟨congrArg Prod.fst attached,
    congrArg (fun streams => (⟨(state.queue.addGroups work.groups).2, streams⟩
      : ReferenceWorkQueue.NewWork)) streams⟩

/-- The active projection contains only tasks from the newly exposed scope. -/
theorem State.maybeIntegrateWork_activeTasks {state : State}
    (work : ReferenceWorkQueue.Work) (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).2.activeTasks.Subset work.tasks := by
  have loop (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      : (tasks.foldl registerTaskStep acc).2.1.Subset (acc.2.1 ++ tasks) := by
    induction tasks generalizing acc with
    | nil =>
        intro candidate member
        exact List.mem_append_left [] member
    | cons task rest ih =>
        intro candidate member
        have after := ih (registerTaskStep acc task) member
        unfold registerTaskStep at after
        dsimp only at after
        split at after
        · simpa only [List.append_assoc, List.singleton_append] using after
        · exact List.mem_append.mpr ((List.mem_append.mp after).imp_right
            (List.mem_cons_of_mem task))
        · exact List.mem_append.mpr ((List.mem_append.mp after).imp_right
            (List.mem_cons_of_mem task))
  exact loop work.tasks
    ({ state with queue := (state.queue.addGroups work.groups).1 }, [], [])

/-- Scope registration appends its complete task catalogue once, independent of activation. -/
theorem State.maybeIntegrateWork_tasks (state : State) (work : ReferenceWorkQueue.Work)
    (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).1.queue.tasks
      = state.queue.tasks ++ work.tasks := by
  have loop (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      : (tasks.foldl registerTaskStep acc).1.queue.tasks = acc.1.queue.tasks ++ tasks := by
    induction tasks generalizing acc with
    | nil => simp
    | cons task rest ih =>
        rw [List.foldl_cons, ih]
        unfold registerTaskStep
        dsimp only
        split <;> rw [State.addTask_tasks] <;> simp only [List.append_assoc, List.singleton_append]
  unfold State.maybeIntegrateWork
  dsimp only
  rw [ReferenceWorkQueue.State.addStreams_tasks]
  change (work.tasks.foldl registerTaskStep
      ({ state with queue := (state.queue.addGroups work.groups).1 }, [], [])).1.queue.tasks
    = state.queue.tasks ++ work.tasks
  rw [loop, ReferenceWorkQueue.State.addGroups_tasks]

/-- Provenance turns exact eager completion into the public catalogue-based start fold.
Witness: each active descriptor is already registered; matching fixes the lookup result
even when a catalogue occurrence is repeated. Original nodes remain intact.
-/
theorem activateRegisteredTasks_eq_startTasks {queue : ReferenceWorkQueue.State}
    {work : Work} (matching : queue.RegisteredTasksMatch work)
    (tasks : List ReferenceWorkQueue.Task) (members : tasks.Subset queue.tasks)
    : activateRegisteredTasks queue tasks
      = tasks.foldl (fun current task => current.startTask task.occurrence) queue := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      have lookup := registeredTask_lookup matching (members List.mem_cons_self)
      have start : activateRegisteredTask queue task = queue.startTask task.occurrence := by
        unfold activateRegisteredTask ReferenceWorkQueue.State.startTask
        split
        · rfl
        · rw [lookup]
          rfl
      change activateRegisteredTasks (activateRegisteredTask queue task) rest
        = rest.foldl (fun current task => current.startTask task.occurrence)
          (queue.startTask task.occurrence)
      rw [start]
      apply ih (matching.startTask task.occurrence)
      intro candidate member
      have old := members (List.mem_cons_of_mem task member)
      unfold ReferenceWorkQueue.State.startTask
      split
      · exact old
      · split <;> exact old

/-- Actual delayed task starts recover the complete reference registration scope.
Witness: full descriptor completion plus structurally justified catalogue lookup, not
the weaker accounting projection. This precedes settlement and release activation.
-/
theorem State.maybeIntegrateWork_startTasks {state : State} {work : Work}
    (present : state.queue.RootGroupsPresent)
    (matching : state.queue.RegisteredTasksMatch work)
    (incoming : ReferenceWorkQueue.Work)
    (known : ∀ task ∈ incoming.tasks, ReferenceWorkQueue.TaskMatches work task)
    (parent : Option Occurrence := none)
    (ready
      : ∀ occurrence,
          parent = some occurrence
          → (state.queue.taskNode? occurrence).isSome = true := by simp)
    : let alternative := state.maybeIntegrateWork incoming parent
      let reference := state.queue.maybeIntegrateWork incoming parent
      alternative.2.activeTasks.foldl
          (fun current task => current.startTask task.occurrence) alternative.1.queue
        = reference.1
      ∧ alternative.2.newWork = reference.2 := by
  have complete := state.maybeIntegrateWork_complete incoming present parent ready
  dsimp only at complete
  have registered := state.maybeIntegrateWork_registeredTasksMatch matching incoming known parent
  have members : (state.maybeIntegrateWork incoming parent).2.activeTasks.Subset
      (state.maybeIntegrateWork incoming parent).1.queue.tasks := by
    intro task member
    rw [State.maybeIntegrateWork_tasks state incoming parent]
    exact List.mem_append_right _ (state.maybeIntegrateWork_activeTasks incoming parent member)
  rw [activateRegisteredTasks_eq_startTasks registered _ members] at complete
  exact complete

/-- Eager completion only appends computation records to its original store.
Witness: every individual activation keeps the store or appends one missing descriptor.
-/
theorem activateRegisteredTasks_taskNodes_sublist (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task)
    : queue.taskNodes.Sublist (activateRegisteredTasks queue tasks).taskNodes := by
  induction tasks generalizing queue with
  | nil => exact .refl _
  | cons task rest ih =>
      apply List.Sublist.trans (l₂ := (activateRegisteredTask queue task).taskNodes) ?_ (ih _)
      unfold activateRegisteredTask
      split
      · exact .refl _
      · exact (List.prefix_append _ _).sublist

/-- Actual cache-aware delayed starts recover reference registration after cache exposure.
Witness: exact eager scope completion supplies catalogue coherence and unique task keys;
the cache/start congruence then transports every active task under the supplied snapshot.
Intermediate rejections can differ before exposure. New-work notices are already identical.
-/
theorem State.maybeIntegrateWork_startTasks_cache {state : State} {work : Work}
    (present : state.queue.RootGroupsPresent)
    (matching : state.queue.RegisteredTasksMatch work)
    (unique : state.queue.TaskNodeKeysUnique)
    (incoming : ReferenceWorkQueue.Work)
    (known : ∀ task ∈ incoming.tasks, ReferenceWorkQueue.TaskMatches work task)
    (available : List (Occurrence × Nat)) (parent : Option Occurrence := none)
    (ready
      : ∀ occurrence,
          parent = some occurrence
          → (state.queue.taskNode? occurrence).isSome = true := by simp)
    : let alternative := state.maybeIntegrateWork incoming parent
      let reference := state.queue.maybeIntegrateWork incoming parent
      (alternative.2.activeTasks.foldl
          (fun current task => current.startTask task.occurrence available)
          alternative.1.queue).cacheTaskFailures
          available
        = reference.1.cacheTaskFailures available
      ∧ alternative.2.newWork = reference.2 := by
  have complete := state.maybeIntegrateWork_complete incoming present parent ready
  have started := state.maybeIntegrateWork_startTasks present matching incoming known parent ready
  dsimp only at complete started ⊢
  have finalKeys := unique.maybeIntegrateWork incoming parent
  rw [← complete.1] at finalKeys
  have initialKeys : (state.maybeIntegrateWork incoming parent).1.queue.TaskNodeKeysUnique :=
    finalKeys.sublist ((activateRegisteredTasks_taskNodes_sublist _ _).map _)
  have exposed := initialKeys.startTasks_cache_congr initialKeys available rfl
    ((state.maybeIntegrateWork incoming parent).2.activeTasks.map
      ReferenceWorkQueue.Task.occurrence)
  simp only [List.foldl_map] at exposed
  exact ⟨exposed.trans (congrArg (fun queue => queue.cacheTaskFailures available) started.1),
    started.2⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
