import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Task-node presence controls settlement handling. A first rejected task is selected
only as causal proof evidence; runtime startup reports every cached member rejection.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A settlement for an absent task leaves the queue unchanged and emits no value. -/
theorem State.taskSuccess_of_taskNode_none {queue : State} {occurrence : Occurrence}
    (absent : queue.taskNode? occurrence = none) (result : TaskResult)
    (available : List (Occurrence × Nat) := [])
    : queue.taskSuccess occurrence result available = (queue, [], []) := by
  simp only [State.taskSuccess, absent]

/-- A rejection for an absent task leaves the queue unchanged and emits no completion. -/
theorem State.taskFailure_of_taskNode_none {queue : State} {occurrence : Occurrence}
    (absent : queue.taskNode? occurrence = none) (errors : Nat)
    : queue.taskFailure occurrence errors = (queue, []) := by
  simp only [State.taskFailure, absent]

/-- Any success output came from a retained started task. -/
theorem State.taskSuccess_output_started {queue : State} {occurrence : Occurrence}
    {result : TaskResult} {available : List (Occurrence × Nat)}
    (emitted : (queue.taskSuccess occurrence result available).2.1 ≠ [])
    : ∃ node, queue.taskNode? occurrence = some node := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found] at emitted
  | some node => exact ⟨node, rfl⟩

/-- Any failure output came from a retained started task. -/
theorem State.taskFailure_output_started {queue : State} {occurrence : Occurrence}
    {errors : Nat} (emitted : (queue.taskFailure occurrence errors).2 ≠ [])
    : ∃ node, queue.taskNode? occurrence = some node := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found] at emitted
  | some node => exact ⟨node, rfl⟩

private theorem foldl_fixed {α β : Type} (step : α → β → α) (initial : α)
    (items : List β) (fixed : ∀ item ∈ items, step initial item = initial)
    : items.foldl step initial = initial := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      rw [List.foldl_cons, fixed item (by simp)]
      exact ih (fun other member => fixed other (List.mem_cons_of_mem _ member))

/-- When all contributing groups are dormant, rejection changes only the task's retained
computation. Group membership, pending counts, and notice state are preserved exactly.
-/
theorem State.taskFailure_dormant {queue : State} {occurrence : Occurrence}
    {node : TaskNode} (found : queue.taskNode? occurrence = some node) (errors : Nat)
    (dormant : ∀ group ∈ node.task.groups, queue.rootGroups.contains group.ref = false)
    : queue.taskFailure occurrence errors
      = (queue.putTaskNode { node with rejection := some errors }, []) := by
  simp only [State.taskFailure, found]
  apply foldl_fixed
  intro group member
  cases present
        : (queue.putTaskNode { node with rejection := some errors }).groupNode?
            group.ref with
  | none => simp
  | some owner =>
      have inactive : group.ref ∉ queue.rootGroups := by simpa using dormant group member
      simp [State.putTaskNode, inactive]

/-- Select one cached task to explain causal failure, without changing runtime reporting. -/
def State.rejectedTask? (state : State) (group : GroupNode) : Option (Occurrence × Nat) :=
  group.tasks.findSome?
    fun occurrence => do
      let task ← state.taskNode? occurrence
      let errors ← task.rejection
      return (occurrence, errors)

/-- A selected causal explanation uses a listed task and its retained computation. -/
theorem State.rejectedTask?_sound {queue : State} {group : GroupNode}
    {occurrence : Occurrence} {errors : Nat}
    (selected : queue.rejectedTask? group = some (occurrence, errors))
    : occurrence ∈ group.tasks
      ∧ ∃ node,
          queue.taskNode? occurrence = some node ∧ node.rejection = some errors := by
  unfold State.rejectedTask? at selected
  obtain ⟨task, member, returned⟩ := List.exists_of_findSome?_eq_some selected
  cases found : queue.taskNode? task with
  | none => simp [found] at returned
  | some node =>
      cases rejected : node.rejection with
      | none => simp [found, rejected] at returned
      | some count =>
          simp [found, rejected] at returned
          obtain ⟨rfl, rfl⟩ := returned
          exact ⟨member, node, found, rejected⟩

/-- Replay finds no rejection exactly when every retained member task is unrejected.
Missing task nodes are skipped, independently of group ancestry or cancellation history.
-/
theorem State.rejectedTask?_eq_none_iff {queue : State} {group : GroupNode}
    : queue.rejectedTask? group = none
      ↔ ∀ occurrence ∈ group.tasks,
          ∀ node, queue.taskNode? occurrence = some node → node.rejection = none := by
  unfold State.rejectedTask?
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro empty occurrence member node found
    have missing := empty occurrence member
    cases rejected : node.rejection <;> simp_all
  · intro empty occurrence member
    cases found : queue.taskNode? occurrence with
    | none => simp
    | some node => simp [empty occurrence member node found]

/-- Replay selects the first retained rejection in registration order, regardless of
which computation settled first. Earlier entries may be absent or unrejected.
-/
theorem State.rejectedTask?_first {queue : State} {group : GroupNode}
    {before after : List Occurrence} {occurrence : Occurrence} {node : TaskNode}
    {errors : Nat} (order : group.tasks = before ++ occurrence :: after)
    (found : queue.taskNode? occurrence = some node)
    (rejected : node.rejection = some errors)
    (earlier
      : ∀ task ∈ before,
          ∀ retained, queue.taskNode? task = some retained → retained.rejection = none)
    : queue.rejectedTask? group = some (occurrence, errors) := by
  unfold State.rejectedTask?
  apply List.findSome?_eq_some_iff.mpr
  refine ⟨before, occurrence, after, order, by simp [found, rejected], ?_⟩
  intro task member
  cases present : queue.taskNode? task with
  | none => simp
  | some retained => simp [earlier task member retained present]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
