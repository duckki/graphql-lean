import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDebt

/-! Immediate failed-closure provenance. Cached startup notices are returned separately
and forwarded only after the current host batch has been consumed.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Recursive release transfers cached-error facts to emitted failures
-----------------------------------------------------------------------------------------

/-- A successful flush emits no failed group closure.
Witness: its output is optional values followed by exactly one successful closure.
-/
theorem State.finishGroupSuccess_groupFailure_absent (queue : State) (node : GroupNode)
    (group : Execution.DeliveryNode) (errors : Nat)
    : Execution.WorkQueueEvent.groupFailure group errors
      ∉ (queue.finishGroupSuccess node).2.1 := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output]
  split <;> simp

/-- A task-failure handler emits its own count only for one of the task's contributors.
Witness: the actual owner fold emits only active-group failures; latent updates emit none.
-/
theorem State.taskFailure_groupFailure_current (queue : State) (occurrence : Occurrence)
    (errors : Nat) {group count}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group count
        ∈ (queue.taskFailure occurrence errors).2)
    : ∃ task,
        queue.taskNode? occurrence = some task
        ∧ group.ref ∈ task.task.groups.map Execution.DeliveryNode.ref
        ∧ count = errors := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      : Execution.WorkQueueEvent.groupFailure group count
          ∈ (groups.foldl (failureGroupStep errors) acc).2
        → Execution.WorkQueueEvent.groupFailure group count ∈ acc.2
          ∨ group.ref ∈ groups.map Execution.DeliveryNode.ref ∧ count = errors := by
    induction groups generalizing acc with
    | nil => exact Or.inl
    | cons owner rest ih =>
        intro member
        obtain ⟨current, events⟩ := acc
        rcases ih (failureGroupStep errors (current, events) owner) member with first | later
        · dsimp only [failureGroupStep] at first
          split at first
          · exact Or.inl first
          · rename_i node found
            split at first
            · rcases List.mem_append.mp first with earlier | latest
              · exact Or.inl earlier
              · have same :=
                  Execution.WorkQueueEvent.groupFailure.inj (List.mem_singleton.mp latest)
                exact Or.inr ⟨by simp [same.1, current.groupNode?_ref found,
                  State.finishGroupFailure], same.2⟩
            · exact Or.inl first
        · exact Or.inr ⟨List.mem_cons_of_mem _ later.1, later.2⟩
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found] at emitted
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found] at emitted
      have origin := loop task.task.groups
        (queue.putTaskNode { task with rejection := some errors }, []) emitted
      exact ⟨task, rfl, origin.resolve_left (by simp)⟩

/-- The drain's immediate outputs contain only successful closures and values. -/
theorem State.drainReadyGroups_groupFailure_absent (queue : State)
    (group : Execution.DeliveryNode) (errors : Nat)
    (available : List (Occurrence × Nat) := [])
    : WorkQueueEvent.groupFailure group errors
      ∉ (queue.drainReadyGroups available).2.1 := by
  have loop (fuel : Nat) (current : State)
      : WorkQueueEvent.groupFailure group errors
        ∉ (State.drainReadyGroups.go available fuel current).2.1 := by
    induction fuel generalizing current with
    | zero => simp [State.drainReadyGroups.go]
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · simp
        · rename_i node found
          intro member
          rcases List.mem_append.mp member with first | later
          · exact current.finishGroupSuccess_groupFailure_absent node group errors first
          · exact ih _ later
  exact loop _ queue

/-- Task success returns startup failures separately from its immediate work events. -/
theorem State.taskSuccess_groupFailure_absent (queue : State) (occurrence : Occurrence)
    (result : TaskResult) (group : Execution.DeliveryNode) (errors : Nat)
    (available : List (Occurrence × Nat) := [])
    : WorkQueueEvent.groupFailure group errors
      ∉ (queue.taskSuccess occurrence result available).2.1 := by
  have fold (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (absent : WorkQueueEvent.groupFailure group errors ∉ acc.2.1)
      : WorkQueueEvent.groupFailure group errors
        ∉ (groups.foldl successGroupStep acc).2.1 := by
    induction groups generalizing acc with
    | nil => exact absent
    | cons owner rest ih =>
        apply ih
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact absent
        · rename_i node found
          split
          · intro member
            exact (List.mem_append.mp member).elim absent
              (State.finishGroupSuccess_groupFailure_absent _ _ group errors)
          · exact absent
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      intro member
      rcases List.mem_append.mp member with earlier | later
      · exact fold node.task.groups (_, [], {}) (by simp) earlier
      · exact State.drainReadyGroups_groupFailure_absent _ group errors available later

/-- Stream-item arrival also defers startup failures outside its immediate outputs. -/
theorem State.streamItems_groupFailure_absent (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (group : Execution.DeliveryNode) (errors : Nat)
    (available : List (Occurrence × Nat) := [])
    : WorkQueueEvent.groupFailure group errors
      ∉ (queue.streamItems stream items available).2.1 := by
  unfold State.streamItems
  split
  · simp
  · intro member
    have later := (List.mem_cons.mp member).resolve_left (by intro same; cases same)
    exact State.drainReadyGroups_groupFailure_absent _ group errors available later

/-- Forwarding uses the queued head's complete stored payload. -/
theorem State.groupFailure_origin (queue : State) (supplied : GroupFailureEvent)
    {group errors}
    (emitted : WorkQueueEvent.groupFailure group errors ∈ (queue.groupFailure supplied).2)
    : ∃ rest, queue.groupFailureEvents = ⟨group, errors⟩ :: rest := by
  unfold State.groupFailure at emitted
  split at emitted
  · cases emitted
  · rename_i first rest queued
    split at emitted
    · have same := List.mem_singleton.mp emitted
      obtain ⟨sameGroup, sameErrors⟩ := WorkQueueEvent.groupFailure.inj same
      cases first with
      | mk firstGroup firstErrors =>
          cases sameGroup
          cases sameErrors
          exact ⟨rest, queued⟩
    · cases emitted

/-- A failed closure comes from the current task outcome or the stored notice FIFO head.
Startup removal and later notification consumption are separate transitions.
-/
theorem State.handleGraphEvent_groupFailure_origin (queue : State) (event : GraphEvent)
    {group errors} (available : List (Occurrence × Nat) := [])
    (emitted
      : WorkQueueEvent.groupFailure group errors
        ∈ (queue.handleGraphEvent event available).2.1)
    : (∃ occurrence task,
        event = .taskFailure occurrence errors
        ∧ (queue.cacheTaskFailures available).taskNode? occurrence = some task
        ∧ group.ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
      ∨ ∃ supplied rest,
          event = .groupFailure supplied
          ∧ queue.groupFailureEvents = ⟨group, errors⟩ :: rest := by
  cases event with
  | taskSuccess occurrence result =>
      exact (State.taskSuccess_groupFailure_absent
        _ occurrence result group errors available emitted).elim
  | taskFailure occurrence count =>
      obtain ⟨task, found, owner, same⟩ :=
        State.taskFailure_groupFailure_current
          (queue.cacheTaskFailures available) occurrence count emitted
      subst count
      exact .inl ⟨occurrence, task, rfl, found, owner⟩
  | groupFailure supplied =>
      obtain ⟨rest, queued⟩ := (queue.cacheTaskFailures available).groupFailure_origin supplied emitted
      rw [State.cacheTaskFailures_groupFailureEvents] at queued
      exact .inr ⟨supplied, rest, rfl, queued⟩
  | streamItems stream items =>
      exact (State.streamItems_groupFailure_absent
        _ stream items group errors available emitted).elim
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess] at emitted
      split at emitted <;> simp at emitted
  | streamFailure stream count =>
      simp only [State.handleGraphEvent, State.streamFailure] at emitted
      split at emitted <;> simp at emitted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
