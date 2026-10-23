import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalBasics

/-! Failed settlements preserve counters on surviving dormant owners. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Removing groups leaves the exact debt of every survivor unchanged.
Witness: the implementation filters live group nodes without changing their fields.
-/
theorem State.PendingDebt.removeGroup {queue : State} {eligible settled remaining}
    (tracks : queue.PendingDebt eligible settled remaining) (ref : NodeRef)
    : (queue.removeGroup ref).PendingDebt eligible settled remaining := by
  intro node member relevant
  exact tracks node (List.mem_filter.mp member).1 relevant

/-- The literal failure-owner fold, named only for induction proofs.
Active owners close immediately; dormant owners retain their pending counters.
-/
def failureGroupStep (errors : Nat) (acc : State × List WorkQueueEvent)
    (group : Execution.DeliveryNode)
    : State × List WorkQueueEvent :=
  let (current, events) := acc
  match current.groupNode? group.ref with
  | none => (current, events)
  | some node =>
      if current.rootGroups.contains group.ref then
        let (next, failure) := current.finishGroupFailure node errors
        (next, events ++ [.groupFailure failure.group failure.errors])
      else
        (current, events)

/-- The failure-owner fold preserves every invariant stable under group removal.
Witness: dormant owners are unchanged and active owners are removed.
-/
theorem failureGroupFold_preserves (invariant : State → Prop)
    (remove : ∀ queue ref, invariant queue → invariant (queue.removeGroup ref))
    (errors : Nat) (groups : List Execution.DeliveryNode)
    (acc : State × List WorkQueueEvent) (valid : invariant acc.1)
    : invariant (groups.foldl (failureGroupStep errors) acc).1 := by
  induction groups generalizing acc with
  | nil => exact valid
  | cons group rest ih =>
      apply ih
      obtain ⟨queue, events⟩ := acc
      dsimp only [failureGroupStep]
      split
      · exact valid
      · split
        · exact remove queue _ valid
        · exact valid

/-- Owner removal preserves an invariant when each visited ref has a fixed certificate.
Witness: induction on the actual owner fold, exposing the ref of every removed group.
-/
theorem failureGroupFold_preserves_on (invariant : State → Prop)
    (allowed : NodeRef → Prop)
    (remove
      : ∀ queue ref, invariant queue → allowed ref → invariant (queue.removeGroup ref))
    (errors : Nat) (groups : List Execution.DeliveryNode)
    (supported : ∀ group ∈ groups, allowed group.ref) (acc : State × List WorkQueueEvent)
    (valid : invariant acc.1)
    : invariant (groups.foldl (failureGroupStep errors) acc).1 := by
  induction groups generalizing acc with
  | nil => exact valid
  | cons group rest ih =>
      apply ih (fun next member => supported next (List.mem_cons_of_mem _ member))
      obtain ⟨queue, events⟩ := acc
      dsimp only [failureGroupStep]
      split
      · exact valid
      · rename_i node found
        split
        · apply remove queue _ valid
          rw [queue.groupNode?_ref found]
          exact supported group List.mem_cons_self
        · exact valid

/-- Failure-owner processing retains only old task nodes. -/
theorem failureGroupFold_taskNodes_subset (errors : Nat)
    (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
    : (groups.foldl (failureGroupStep errors) acc).1.taskNodes.Subset
        acc.1.taskNodes := by
  apply failureGroupFold_preserves (fun state => state.taskNodes.Subset acc.1.taskNodes)
    (fun _ _ prior node member => prior (List.mem_filter.mp member).1)
  exact List.Subset.refl _

/-- Failure-owner processing leaves every surviving group record unchanged. -/
theorem failureGroupFold_groupNodes_subset (errors : Nat)
    (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
    : (groups.foldl (failureGroupStep errors) acc).1.groupNodes.Subset
        acc.1.groupNodes := by
  apply failureGroupFold_preserves (fun state => state.groupNodes.Subset acc.1.groupNodes)
    (fun _ _ prior node member => prior (List.mem_filter.mp member).1)
  exact List.Subset.refl _

/-- Task failure retains its rejected computation before visiting its owners.
Witness: the handler's definition; no group-level failure cache is introduced.
-/
theorem State.taskFailure_eq {queue : State} (occurrence : Occurrence) (errors : Nat)
    (node : TaskNode) (found : queue.taskNode? occurrence = some node)
    : queue.taskFailure occurrence errors
      = node.task.groups.foldl (failureGroupStep errors)
          (queue.putTaskNode { node with rejection := some errors }, []) := by
  simp only [State.taskFailure, found]
  rfl

/-- Every event emitted by task rejection is a failed group completion.
Witness: each owner step either appends that one constructor or leaves output unchanged.
-/
theorem State.taskFailure_event_failure (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : ∀ event ∈ (queue.taskFailure occurrence errors).2,
        ∃ group, event = Execution.WorkQueueEvent.groupFailure group errors := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : ∀ event ∈ acc.2, ∃ group, event = Execution.WorkQueueEvent.groupFailure group errors)
      : ∀ event ∈ (groups.foldl (failureGroupStep errors) acc).2,
          ∃ group, event = Execution.WorkQueueEvent.groupFailure group errors := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        obtain ⟨current, events⟩ := acc
        dsimp only [failureGroupStep]
        split
        · exact prior
        · split
          · intro event member
            rcases List.mem_append.mp member with old | new
            · exact prior event old
            · exact ⟨_, List.mem_singleton.mp new⟩
          · exact prior
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found]
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      exact loop task.task.groups _ (by simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
