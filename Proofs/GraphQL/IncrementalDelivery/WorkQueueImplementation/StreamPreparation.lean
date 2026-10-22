import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectPublications
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage

/-! Proof-facing names for the item-integration phase before the shared ready drain. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

/-- One actual item-fold step retains its accumulated notices and item values.
`acc` is the current queue and this handler's output metadata; `item` supplies new work.
This is a definitional proof helper for the loop inside `State.streamItems`.
-/
def streamItemStep
    (acc
      : State
        × List Execution.DeliveryNode
        × List Execution.DeliveryNode
        × List StreamItemValue
        × List GroupFailureEvent)
    (item : StreamItem) (available : List (Occurrence × Nat) := [])
    : State
      × List Execution.DeliveryNode
      × List Execution.DeliveryNode
      × List StreamItemValue
      × List GroupFailureEvent :=
  let (current, groups, streams, values, failures) := acc
  let (integrated, newWork) := current.maybeIntegrateWork item.work
  let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
  let (started, queued) :=
    pruned.startNewWork { newWork with newGroups := nonempty } available
  (
    started,
    groups ++ nonempty,
    streams ++ newWork.newStreams,
    values ++ [item.value],
    failures ++ queued
  )

/-- The queue after integrating `items`, before emitting their value event and draining. -/
def State.preparedStreamItems (queue : State) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    : State :=
  (items.foldl (fun acc item => streamItemStep acc item available)
    (queue, [], [], [], [])).1

/-- Any invariant preserved by each actual item integration holds at drain entry.
Witness: induction on the concrete metadata-carrying item fold, projecting its queue.
-/
theorem State.preparedStreamItems_preserves (property : State → Prop)
    {queue : State} (initial : property queue) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    (step
      : ∀ current item,
          item ∈ items
          → property current
          → property (current.integrateStreamItem item available))
    : property (queue.preparedStreamItems items available) := by
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue
        × List GroupFailureEvent)
      (prior : property acc.1)
      : property (more.foldl (fun acc item => streamItemStep acc item available) acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (step acc.1 item (included List.mem_cons_self) prior)
  exact loop items (List.Subset.refl _) (queue, [], [], [], []) initial

/-- The named preparation is definitionally the implementation's metadata-carrying loop.
Witness: unfold the proof helper; no scheduling or generated-work premise is involved.
-/
theorem State.streamItems_eq (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat) := [])
    : queue.streamItems stream items available
      = if !queue.rootStreams.contains stream.ref then
          (queue, [], [])
        else
          let prepared :=
            items.foldl (fun acc item => streamItemStep acc item available)
              (queue, [], [], [], [])
          let drained := prepared.1.drainReadyGroups available
          (
            drained.1,
            .streamValues stream prepared.2.2.2.1 prepared.2.1 prepared.2.2.1
            :: drained.2.1,
            prepared.2.2.2.2 ++ drained.2.2
          ) :=
  rfl

/-- An item handler's object block comes from its drain after the leading item event.
Witness: rejected input emits nothing; accepted input prepends one object-free event.
The exact strict object projection and final queue agree with the drain's own boundary.
-/
theorem State.streamItems_value_boundary (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) {position group values}
    (available : List (Occurrence × Nat) := [])
    (selected
      : (queue.streamItems stream items available).2.1[position]?
        = some (.groupValues group values))
    : queue.rootStreams.contains stream.ref = true
      ∧ ∃ index,
          ((queue.preparedStreamItems items available).drainReadyGroups
              available).2.1[index]?
            = some (.groupValues group values)
          ∧ ((queue.streamItems stream items available).2.1.take position).flatMap
              WorkQueueEvent.objectValues
            = (((queue.preparedStreamItems items available).drainReadyGroups
                  available).2.1.take
                index).flatMap
                WorkQueueEvent.objectValues
          ∧ (queue.streamItems stream items available).1
            = ((queue.preparedStreamItems items available).drainReadyGroups
                available).1 := by
  rw [queue.streamItems_eq stream items available] at selected ⊢
  cases active : queue.rootStreams.contains stream.ref with
  | false =>
      simp only [active, Bool.not_false, ↓reduceIte, List.getElem?_nil,
        reduceCtorEq] at selected
  | true =>
      simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      cases position with
      | zero => cases selected
      | succ index =>
          exact ⟨trivial, index, selected, rfl, rfl⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
