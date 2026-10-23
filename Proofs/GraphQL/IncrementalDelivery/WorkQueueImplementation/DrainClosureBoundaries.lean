import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainValueCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerConservation

/-! Indexed successful drain outputs identify their exact executable closure boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Invert a selected ready group and the final carrier of its successful flush
-----------------------------------------------------------------------------------------

/-- The drain's selected record is live and active, with zero pending.
Witness: invert the actual root-ref search and its successful group lookup.
-/
theorem State.readyGroup_sound {queue : State} {group : GroupNode}
    (selected
      : queue.rootGroups.findSome?
          (fun ref => do
            let node ← queue.groupNode? ref
            if node.pending == 0 then
              some node
            else
              none)
        = some group)
    : queue.groupNode? group.group.node.ref = some group
      ∧ group.group.node.ref ∈ queue.rootGroups
      ∧ group.pending = 0 := by
  obtain ⟨ref, active, choice⟩ := List.exists_of_findSome?_eq_some selected
  cases found : queue.groupNode? ref with
  | none => simp [found] at choice
  | some node =>
      simp only [found] at choice
      change (if node.pending == 0 then some node else none) = some group
        at choice
      split at choice
      · rename_i ready
        obtain rfl := Option.some.inj choice
        have same := State.groupNode?_ref found
        exact ⟨same ▸ found, same ▸ active, by simpa using ready⟩
      · contradiction

/-- An indexed successful flush carrier is its final event, after precisely its value prefix.
Witness: the executable selected-node witness emits at most one value event and then its
unchanged completion carrier. No uniqueness of group descriptors is assumed.
-/
theorem State.finishGroupSuccess_index_prefix (queue : State) (node : GroupNode)
    {index group groups streams}
    (selected
      : (queue.finishGroupSuccess node).2.1[index]?
        = some (.groupSuccess group groups streams))
    : ∃ before,
        node.group.node = group
        ∧ (queue.finishGroupSuccess node).2.1
          = before ++ [.groupSuccess group groups streams]
        ∧ (queue.finishGroupSuccess node).2.1.take index = before := by
  obtain ⟨chosen, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output] at selected ⊢
  by_cases empty : (chosen.filterMap TaskNode.value).isEmpty = true
  · simp only [empty, ↓reduceIte, List.nil_append] at selected ⊢
    cases index with
    | zero =>
        obtain ⟨rfl, rfl, rfl⟩ :=
          Execution.WorkQueueEvent.groupSuccess.inj (Option.some.inj selected)
        exact ⟨[], rfl, rfl, rfl⟩
    | succ index => simp at selected
  · simp only [empty] at selected ⊢
    cases index with
    | zero => cases selected
    | succ index =>
        cases index with
        | zero =>
            obtain ⟨rfl, rfl, rfl⟩ :=
              Execution.WorkQueueEvent.groupSuccess.inj (Option.some.inj selected)
            exact ⟨[.groupValues node.group.node (chosen.filterMap TaskNode.value)],
              rfl, rfl, rfl⟩
        | succ index => simp at selected

/-- An indexed value block is the first event of its successful group flush.
Witness: inspect the optional value event before the unconditional completion carrier.
-/
theorem State.finishGroupSuccess_value_index (queue : State) (node : GroupNode)
    {index group values}
    (selected
      : (queue.finishGroupSuccess node).2.1[index]? = some (.groupValues group values))
    : index = 0 ∧ node.group.node = group := by
  obtain ⟨chosen, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output] at selected
  by_cases empty : (chosen.filterMap TaskNode.value).isEmpty = true
  · simp only [empty, ↓reduceIte, List.nil_append] at selected
    cases index with
    | zero => cases selected
    | succ index => simp at selected
  · simp only [empty] at selected
    cases index with
    | zero =>
        exact ⟨rfl, (Execution.WorkQueueEvent.groupValues.inj (Option.some.inj selected)).1⟩
    | succ index =>
        cases index with
        | zero => cases selected
        | succ index => simp at selected

-----------------------------------------------------------------------------------------
-- Recover the real bounded-drain prefix for an exact output position
-----------------------------------------------------------------------------------------

/-- Every indexed drain value block starts at an exact internal drain boundary.
Witness: follow successful closure blocks to their live, active zero-pending group.
The recovered prefix excludes the selected value block itself.
-/
theorem State.drainReadyGroups_go_value_boundary (fuel : Nat) (queue : State)
    {index group values} (available : List (Occurrence × Nat) := [])
    (selected
      : (State.drainReadyGroups.go available fuel queue).2.1[index]?
        = some (.groupValues group values))
    : ∃ steps node,
        steps < fuel
        ∧ (State.drainReadyGroups.go available steps queue).1.groupNode?
            node.group.node.ref
          = some node
        ∧ node.group.node.ref
          ∈ (State.drainReadyGroups.go available steps queue).1.rootGroups
        ∧ node.pending = 0
        ∧ node.group.node = group
        ∧ (State.drainReadyGroups.go available fuel queue).2.1.take index
          = (State.drainReadyGroups.go available steps queue).2.1 := by
  induction fuel generalizing queue index with
  | zero => simp [State.drainReadyGroups.go] at selected
  | succ fuel ih =>
      cases ready
            : queue.rootGroups.findSome?
                (fun ref => do
                  let node ← queue.groupNode? ref
                  if node.pending == 0 then some node else none) with
      | none =>
          simp only [State.drainReadyGroups.go, ready, List.getElem?_nil] at selected
          contradiction
      | some node =>
          obtain ⟨found, active, zero⟩ := State.readyGroup_sound ready
          let next := ((queue.finishGroupSuccess node).1.startNewWork
            (queue.finishGroupSuccess node).2.2 available).1
          let emitted := (queue.finishGroupSuccess node).2.1
          have state (count : Nat)
              : (State.drainReadyGroups.go available (count + 1) queue).1
                = (State.drainReadyGroups.go available count next).1 := by
            simp only [State.drainReadyGroups.go, ready]
            rfl
          have events (count : Nat)
              : (State.drainReadyGroups.go available (count + 1) queue).2.1
                = emitted ++ (State.drainReadyGroups.go available count next).2.1 := by
            simp only [State.drainReadyGroups.go, ready]
            rfl
          rw [events fuel] at selected
          by_cases inside : index < emitted.length
          · have atFlush := selected
            rw [List.getElem?_append_left inside] at atFlush
            obtain ⟨rfl, same⟩ := queue.finishGroupSuccess_value_index node atFlush
            exact ⟨0, node, by omega, found, active, zero, same,
              by simp [State.drainReadyGroups.go]⟩
          · have outside : emitted.length ≤ index := by omega
            rw [List.getElem?_append_right outside] at selected
            obtain ⟨steps, later, bound, lookup, root, zero, same, exactPrefix⟩ :=
              ih next selected
            refine ⟨steps + 1, later, by omega, ?_, ?_, zero, same, ?_⟩
            · simpa only [state] using lookup
            · simpa only [state] using root
            · rw [events fuel, List.take_append, List.take_of_length_le outside,
                exactPrefix, events]

/-- Every indexed successful drain carrier has a concrete earlier drain boundary.
Witness: recurse through actual successful closure blocks, retaining silent prefixes and
exact output offsets. Startup failure notices have a separate return component.
-/
theorem State.drainReadyGroups_go_success_boundary_selected (fuel : Nat)
    (queue : State) {index group groups streams}
    (available : List (Occurrence × Nat) := [])
    (selected
      : (State.drainReadyGroups.go available fuel queue).2.1[index]?
        = some (.groupSuccess group groups streams))
    : ∃ steps node before,
        steps < fuel
        ∧ (State.drainReadyGroups.go available steps queue).1.rootGroups.findSome?
            (fun ref => do
              let candidate ←
                (State.drainReadyGroups.go available steps queue).1.groupNode? ref
              if candidate.pending == 0 then some candidate else none)
          = some node
        ∧ (State.drainReadyGroups.go available steps queue).1.groupNode?
            node.group.node.ref
          = some node
        ∧ node.group.node.ref
          ∈ (State.drainReadyGroups.go available steps queue).1.rootGroups
        ∧ node.pending = 0
        ∧ node.group.node = group
        ∧ ((State.drainReadyGroups.go available steps queue).1.finishGroupSuccess
            node).2.1
          = before ++ [.groupSuccess group groups streams]
        ∧ (State.drainReadyGroups.go available fuel queue).2.1.take index
          = (State.drainReadyGroups.go available steps queue).2.1 ++ before
        ∧ ( let closed :=
              (State.drainReadyGroups.go available steps queue).1.finishGroupSuccess node
            ((closed.1.startNewWork closed.2.2 available).1.cancelledGroups).Subset
              (State.drainReadyGroups.go available fuel queue).1.cancelledGroups) := by
  induction fuel generalizing queue index with
  | zero => simp [State.drainReadyGroups.go] at selected
  | succ fuel ih =>
      cases ready
            : queue.rootGroups.findSome?
                (fun ref => do
                  let node ← queue.groupNode? ref
                  if node.pending == 0 then some node else none) with
      | none =>
          simp only [State.drainReadyGroups.go, ready, List.getElem?_nil] at selected
          contradiction
      | some node =>
          obtain ⟨found, active, zero⟩ := State.readyGroup_sound ready
          let next := ((queue.finishGroupSuccess node).1.startNewWork
            (queue.finishGroupSuccess node).2.2 available).1
          let emitted := (queue.finishGroupSuccess node).2.1
          have state (count : Nat)
              : (State.drainReadyGroups.go available (count + 1) queue).1
                = (State.drainReadyGroups.go available count next).1 := by
            simp only [State.drainReadyGroups.go, ready]
            rfl
          have events (count : Nat)
              : (State.drainReadyGroups.go available (count + 1) queue).2.1
                = emitted ++ (State.drainReadyGroups.go available count next).2.1 := by
            simp only [State.drainReadyGroups.go, ready]
            rfl
          rw [events fuel] at selected
          by_cases inside : index < emitted.length
          · have atFlush := selected
            rw [List.getElem?_append_left inside] at atFlush
            obtain ⟨before, same, output, exactPrefix⟩ :=
              queue.finishGroupSuccess_index_prefix node atFlush
            refine ⟨
              0,
              node,
              before,
              by omega,
              ready,
              found,
              active,
              zero,
              same,
              output,
              ?_,
              ?_
            ⟩
            · rw [events fuel]
              simpa only [List.take_append_of_le_length (Nat.le_of_lt inside),
                State.drainReadyGroups.go, List.nil_append] using exactPrefix
            · simpa only [State.drainReadyGroups.go, ready]
                using State.drainReadyGroups_go_cancelledGroups_subset fuel next available
          · have outside : emitted.length ≤ index := by omega
            rw [List.getElem?_append_right outside] at selected
            obtain ⟨steps, later, before, bound, chosen, lookup, root, zero, same, output,
              exactPrefix, cancelled⟩ := ih next selected
            refine ⟨steps + 1, later, before, by omega, ?_, ?_, ?_, zero, same, ?_, ?_, ?_⟩
            · simpa only [state] using chosen
            · simpa only [state] using lookup
            · simpa only [state] using root
            · simpa only [state] using output
            · rw [events fuel, List.take_append, List.take_of_length_le outside,
                exactPrefix, events]
              simp only [List.append_assoc]
            · simpa only [state] using cancelled

/-- Retain startup cancellation while projecting the established carrier-boundary interface. -/
theorem State.drainReadyGroups_go_success_boundary_withCancellation (fuel : Nat)
    (queue : State) {index group groups streams}
    (available : List (Occurrence × Nat) := [])
    (selected
      : (State.drainReadyGroups.go available fuel queue).2.1[index]?
        = some (.groupSuccess group groups streams))
    : ∃ steps node before,
        steps < fuel
        ∧ (State.drainReadyGroups.go available steps queue).1.groupNode?
            node.group.node.ref
          = some node
        ∧ node.group.node.ref
          ∈ (State.drainReadyGroups.go available steps queue).1.rootGroups
        ∧ node.pending = 0
        ∧ node.group.node = group
        ∧ ((State.drainReadyGroups.go available steps queue).1.finishGroupSuccess
            node).2.1
          = before ++ [.groupSuccess group groups streams]
        ∧ (State.drainReadyGroups.go available fuel queue).2.1.take index
          = (State.drainReadyGroups.go available steps queue).2.1 ++ before
        ∧ ( let closed :=
              (State.drainReadyGroups.go available steps queue).1.finishGroupSuccess node
            ((closed.1.startNewWork closed.2.2 available).1.cancelledGroups).Subset
              (State.drainReadyGroups.go available fuel queue).1.cancelledGroups) := by
  obtain ⟨steps, node, before, bounded, _, found, active, zero, same, output,
    exactPrefix, cancelled⟩ :=
    State.drainReadyGroups_go_success_boundary_selected fuel queue available selected
  exact ⟨steps, node, before, bounded, found, active, zero, same, output,
    exactPrefix, cancelled⟩

/-- An indexed successful carrier identifies its exact pre-flush state and strict output.
Witness: project the stronger boundary certificate that also retains startup cancellation.
-/
theorem State.drainReadyGroups_go_success_boundary (fuel : Nat) (queue : State)
    {index group groups streams} (available : List (Occurrence × Nat) := [])
    (selected
      : (State.drainReadyGroups.go available fuel queue).2.1[index]?
        = some (.groupSuccess group groups streams))
    : ∃ steps node before,
        steps < fuel
        ∧ (State.drainReadyGroups.go available steps queue).1.groupNode?
            node.group.node.ref
          = some node
        ∧ node.group.node.ref
          ∈ (State.drainReadyGroups.go available steps queue).1.rootGroups
        ∧ node.pending = 0
        ∧ node.group.node = group
        ∧ ((State.drainReadyGroups.go available steps queue).1.finishGroupSuccess
            node).2.1
          = before ++ [.groupSuccess group groups streams]
        ∧ (State.drainReadyGroups.go available fuel queue).2.1.take index
          = (State.drainReadyGroups.go available steps queue).2.1 ++ before := by
  obtain ⟨steps, node, before, bound, found, active, zero, same, output, exactPrefix, _⟩ :=
    State.drainReadyGroups_go_success_boundary_withCancellation fuel queue available selected
  exact ⟨steps, node, before, bound, found, active, zero, same, output, exactPrefix⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
