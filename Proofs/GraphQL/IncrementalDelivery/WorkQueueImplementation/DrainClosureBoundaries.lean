import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainValueCoverage

/-! Indexed successful drain outputs identify their exact executable closure boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

-----------------------------------------------------------------------------------------
-- Invert a selected ready group and the final carrier of its successful flush
-----------------------------------------------------------------------------------------

/-- The drain's selected record is live and active, with a cached failure or zero pending.
Witness: invert the actual root-key search and its successful group lookup.
-/
private theorem ready_group {queue : State} {group : GroupNode}
    (selected
      : queue.rootGroups.findSome?
          (fun key => do
            let node ← queue.groupNode? key
            if node.failure.isSome || node.pending == 0 then some node else none)
        = some group)
    : queue.groupNode? group.group.node.key = some group
      ∧ group.group.node.key ∈ queue.rootGroups
      ∧ (group.failure.isSome = true ∨ group.pending = 0) := by
  obtain ⟨key, active, choice⟩ := List.exists_of_findSome?_eq_some selected
  cases found : queue.groupNode? key with
  | none => simp [found] at choice
  | some node =>
      simp only [found] at choice
      change (if node.failure.isSome || node.pending == 0 then some node else none) = some group
        at choice
      split at choice
      · rename_i ready
        obtain rfl := Option.some.inj choice
        have same := State.groupNode?_key found
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
        obtain ⟨rfl, rfl, rfl⟩ := Execution.WorkQueueEvent.groupSuccess.inj (Option.some.inj selected)
        exact ⟨[], rfl, rfl, rfl⟩
    | succ index => simp at selected
  · simp only [empty] at selected ⊢
    cases index with
    | zero => cases selected
    | succ index =>
        cases index with
        | zero =>
            obtain ⟨rfl, rfl, rfl⟩ := Execution.WorkQueueEvent.groupSuccess.inj (Option.some.inj selected)
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
Witness: follow the actual closure blocks to its live, active, uncached zero-pending
group. The recovered prefix excludes the selected value block itself.
-/
theorem State.drainReadyGroups_go_value_boundary (fuel : Nat) (queue : State)
    {index group values}
    (selected
      : (State.drainReadyGroups.go fuel queue).2[index]?
        = some (.groupValues group values))
    : ∃ steps node,
        steps < fuel
        ∧ (State.drainReadyGroups.go steps queue).1.groupNode? node.group.node.key
          = some node
        ∧ node.group.node.key ∈ (State.drainReadyGroups.go steps queue).1.rootGroups
        ∧ node.failure = none
        ∧ node.pending = 0
        ∧ node.group.node = group
        ∧ (State.drainReadyGroups.go fuel queue).2.take index
          = (State.drainReadyGroups.go steps queue).2 := by
  induction fuel generalizing queue index with
  | zero => simp [State.drainReadyGroups.go] at selected
  | succ fuel ih =>
      cases ready
            : queue.rootGroups.findSome?
                (fun key => do
                  let node ← queue.groupNode? key
                  if node.failure.isSome || node.pending == 0 then
                    some node
                  else
                    none) with
      | none =>
          simp only [State.drainReadyGroups.go, ready, List.getElem?_nil] at selected
          contradiction
      | some node =>
          obtain ⟨found, active, condition⟩ := ready_group ready
          cases cached : node.failure with
          | none =>
              let next := (queue.finishGroupSuccess node).1.startNewWork
                (queue.finishGroupSuccess node).2.2
              let emitted := (queue.finishGroupSuccess node).2.1
              have step (count : Nat) : State.drainReadyGroups.go (count + 1) queue =
                  ((State.drainReadyGroups.go count next).1,
                    emitted ++ (State.drainReadyGroups.go count next).2) := by
                simp only [State.drainReadyGroups.go, ready, cached]
                rfl
              rw [step fuel] at selected
              by_cases inside : index < emitted.length
              · have atFlush := selected
                rw [List.getElem?_append_left inside] at atFlush
                obtain ⟨rfl, same⟩ := queue.finishGroupSuccess_value_index node atFlush
                exact ⟨0, node, by omega, found, active, cached,
                  by simpa [cached] using condition, same, by simp [State.drainReadyGroups.go]⟩
              · have outside : emitted.length ≤ index := by omega
                rw [List.getElem?_append_right outside] at selected
                obtain ⟨steps, later, bound, lookup, root, healthy, zero, same,
                  exactPrefix⟩ := ih next selected
                refine ⟨steps + 1, later, by omega, ?_, ?_, healthy, zero, same, ?_⟩
                · simpa only [step] using lookup
                · simpa only [step] using root
                · rw [step fuel, List.take_append, List.take_of_length_le outside,
                    exactPrefix, step]
          | some errors =>
              let next := (queue.finishGroupFailure node errors).1
              have step (count : Nat) : State.drainReadyGroups.go (count + 1) queue =
                  ((State.drainReadyGroups.go count next).1,
                    [.groupFailure node.group.node errors]
                      ++ (State.drainReadyGroups.go count next).2) := by
                simp only [State.drainReadyGroups.go, ready, cached]
                rfl
              rw [step fuel] at selected
              simp only [List.singleton_append] at selected
              cases index with
              | zero => cases selected
              | succ index =>
                  obtain ⟨steps, later, bound, lookup, root, healthy, zero, same,
                    exactPrefix⟩ := ih next selected
                  refine ⟨steps + 1, later, by omega, ?_, ?_, healthy, zero, same, ?_⟩
                  · simpa only [step] using lookup
                  · simpa only [step] using root
                  · simp only [step, List.cons_append, List.nil_append,
                      List.take_succ_cons, exactPrefix]

/-- Every indexed successful drain carrier has a concrete earlier drain boundary.
Witness: recurse through actual closure blocks, retaining silent prefixes and exact output
offsets. The recovered group is live, active, uncached, and zero-pending; its value prefix
ends exactly at the selected output position. Equal-looking raw carriers are not merged.
-/
theorem State.drainReadyGroups_go_success_boundary (fuel : Nat) (queue : State)
    {index group groups streams}
    (selected
      : (State.drainReadyGroups.go fuel queue).2[index]?
        = some (.groupSuccess group groups streams))
    : ∃ steps node before,
        steps < fuel
        ∧ (State.drainReadyGroups.go steps queue).1.groupNode? node.group.node.key
          = some node
        ∧ node.group.node.key ∈ (State.drainReadyGroups.go steps queue).1.rootGroups
        ∧ node.failure = none
        ∧ node.pending = 0
        ∧ node.group.node = group
        ∧ ((State.drainReadyGroups.go steps queue).1.finishGroupSuccess node).2.1
          = before ++ [.groupSuccess group groups streams]
        ∧ (State.drainReadyGroups.go fuel queue).2.take index
          = (State.drainReadyGroups.go steps queue).2 ++ before := by
  induction fuel generalizing queue index with
  | zero => simp [State.drainReadyGroups.go] at selected
  | succ fuel ih =>
      cases ready
            : queue.rootGroups.findSome?
                (fun key => do
                  let node ← queue.groupNode? key
                  if node.failure.isSome || node.pending == 0 then
                    some node
                  else
                    none) with
      | none =>
          simp only [State.drainReadyGroups.go, ready, List.getElem?_nil] at selected
          contradiction
      | some node =>
          obtain ⟨found, active, condition⟩ := ready_group ready
          cases cached : node.failure with
          | none =>
              let next := (queue.finishGroupSuccess node).1.startNewWork
                (queue.finishGroupSuccess node).2.2
              let emitted := (queue.finishGroupSuccess node).2.1
              have step (count : Nat) : State.drainReadyGroups.go (count + 1) queue =
                  ((State.drainReadyGroups.go count next).1,
                    emitted ++ (State.drainReadyGroups.go count next).2) := by
                simp only [State.drainReadyGroups.go, ready, cached]
                rfl
              rw [step fuel] at selected
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
                  found,
                  active,
                  cached,
                  ?_,
                  same,
                  output,
                  ?_
                ⟩
                · simpa [cached] using condition
                · rw [step fuel]
                  simpa only [List.take_append_of_le_length (Nat.le_of_lt inside),
                    State.drainReadyGroups.go, List.nil_append] using exactPrefix
              · have outside : emitted.length ≤ index := by omega
                rw [List.getElem?_append_right outside] at selected
                obtain ⟨steps, later, before, bound, lookup, root, healthy, zero, same, output,
                  exactPrefix⟩ :=
                  ih next selected
                refine ⟨
                  steps + 1,
                  later,
                  before,
                  by omega,
                  ?_,
                  ?_,
                  healthy,
                  zero,
                  same,
                  ?_,
                  ?_
                ⟩
                · simpa only [step] using lookup
                · simpa only [step] using root
                · simpa only [step] using output
                · rw [step fuel, List.take_append, List.take_of_length_le outside,
                    exactPrefix, step]
                  simp only [List.append_assoc]
          | some errors =>
              let next := (queue.finishGroupFailure node errors).1
              have step (count : Nat) : State.drainReadyGroups.go (count + 1) queue =
                  ((State.drainReadyGroups.go count next).1,
                    [.groupFailure node.group.node errors]
                      ++ (State.drainReadyGroups.go count next).2) := by
                simp only [State.drainReadyGroups.go, ready, cached]
                rfl
              rw [step fuel] at selected
              simp only [List.singleton_append] at selected
              cases index with
              | zero => cases selected
              | succ index =>
                  obtain ⟨steps, later, before, bound, lookup, root, healthy, zero, same, output,
                    exactPrefix⟩ := ih next selected
                  refine ⟨
                    steps + 1,
                    later,
                    before,
                    by omega,
                    ?_,
                    ?_,
                    healthy,
                    zero,
                    same,
                    ?_,
                    ?_
                  ⟩
                  · simpa only [step] using lookup
                  · simpa only [step] using root
                  · simpa only [step] using output
                  · simp only [step, List.cons_append, List.nil_append,
                      List.take_succ_cons, exactPrefix]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
