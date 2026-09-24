import Proofs.GraphQL.IncrementalDelivery.Correctness.AbsolutePositions
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkEventMetadata

/-! Work batching preserves the exact ordered absolute data atoms, not just their set. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

/-- Forget control notices and numeric IDs while retaining every object or item payload.
One atom is retained per streamed item, even when a WorkEvent coalesces several items.
-/
def eventPositionAtoms : WorkEvent → List PositionAtom
  | .groupValues _ values => values.map (fun value => .object value.path value.data)
  | .streamValues node values _ _ => values.map (fun value => .item node.path value.item)
  | _ => []

/-- Combining compatible events preserves their ordered absolute atoms. Witness: list
append for objects and items; coherent key paths identify the coalesced stream's path.
-/
theorem combineValues_positionAtoms {paths : Nat → ResponsePath} {left right combined}
    (leftPaths : ∀ node ∈ eventNodes left, paths node.key = node.path)
    (rightPaths : ∀ node ∈ eventNodes right, paths node.key = node.path)
    (compatible : combineValues left right = some combined)
    : eventPositionAtoms combined
      = eventPositionAtoms left ++ eventPositionAtoms right := by
  cases left <;> cases right <;> simp [combineValues] at compatible
  case groupValues.groupValues node values other more =>
    obtain ⟨_, rfl⟩ := compatible
    simp [eventPositionAtoms]
  case
    streamValues.streamValues node values groups streams other more moreGroups moreStreams
      =>
    obtain ⟨keys, rfl⟩ := compatible
    have first := leftPaths node (by simp [eventNodes])
    have second := rightPaths other (by simp [eventNodes])
    have same : node.path = other.path := first.symm.trans (keys ▸ second)
    simp [eventPositionAtoms, same]

/-- Optional value coalescing preserves all absolute data atoms in their original order.
Witness: grouping induction, retaining source descriptor paths for each intermediate head.
-/
theorem valueGrouping_positionAtoms {paths : Nat → ResponsePath} {events grouped}
    (grouping : ValueGrouping events grouped)
    (coherent : ∀ node ∈ events.flatMap eventNodes, paths node.key = node.path)
    : grouped.flatMap eventPositionAtoms = events.flatMap eventPositionAtoms := by
  induction grouping with
  | nil => rfl
  | separate head rest ih =>
      have tail := ih (fun node member => coherent node (List.mem_append_right _ member))
      simp only [List.flatMap_cons, tail]
  | @combine head tail first rest merged grouped compatible ih =>
      have tailPaths : ∀ node ∈ tail.flatMap eventNodes, paths node.key = node.path :=
        fun node member => coherent node (List.mem_append_right _ member)
      have firstPaths : ∀ node ∈ eventNodes first, paths node.key = node.path :=
        fun node member => tailPaths node
          (valueGrouping_nodes grouped node (List.mem_append_left _ member))
      have combined := combineValues_positionAtoms
        (fun node member => coherent node (List.mem_append_left _ member))
        firstPaths compatible
      simp only [List.flatMap_cons, combined, List.append_assoc]
      exact congrArg (eventPositionAtoms head ++ ·) (ih tailPaths)

/-- Nonempty work-event batching also preserves every ordered data atom. Witness:
partition induction, with the value-coalescing theorem inside each partition.
-/
theorem workBatching_positionAtoms {paths : Nat → ResponsePath} {events batches}
    (grouping : WorkBatching events batches)
    (coherent : ∀ node ∈ events.flatMap eventNodes, paths node.key = node.path)
    : batches.flatten.flatMap eventPositionAtoms = events.flatMap eventPositionAtoms := by
  induction grouping with
  | nil => rfl
  | cons _ values rest ih =>
      simp only [List.flatMap_append] at coherent
      have firstPaths := fun node member => coherent node
        (List.mem_append_left _ member)
      have tailPaths := fun node member => coherent node
        (List.mem_append_right _ member)
      simp only [List.flatten_cons, List.flatMap_append]
      rw [valueGrouping_positionAtoms values firstPaths, ih tailPaths]

/-- Admitted work batches have exactly the absolute atoms of their unbatched history;
the optional terminal marker contributes none. Witness: generated path coherence and
the checked partition/grouping law, without any chosen completion order.
-/
theorem admitted_positionAtoms {paths bound work history}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (admitted : AdmissiblePrefix work history ∨ AdmissibleRun work history)
    : ∃ events matching failures,
        Explains work history.initialGroups history.initialStreams events matching
          failures
        ∧ history.batches.flatten.flatMap eventPositionAtoms
          = events.flatMap eventPositionAtoms := by
  have nodePaths {events matching failures}
      (explained : Explains work history.initialGroups history.initialStreams events
        matching failures)
      : ∀ node ∈ events.flatMap eventNodes, paths node.key = node.path := by
    intro node member
    obtain ⟨kind, parents, birth, known⟩ := explained_nodes explained node member
    exact (workAt_node coherent known).2
  rcases admitted with ⟨events, matching, failures, explained, grouped⟩
    | ⟨events, matching, failures, explained, _, grouped⟩
  · exact ⟨events, matching, failures, explained,
      workBatching_positionAtoms grouped (nodePaths explained)⟩
  · refine ⟨events, matching, failures, explained, ?_⟩
    have paths : ∀ node ∈ (events ++ [WorkEvent.workQueueTermination]).flatMap eventNodes,
        paths node.key = node.path := by
      simpa only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, eventNodes,
        List.nil_append, List.append_nil]
        using nodePaths explained
    simpa only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      eventPositionAtoms, List.nil_append, List.append_nil]
      using workBatching_positionAtoms grouped paths

end GraphQL.IncrementalDelivery.Correctness
