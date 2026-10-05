import Proofs.GraphQL.IncrementalDelivery.Correctness.EntryFailureCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceCursorExtension
import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedCursorMerging

/-! Failure-aware entry coverage survives assembly of initial response containers. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics
open Semantics.MixedPaths

-----------------------------------------------------------------------------------------
-- Local inventories include initial positions and actual payload-seeded future positions
-----------------------------------------------------------------------------------------

/-- Local field positions available initially or in the attached future work.
The initial fields seed nested stream offsets; failed tasks contribute no data positions.
-/
def preparedFieldPositions (containers : Bool) (path : ResponsePath)
    (initial : List (Name × ResponseValue)) (work : Work)
    : List ResponsePath :=
  ResponsePositions.fields containers path initial
  ++ (sourceTasks [] none (ResponsePositions.fieldCursors path initial) work).flatMap
      (SourceTask.positions containers)

/-- Local value positions available initially or in its actual future work.
The same container flag applies to initial data and successful source payloads.
-/
def preparedValuePositions (containers : Bool) (path : ResponsePath)
    (initial : ResponseValue) (work : Work)
    : List ResponsePath :=
  ResponsePositions.value containers path initial
  ++ (sourceTasks [] none (ResponsePositions.listCursors path initial) work).flatMap
      (SourceTask.positions containers)

/-- Initial item positions and future work positions at the specified absolute offset.
Only nested item cursors are included here; the enclosing list is added separately.
-/
def preparedItemPositions (containers : Bool) (path : ResponsePath) (index : Nat)
    (initial : List ResponseValue) (work : Work)
    : List ResponsePath :=
  ResponsePositions.items containers path index initial
  ++ (sourceTasks [] none (ResponsePositions.itemCursors path index initial) work).flatMap
      (SourceTask.positions containers)

/-- Combining work concatenates actual source positions at the same cursor environment.
Witness: source descent and relabelling invariance; structural addresses do not move data.
-/
theorem sourcePositions_combine (containers : Bool) (cursors : ResponsePositions.Cursors)
    (left right : Work)
    : (sourceTasks [] none cursors (.combine left right)).flatMap
        (SourceTask.positions containers)
      = (sourceTasks [] none cursors left).flatMap (SourceTask.positions containers)
        ++ (sourceTasks [] none cursors right).flatMap
            (SourceTask.positions containers) := by
  simp only [sourceTasks, List.flatMap_append, List.nil_append]
  rw [sourceTasks_positions_relabel containers left cursors [0] [] none none,
    sourceTasks_positions_relabel containers right cursors [1] [] none none]

-----------------------------------------------------------------------------------------
-- Coverage is monotone in available positions and retains real failure payloads
-----------------------------------------------------------------------------------------

/-- Availability of every visible typed path suffices without any failure explanation.
Witness: filter/map membership; this applies to exact initial values and direct payloads.
-/
theorem EntriesCovered.of_visiblePaths_subset {containers reference available work}
    (included : (visibleEntryPaths containers reference).Subset available)
    : EntriesCovered containers reference available work := by
  intro entry member visible
  exact Or.inl (included (mem_visibleEntryPaths_iff.mpr ⟨entry, member, visible, rfl⟩))

/-- Enlarging the available data inventory preserves all covered reference entries.
Witness: entry-level membership monotonicity; null tags and failed tasks stay unchanged.
-/
theorem EntriesCovered.available_mono {containers reference available other work}
    (covered : EntriesCovered containers reference available work)
    (included : available.Subset other)
    : EntriesCovered containers reference other work := by
  intro entry member visible
  exact (covered entry member visible).available_mono included

/-- Adding right-hand work preserves reference coverage in the left component.
Witness: actual task embedding, not a new failure or a coverage assumption on the sibling.
-/
theorem EntriesCovered.combine_left {containers reference available work}
    (covered : EntriesCovered containers reference available work) (right : Work)
    : EntriesCovered containers reference available (.combine work right) := by
  intro entry member visible
  exact (covered entry member visible).combine_left right

/-- Adding left-hand work preserves reference coverage in the right component.
Witness: payload-preserving structural embedding; ordinary null ancestry is retained.
-/
theorem EntriesCovered.combine_right {containers reference available work}
    (covered : EntriesCovered containers reference available work) (left : Work)
    : EntriesCovered containers reference available (.combine left work) := by
  intro entry member visible
  exact (covered entry member visible).combine_right left

-----------------------------------------------------------------------------------------
-- Object-field assembly preserves both components' actual inventories
-----------------------------------------------------------------------------------------

/-- Later initial fields and work do not lose the earlier component's available positions.
Witness: right cursor extension, actual source relabelling, and list membership.
-/
theorem preparedFieldPositions_append_left {containers path leftWork leftSlices}
    (left right : List (Name × ResponseValue)) (rightWork : Work)
    (seeded
      : WorkCursorSeed (ResponsePositions.fieldCursors path left) leftWork leftSlices)
    : (preparedFieldPositions containers path left leftWork).Subset
        (preparedFieldPositions containers path (left ++ right)
          (.combine leftWork rightWork)) := by
  unfold preparedFieldPositions
  rw [responsePositions_fields_append, sourcePositions_combine]
  have same := congrArg (List.flatMap (SourceTask.positions containers))
    (sourceTasks_appendFields_left left right seeded [] none)
  rw [← same]
  intro position member
  simp only [List.mem_append] at member ⊢
  rcases member with initial | future
  · exact Or.inl (Or.inl initial)
  · exact Or.inr (Or.inl future)

/-- Earlier disjoint initial fields do not shadow the later component's stream offsets.
Witness: the seeded right inventory is unchanged by field concatenation when the assembled
initial positions are unique. Counted errors and future failures remain unrestricted.
-/
theorem preparedFieldPositions_append_right {containers path rightWork rightSlices}
    (left right : List (Name × ResponseValue)) (leftWork : Work)
    (seeded
      : WorkCursorSeed (ResponsePositions.fieldCursors path right) rightWork rightSlices)
    (unique : (ResponsePositions.fields true path (left ++ right)).Nodup)
    : (preparedFieldPositions containers path right rightWork).Subset
        (preparedFieldPositions containers path (left ++ right)
          (.combine leftWork rightWork)) := by
  unfold preparedFieldPositions
  rw [responsePositions_fields_append, sourcePositions_combine]
  have same := congrArg (List.flatMap (SourceTask.positions containers))
    (sourceTasks_appendFields_right left right seeded unique [] none)
  rw [← same]
  intro position member
  simp only [List.mem_append] at member ⊢
  rcases member with initial | future
  · exact Or.inl (Or.inr initial)
  · exact Or.inr (Or.inr future)

/-- Covered field partitions combine while retaining their actual failure explanations.
Witness: both seeded inventories embed in the assembled initial fields and combined work;
typed reference entries append independently of response order or error counts.
-/
theorem EntriesCovered.append_fields
    {containers path leftReference rightReference
      leftWork rightWork leftSlices rightSlices}
    (left right : List (Name × ResponseValue))
    (leftCovered
      : EntriesCovered containers leftReference
          (preparedFieldPositions containers path left leftWork) leftWork)
    (rightCovered
      : EntriesCovered containers rightReference
          (preparedFieldPositions containers path right rightWork) rightWork)
    (leftSeed
      : WorkCursorSeed (ResponsePositions.fieldCursors path left) leftWork leftSlices)
    (rightSeed
      : WorkCursorSeed (ResponsePositions.fieldCursors path right) rightWork rightSlices)
    (unique : (ResponsePositions.fields true path (left ++ right)).Nodup)
    : EntriesCovered containers (leftReference ++ rightReference)
        (preparedFieldPositions containers path (left ++ right)
          (.combine leftWork rightWork)) (.combine leftWork rightWork) := by
  apply EntriesCovered.append_iff.mpr
  exact ⟨(leftCovered.combine_left rightWork).available_mono
      (preparedFieldPositions_append_left left right rightWork leftSeed),
    (rightCovered.combine_right leftWork).available_mono
      (preparedFieldPositions_append_right left right leftWork rightSeed unique)⟩

-----------------------------------------------------------------------------------------
-- List-item assembly keeps absolute indices and payload-seeded child work
-----------------------------------------------------------------------------------------

/-- Concatenating initial items concatenates visible positions at the shifted offset.
Witness: item descent; the second list starts after the first list's actual item count.
-/
private theorem positions_items_append (containers : Bool) (path : ResponsePath)
    (index : Nat) (left right : List ResponseValue)
    : ResponsePositions.items containers path index (left ++ right)
      = ResponsePositions.items containers path index left
        ++ ResponsePositions.items containers path (index + left.length) right := by
  induction left generalizing index with
  | nil => simp [ResponsePositions.items]
  | cons head tail ih =>
      simp only [List.cons_append, ResponsePositions.items, ih, List.length_cons,
        List.append_assoc, Nat.add_assoc, Nat.add_comm 1]

/-- Later initial items preserve the earlier items' exact future-work inventory.
Witness: right cursor extension at the actual shifted item offset.
-/
theorem preparedItemPositions_append_left {containers path index leftWork leftSlices}
    (left right : List ResponseValue) (rightWork : Work)
    (seeded
      : WorkCursorSeed (ResponsePositions.itemCursors path index left)
          leftWork leftSlices)
    : (preparedItemPositions containers path index left leftWork).Subset
        (preparedItemPositions containers path index (left ++ right)
          (.combine leftWork rightWork)) := by
  have extended : CursorExtends (ResponsePositions.itemCursors path index left)
      (ResponsePositions.itemCursors path index (left ++ right)) := by
    rw [TypedResponse.itemCursors_append]
    exact .append_right _ _
  have same := sourceTasks_positions_cursorExtension seeded extended containers [] none
  unfold preparedItemPositions
  rw [positions_items_append, sourcePositions_combine, ← same]
  intro position member
  simp only [List.mem_append] at member ⊢
  rcases member with initial | future
  · exact Or.inl (Or.inl initial)
  · exact Or.inr (Or.inl future)

/-- Earlier unique initial items preserve the later items' nested stream offsets.
Witness: initial-position disjointness excludes cursor shadowing, then exact source
extension supplies the inventory at its unchanged absolute index.
-/
theorem preparedItemPositions_append_right {containers path index rightWork rightSlices}
    (left right : List ResponseValue) (leftWork : Work)
    (seeded
      : WorkCursorSeed (ResponsePositions.itemCursors path (index + left.length) right)
          rightWork rightSlices)
    (unique : (ResponsePositions.items true path index (left ++ right)).Nodup)
    : (preparedItemPositions containers path (index + left.length) right rightWork).Subset
        (preparedItemPositions containers path index (left ++ right)
          (.combine leftWork rightWork)) := by
  have positions : (DeliveryPaths.items true path (index + left.length) right
      ++ DeliveryPaths.items true path index left).Nodup := by
    rw [positions_items_append] at unique
    rw [← source_items_eq_positions, ← source_items_eq_positions] at unique
    exact List.perm_append_comm.nodup_iff.mp unique
  have extended := CursorExtends.of_disjoint_history
    (itemCursors_positions path (index + left.length) right)
    (itemCursors_positions path index left) positions
  rw [← TypedResponse.itemCursors_append] at extended
  have same := sourceTasks_positions_cursorExtension seeded extended containers [] none
  unfold preparedItemPositions
  rw [positions_items_append, sourcePositions_combine, ← same]
  intro position member
  simp only [List.mem_append] at member ⊢
  rcases member with initial | future
  · exact Or.inl (Or.inr initial)
  · exact Or.inr (Or.inr future)

/-- Covered item partitions combine at the actual initial prefix length.
Witness: both seeded inventories embed at their absolute offsets; failed-task payloads
survive combination. The reference entries need not be zero-error or fully delivered.
-/
theorem EntriesCovered.append_items
    {containers path index leftReference rightReference
      leftWork rightWork leftSlices rightSlices}
    (left right : List ResponseValue)
    (leftCovered
      : EntriesCovered containers leftReference
          (preparedItemPositions containers path index left leftWork) leftWork)
    (rightCovered
      : EntriesCovered containers rightReference
          (preparedItemPositions containers path (index + left.length) right rightWork)
          rightWork)
    (leftSeed
      : WorkCursorSeed (ResponsePositions.itemCursors path index left)
          leftWork leftSlices)
    (rightSeed
      : WorkCursorSeed (ResponsePositions.itemCursors path (index + left.length) right)
          rightWork rightSlices)
    (unique : (ResponsePositions.items true path index (left ++ right)).Nodup)
    : EntriesCovered containers (leftReference ++ rightReference)
        (preparedItemPositions containers path index (left ++ right)
          (.combine leftWork rightWork)) (.combine leftWork rightWork) := by
  apply EntriesCovered.append_iff.mpr
  exact ⟨(leftCovered.combine_left rightWork).available_mono
      (preparedItemPositions_append_left left right rightWork leftSeed),
    (rightCovered.combine_right leftWork).available_mono
      (preparedItemPositions_append_right left right leftWork rightSeed unique)⟩

-----------------------------------------------------------------------------------------
-- Container wrappers preserve leaf coverage and add their own optional visible entry
-----------------------------------------------------------------------------------------

/-- A field alias changes only the local value attachment, not its available inventory.
Witness: singleton field position/cursor equations; arbitrary future failures are kept.
-/
theorem preparedFieldPositions_singleton (containers : Bool) (path : ResponsePath)
    (name : Name) (initial : ResponseValue) (work : Work)
    : preparedFieldPositions containers path [(name, initial)] work
      = preparedValuePositions containers (path ++ [.field name]) initial work := by
  simp [preparedFieldPositions, preparedValuePositions, ResponsePositions.fields,
    ResponsePositions.fieldCursors]

/-- A singleton item shares its value's inventory at the same absolute list index.
Witness: singleton item position/cursor equations, including nested future work.
-/
theorem preparedItemPositions_singleton (containers : Bool) (path : ResponsePath)
    (index : Nat) (initial : ResponseValue) (work : Work)
    : preparedItemPositions containers path index [initial] work
      = preparedValuePositions containers (path ++ [.index index]) initial work := by
  simp [preparedItemPositions, preparedValuePositions, ResponsePositions.items,
    ResponsePositions.itemCursors]

/-- Wrapping initial fields in an object retains coverage and its optional container path.
Witness: the object uses exactly the same nested cursors as its fields. Its visible root
entry is supplied by the actual initial object, not by unrelated future work.
-/
theorem EntriesCovered.object {containers path work}
    (reference initial : List (Name × ResponseValue))
    (covered
      : EntriesCovered containers (TypedResponse.fields path reference)
          (preparedFieldPositions containers path initial work) work)
    : EntriesCovered containers (TypedResponse.value path (.object reference))
        (preparedValuePositions containers path (.object initial) work) work := by
  intro entry member visible
  simp only [TypedResponse.value, List.mem_cons] at member
  rcases member with rfl | member
  · have flag : containers = true := visible
    exact Or.inl (by simp [preparedValuePositions, ResponsePositions.value, flag])
  · apply (covered entry member visible).available_mono
    intro position present
    simp only [preparedFieldPositions, preparedValuePositions, ResponsePositions.value,
      ResponsePositions.listCursors, List.mem_append] at present ⊢
    rcases present with initial | future
    · exact Or.inl (Or.inr initial)
    · exact Or.inr future

/-- Wrapping assembled items in a list retains coverage and its optional container path.
Witness: seeded child-source inventory survives adding the enclosing list cursor; the
initial list itself supplies the visible root entry, including for an empty list.
-/
theorem EntriesCovered.list {containers path work slices}
    (reference initial : List ResponseValue)
    (covered
      : EntriesCovered containers (TypedResponse.items path 0 reference)
          (preparedItemPositions containers path 0 initial work) work)
    (seeded : WorkCursorSeed (ResponsePositions.itemCursors path 0 initial) work slices)
    : EntriesCovered containers (TypedResponse.value path (.list reference))
        (preparedValuePositions containers path (.list initial) work) work := by
  intro entry member visible
  simp only [TypedResponse.value, List.mem_cons] at member
  rcases member with rfl | member
  · have flag : containers = true := visible
    exact Or.inl (by simp [preparedValuePositions, ResponsePositions.value, flag])
  · apply (covered entry member visible).available_mono
    intro position present
    have same := congrArg (List.flatMap (SourceTask.positions containers))
      (sourceTasks_enclosingList initial seeded [] none)
    unfold preparedItemPositions at present
    unfold preparedValuePositions
    rw [← same]
    simp only [ResponsePositions.value, List.mem_append] at present ⊢
    rcases present with initial | future
    · exact Or.inl (Or.inr initial)
    · exact Or.inr future

end GraphQL.IncrementalDelivery.Correctness
