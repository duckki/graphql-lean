import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamCoordinates

/-! Cursor replay consumes supplied publications using their proved source coordinates.
No future output is selected and no correctness premise is added to scheduler admission.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics
open Semantics.MixedPaths

/-- Cursor lookup distinguishes a newest update from the older cursor history. -/
theorem cursorAt_cons (path query : ResponsePath) (index : Nat)
    (rest : ResponsePositions.Cursors)
    : ResponsePositions.cursorAt ((path, index) :: rest) query
      = if path = query then some index else ResponsePositions.cursorAt rest query := by
  by_cases same : path = query <;> simp [ResponsePositions.cursorAt, same]

mutual
  /-- Every list cursor in a value is at or below that value's attachment path. -/
  theorem listCursors_below (path : ResponsePath) (value : ResponseValue)
      {entry} (member : entry ∈ ResponsePositions.listCursors path value)
      : Below path entry.1 := by
    cases value with
    | null | scalar _ => simp [ResponsePositions.listCursors] at member
    | object fields => exact fieldCursors_below path fields member
    | list items =>
        rcases List.mem_cons.mp member with rfl | member
        · exact below_self _
        · exact itemCursors_below path 0 items member

  /-- Field cursor paths remain below their enclosing object, by value/list descent. -/
  theorem fieldCursors_below (path : ResponsePath) (fields : List (Name × ResponseValue))
      {entry} (member : entry ∈ ResponsePositions.fieldCursors path fields)
      : Below path entry.1 := by
    cases fields with
    | nil => simp [ResponsePositions.fieldCursors] at member
    | cons head rest =>
        rcases List.mem_append.mp member with member | member
        · exact below_child (listCursors_below _ head.2 member)
        · exact fieldCursors_below path rest member

  /-- Item cursor paths remain below their enclosing list, by increasing-index descent. -/
  theorem itemCursors_below (path : ResponsePath) (index : Nat)
      (items : List ResponseValue) {entry}
      (member : entry ∈ ResponsePositions.itemCursors path index items)
      : Below path entry.1 := by
    cases items with
    | nil => simp [ResponsePositions.itemCursors] at member
    | cons head rest =>
        rcases List.mem_append.mp member with member | member
        · exact below_child (listCursors_below _ head member)
        · exact itemCursors_below path (index + 1) rest member
end

/-- The cursors introduced inside an item cannot shadow its enclosing list's cursor.
Witness: every introduced list is below the item's strictly longer indexed path.
-/
theorem SourceTask.cursors_ne_stream {task : SourceTask} {node result}
    (payload : task.payload = .item node result)
    : ∀ entry ∈ task.cursors, entry.1 ≠ node.path := by
  rw [SourceTask.cursors, payload]
  cases result with
  | error _ => simp [resultCursors]
  | ok pair =>
      intro entry member
      exact below_child_ne (listCursors_below _ pair.1 member)

/-- The ghost cursor writes made by one published source task: its payload's new lists
and, for an item, the incremented cursor of its enclosing stream.
-/
def SourceTask.cursorUpdates (task : SourceTask) : ResponsePositions.Cursors :=
  match task.payload with
  | .object .. => task.cursors
  | .item node _ => (node.path, task.index + 1) :: task.cursors

/-- Publishing a payload establishes each list cursor that payload introduces. Witness:
append lookup and the fact that an item's outer stream path cannot shadow an inner list.
-/
theorem SourceTask.cursorUpdates_introduce {task : SourceTask} {path index current}
    (cursor : ResponsePositions.cursorAt task.cursors path = some index)
    : ResponsePositions.cursorAt (task.cursorUpdates ++ current) path = some index := by
  cases payload : task.payload with
  | object base result =>
      simpa only [SourceTask.cursorUpdates, payload] using cursorAt_append cursor
  | item node result =>
      have unequal : node.path ≠ path := by
        intro equal
        exact task.cursors_ne_stream payload _ (cursorAt_member cursor) equal.symm
      simp only [SourceTask.cursorUpdates, payload, List.cons_append, cursorAt_cons,
        ite_eq_right unequal]
      exact cursorAt_append cursor

/-- Publishing an item advances its list to the successor of its absolute source index.
Witness: the newest enclosing-list write is first in the cursor history.
-/
theorem SourceTask.cursorUpdates_stream {task : SourceTask} {node result current}
    (payload : task.payload = .item node result)
    : ResponsePositions.cursorAt (task.cursorUpdates ++ current) node.path
      = some (task.index + 1) := by
  simp [SourceTask.cursorUpdates, payload, cursorAt_cons]

/-- Stable source lookup recovers the unique inventory label for this occurrence.
Witness: a member rules out missing lookup and occurrence uniqueness identifies its hit.
-/
theorem sourceTasks_find {work initial task}
    (member : task ∈ sourceTasks [] none initial work)
    : (sourceTasks [] none initial work).find?
        (fun candidate => decide (candidate.occurrence = task.occurrence))
      = some task := by
  cases found
        : (sourceTasks [] none initial work).find?
            (fun candidate => decide (candidate.occurrence = task.occurrence)) with
  | none =>
      have absent := List.find?_eq_none.mp found task member
      simp at absent
  | some selected =>
      have selectedMember := List.mem_of_find?_eq_some found
      have equal : selected.occurrence = task.occurrence := by
        simpa using List.find?_some found
      exact congrArg some (sourceTasks_same selectedMember member equal)

/-- Cursor writes for one supplied output index; control events introduce no data.
The total projection's missing-label branch is excluded by publication provenance.
-/
def sourceEventCursors (tasks : List SourceTask) (matching : PublicationMatching)
    (index : Nat) (event : WorkEvent)
    : ResponsePositions.Cursors :=
  match event with
  | .groupValues .. | .streamValues .. =>
      ((tasks.find? (fun task => decide (task.occurrence = matching index))).map
        SourceTask.cursorUpdates).getD
        []
  | _ => []

/-- A value event writes exactly its matched source label's cursor contribution. -/
theorem sourceEventCursors_value {work initial matching index event task}
    (value : IsValue event) (member : task ∈ sourceTasks [] none initial work)
    (same : task.occurrence = matching index)
    : sourceEventCursors (sourceTasks [] none initial work) matching index event
      = task.cursorUpdates := by
  cases event <;> try contradiction
  all_goals simp [sourceEventCursors, ← same, sourceTasks_find member]

/-- Control events leave data cursors unchanged; inspect the event constructor. -/
theorem sourceEventCursors_control {tasks matching index event} (control : ¬IsValue event)
    : sourceEventCursors tasks matching index event = [] := by
  cases event <;> simp_all [IsValue, sourceEventCursors]

/-- Replay only the first cut supplied outputs, retaining the newest cursor writes first.
This proof projection uses source coordinates; the next lemma must justify those indices
against the cursors available before publication.
-/
def sourceHistoryCursors (tasks : List SourceTask) (matching : PublicationMatching)
    (events : List WorkEvent) (initial : ResponsePositions.Cursors)
    : Nat → ResponsePositions.Cursors
  | 0 => initial
  | cut + 1 =>
      ((events[cut]?).map (sourceEventCursors tasks matching cut)).getD []
      ++ sourceHistoryCursors tasks matching events initial cut

/-- A supplied event contributes its source cursor writes at the successor cut. -/
theorem sourceHistoryCursors_step {tasks matching events initial cut event}
    (selected : events[cut]? = some event)
    : sourceHistoryCursors tasks matching events initial (cut + 1)
      = sourceEventCursors tasks matching cut event
        ++ sourceHistoryCursors tasks matching events initial cut := by
  simp [sourceHistoryCursors, selected]

/-- A range of writes avoiding a path preserves that path's cursor lookup. Witness:
induction from the earlier cut to the later cut, with cursorAt_prepend at each step.
-/
theorem sourceHistoryCursors_preserve {tasks matching events initial path start finish}
    (ordered : start ≤ finish)
    (avoids
      : ∀ index event,
          start ≤ index
          → index < finish
          → events[index]? = some event
          → ∀ entry ∈ sourceEventCursors tasks matching index event, entry.1 ≠ path)
    : ResponsePositions.cursorAt
        (sourceHistoryCursors tasks matching events initial finish) path
      = ResponsePositions.cursorAt
          (sourceHistoryCursors tasks matching events initial start) path := by
  induction finish with
  | zero =>
      have : start = 0 := by omega
      subst start
      rfl
  | succ finish ih =>
      by_cases same : start = finish + 1
      · subst start; rfl
      have before : start ≤ finish := by omega
      have previous := ih before (fun index event lower upper selected =>
        avoids index event lower (by omega) selected)
      cases selected : events[finish]? with
      | none => simpa [sourceHistoryCursors, selected] using previous
      | some event =>
          rw [sourceHistoryCursors_step selected,
            cursorAt_prepend (avoids finish event before (by omega) selected)]
          exact previous

end GraphQL.IncrementalDelivery.Correctness
