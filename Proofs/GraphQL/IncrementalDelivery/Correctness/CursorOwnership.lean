import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceTaskAccounting

/-! Source disjointness identifies the unique payload that creates each list cursor. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths

/-- A list path has one seed origin and one starting cursor across the source inventory.
Witness: initial/task position disjointness excludes two introducing payloads; functional
source lookup identifies repeated references to the same producer.
-/
theorem CursorOrigin.lookup_unique {initial : ResponsePositions.Cursors} {work positions}
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    {left right before after path first second}
    (leftOrigin : CursorOrigin initial (sourceTasks [] none initial work) left before)
    (rightOrigin : CursorOrigin initial (sourceTasks [] none initial work) right after)
    (leftCursor : ResponsePositions.cursorAt before path = some first)
    (rightCursor : ResponsePositions.cursorAt after path = some second)
    : left = right ∧ before = after ∧ first = second := by
  obtain ⟨_, futureUnique, initialApart⟩ := List.nodup_append.mp disjoint
  cases left with
  | none =>
      change before = initial at leftOrigin
      subst before
      cases right with
      | none =>
          change after = initial at rightOrigin
          subst after
          exact ⟨rfl, rfl, Option.some.inj (leftCursor.symm.trans rightCursor)⟩
      | some parent =>
          obtain ⟨task, member, same, rfl⟩ := rightOrigin
          exact False.elim (initialApart path (initialHistory.lookup leftCursor) path
            (List.mem_flatMap.mpr ⟨task, member, task.cursorHistory.lookup rightCursor⟩) rfl)
  | some parent =>
      obtain ⟨task, member, same, rfl⟩ := leftOrigin
      cases right with
      | none =>
          change after = initial at rightOrigin
          subst after
          exact False.elim (initialApart path (initialHistory.lookup rightCursor) path
            (List.mem_flatMap.mpr ⟨task, member, task.cursorHistory.lookup leftCursor⟩) rfl)
      | some other =>
          obtain ⟨next, nextMember, nextSame, rfl⟩ := rightOrigin
          by_cases equal : parent = other
          · have taskEqual := sourceTasks_same member nextMember
              (same.trans (equal.trans nextSame.symm))
            subst next
            exact ⟨congrArg some equal, rfl,
              Option.some.inj (leftCursor.symm.trans rightCursor)⟩
          · exact False.elim (sourceTask_positions_disjoint futureUnique member nextMember
              (fun equalTasks => equal (same.symm.trans (equalTasks.trans nextSame)))
              (task.cursorHistory.lookup leftCursor) (next.cursorHistory.lookup rightCursor))

/-- A payload other than a list's creator cannot introduce a cursor at that list path.
Witness: every payload cursor names one of its own source positions, which are disjoint
from the creator's positions. This does not concern stream advancement of an existing
cursor, which is handled separately.
-/
theorem CursorOrigin.no_other_introduction {initial : ResponsePositions.Cursors}
    {work positions} (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    {producer seed path index task}
    (origin : CursorOrigin initial (sourceTasks [] none initial work) producer seed)
    (cursor : ResponsePositions.cursorAt seed path = some index)
    (member : task ∈ sourceTasks [] none initial work)
    (different : producer ≠ some task.occurrence)
    : ∀ entry ∈ task.cursors, entry.1 ≠ path := by
  obtain ⟨_, futureUnique, initialApart⟩ := List.nodup_append.mp disjoint
  intro entry entryMember equal
  have introduced : path ∈ task.positions true := equal ▸ task.cursorHistory entry entryMember
  cases producer with
  | none =>
      change seed = initial at origin
      subst seed
      exact initialApart path (initialHistory.lookup cursor) path
        (List.mem_flatMap.mpr ⟨task, member, introduced⟩) rfl
  | some parent =>
      obtain ⟨creator, creatorMember, same, rfl⟩ := origin
      exact sourceTask_positions_disjoint futureUnique creatorMember member
        (fun equal => different (congrArg some (same.symm.trans equal)))
        (creator.cursorHistory.lookup cursor) introduced

/-- Publishing an unrelated payload preserves this already-observed list cursor.
Witness: no other payload introduces its path, so prepending its cursors cannot shadow it.
-/
theorem CursorOrigin.preserve_cursor {initial : ResponsePositions.Cursors}
    {work positions} (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    {producer seed path start task current}
    (origin : CursorOrigin initial (sourceTasks [] none initial work) producer seed)
    (cursor : ResponsePositions.cursorAt seed path = some start)
    (member : task ∈ sourceTasks [] none initial work)
    (different : producer ≠ some task.occurrence)
    : ResponsePositions.cursorAt (task.cursors ++ current) path
      = ResponsePositions.cursorAt current path :=
  cursorAt_prepend
    (origin.no_other_introduction initialHistory disjoint cursor member different)

end GraphQL.IncrementalDelivery.Correctness
