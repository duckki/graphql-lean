import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceTaskProvenance

/-! Every stream offset originates in initial data or the task that creates its list. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths
open scoped List

/-- A seed cursor list comes from initial data or the indicated producer's payload.
The inventory is the proof-only source labelling, not a runtime queue or future trace.
-/
def CursorOrigin (initial : ResponsePositions.Cursors) (tasks : List SourceTask)
    (producer : Option Occurrence) (cursors : ResponsePositions.Cursors)
    : Prop :=
  match producer with
  | none => cursors = initial
  | some parent => ∃ task ∈ tasks, task.occurrence = parent ∧ cursors = task.cursors

/-- An indexed stream child's seed uses its absolute source index. Witness: descent
through the item certificate advances the index once for each preceding item.
-/
theorem itemCursorSeed_entry {path index items slices}
    (seeded : ItemCursorSeed path index items slices)
    {offset result children} (entry : items[offset]? = some (result, children))
    : ∃ childSlices,
        WorkCursorSeed
          (resultCursors
            (ResponsePositions.listCursors (path ++ [.index (index + offset)])) result)
          children childSlices := by
  induction offset generalizing index items slices with
  | zero =>
      cases seeded with
      | nil => simp at entry
      | cons child rest =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at entry
          obtain ⟨rfl, rfl⟩ := entry
          exact ⟨_, by simpa using child⟩
  | succ offset ih =>
      cases seeded with
      | nil => simp at entry
      | cons child rest =>
          obtain ⟨childSlices, childSeed⟩ := ih rest entry
          exact ⟨
            childSlices,
            by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using childSeed
          ⟩

/-- Located work retains both its source-position certificate and the exact origin of
its seed cursors. Witness: structural navigation; a producer transition uses only that
producer's payload, while append edges retain the current seed.
-/
theorem sourceTasks_located_seeded {work address current producer owners cursors slices}
    (seeded : WorkCursorSeed cursors work slices)
    (located : Located work address current producer owners)
    : ∃ localCursors localSlices,
        WorkCursorSeed localCursors current localSlices
        ∧ sourceTasks address producer localCursors current
          <+ sourceTasks [] none cursors work
        ∧ CursorOrigin cursors (sourceTasks [] none cursors work) producer
            localCursors := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact ⟨cursors, slices, seeded, .refl _, rfl⟩
  | left _ ih =>
      obtain ⟨localCursors, _, seed, included, origin⟩ := ih
      cases seed with
      | combine left right =>
          rw [sourceTasks] at included
          exact ⟨localCursors, _, left,
            (List.sublist_append_left _ _).trans included, origin⟩
  | right _ ih =>
      obtain ⟨localCursors, _, seed, included, origin⟩ := ih
      cases seed with
      | combine left right =>
          rw [sourceTasks] at included
          exact ⟨localCursors, _, right,
            (List.sublist_append_right _ _).trans included, origin⟩
  | @executionGroup address groups path result children producer owners located ih =>
      obtain ⟨localCursors, _, seed, included, origin⟩ := ih
      cases seed with
      | executionGroup child =>
          rw [sourceTasks] at included
          refine ⟨_, _, child, (List.sublist_cons_self _ _).trans included, ?_⟩
          exact ⟨⟨.executionGroup address, producer, .object path result, 0⟩,
            included.subset List.mem_cons_self, rfl, rfl⟩
  | @item address node items producer owners index result children located entry ih =>
      obtain ⟨localCursors, _, seed, included, origin⟩ := ih
      cases seed with
      | @stream _ _ _ start _ cursor itemsSeed =>
          rw [sourceTasks, cursor, Option.getD_some] at included
          obtain ⟨member, child⟩ := sourceItemTasks_entry entry address producer node start 0
          simp only [Nat.zero_add] at member child
          obtain ⟨childSlices, childSeed⟩ := itemCursorSeed_entry itemsSeed entry
          exact ⟨_, childSlices, childSeed, child.trans included,
            ⟨_, included.subset member, rfl, rfl⟩⟩

/-- An item label's response index is its producer-seeded start plus its task ordinal.
Object labels do not consume a stream cursor.
-/
def SourceTask.Seeded (initial : ResponsePositions.Cursors) (tasks : List SourceTask)
    (task : SourceTask)
    : Prop :=
  match task.occurrence, task.payload with
  | .item _ ordinal, .item node _ =>
      ∃ cursors start,
        CursorOrigin initial tasks task.producer cursors
        ∧ ResponsePositions.cursorAt cursors node.path = some start
        ∧ task.index = start + ordinal
  | .executionGroup _, .object .. => True
  | _, _ => False

/-- Every actual task has a label with the correct payload, producer, and source cursor
origin. Witness: the strengthened location certificate and stream entry lookup.
-/
theorem sourceTasks_task_seeded {work occurrence owners producer payload cursors slices}
    (seeded : WorkCursorSeed cursors work slices)
    (known : TaskAt work occurrence owners producer payload)
    : ∃ task ∈ sourceTasks [] none cursors work,
        task.occurrence = occurrence
        ∧ task.producer = producer
        ∧ task.payload = payload
        ∧ task.Seeded cursors (sourceTasks [] none cursors work) := by
  cases StructuralEquivalence.taskAt_of_current known with
  | @executionGroup address groups path result children producer owners located =>
      obtain ⟨_, _, _, included, _⟩ :=
        sourceTasks_located_seeded seeded located.toCurrent
      rw [sourceTasks] at included
      exact ⟨⟨.executionGroup address, producer, .object path result, 0⟩,
        included.subset List.mem_cons_self, rfl, rfl, rfl, trivial⟩
  | @item address node items producer owners index result children located entry =>
      obtain ⟨localCursors, _, seed, included, origin⟩ :=
        sourceTasks_located_seeded seeded located.toCurrent
      cases seed with
      | @stream _ _ _ start _ cursor itemsSeed =>
          rw [sourceTasks, cursor, Option.getD_some] at included
          have member := (sourceItemTasks_entry entry address producer node start 0).1
          simp only [Nat.zero_add] at member
          exact ⟨_, included.subset member, rfl, rfl, rfl,
            localCursors, start, origin, cursor, rfl⟩

/-- Every introduced cursor belongs to a position introduced by that same payload.
Witness: the recursive list/field cursor projection lemmas, including caught nulls.
-/
theorem SourceTask.cursorHistory (task : SourceTask)
    : CursorHistory task.cursors (task.positions true) := by
  rcases task with ⟨occurrence, producer, payload, index⟩
  cases payload with
  | object path result =>
      cases result with
      | error errors => simp [SourceTask.cursors, SourceTask.positions, resultCursors,
          DeliveryPaths.result, CursorHistory]
      | ok pair =>
          simpa only [SourceTask.cursors, SourceTask.positions, resultCursors,
            DeliveryPaths.result, source_fields_eq_positions]
            using fieldCursors_positions path pair.1
  | item node result =>
      cases result with
      | error errors => simp [SourceTask.cursors, SourceTask.positions, resultCursors,
          DeliveryPaths.result, CursorHistory]
      | ok pair =>
          simpa only [SourceTask.cursors, SourceTask.positions, resultCursors,
            DeliveryPaths.result, source_value_eq_positions]
            using listCursors_positions (node.path ++ [.index index]) pair.1

end GraphQL.IncrementalDelivery.Correctness
