import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceTasks
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.StructuralEquivalence

/-! Structural task lookup recovers the same labels used by source-position ownership. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths
open scoped List

/-- A stream entry and its child tasks occur at the corresponding labelled offsets.
Witness: list lookup induction retains both the absolute index and structural ordinal.
-/
theorem sourceItemTasks_entry {items : List (Result ResponseValue × Work)}
    {offset result children} (entry : items[offset]? = some (result, children))
    (address : Address) (producer : Option Occurrence) (node : DeliveryNode)
    (index ordinal : Nat)
    : let task : SourceTask :=
        ⟨.item address (ordinal + offset), producer, .item node result, index + offset⟩
      task ∈ sourceItemTasks address producer node index ordinal items
      ∧ sourceTasks (address ++ [ordinal + offset]) (some task.occurrence)
          task.cursors children
        <+ sourceItemTasks address producer node index ordinal items := by
  induction items generalizing offset index ordinal with
  | nil => simp at entry
  | cons head rest ih =>
      rcases head with ⟨headResult, headChildren⟩
      cases offset with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at entry
          obtain ⟨rfl, rfl⟩ := entry
          dsimp
          constructor
          · simp [sourceItemTasks]
          · exact (List.sublist_append_left _ _).cons _
      | succ offset =>
          obtain ⟨member, sublist⟩ := ih entry (index + 1) (ordinal + 1)
          dsimp at member sublist ⊢
          simp only [Nat.add_left_comm, Nat.add_comm] at member sublist ⊢
          rw [sourceItemTasks]
          constructor
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
          · exact (sublist.trans (List.sublist_append_right _ _)).cons _

/-- Located subwork keeps a contiguous source-task inventory with its own payload seeds.
Witness: follow the structural lookup, extracting the selected streamed child's sublist.
-/
theorem sourceTasks_located {work address current producer owners}
    (located : Located work address current producer owners)
    (cursors : ResponsePositions.Cursors)
    : ∃ localCursors,
        sourceTasks address producer localCursors current
        <+ sourceTasks [] none cursors work := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact ⟨cursors, .refl _⟩
  | left _ ih =>
      obtain ⟨localCursors, included⟩ := ih
      rw [sourceTasks] at included
      exact ⟨localCursors, (List.sublist_append_left _ _).trans included⟩
  | right _ ih =>
      obtain ⟨localCursors, included⟩ := ih
      rw [sourceTasks] at included
      exact ⟨localCursors, (List.sublist_append_right _ _).trans included⟩
  | executionGroup _ ih =>
      obtain ⟨_, included⟩ := ih
      rw [sourceTasks] at included
      exact ⟨_, (List.sublist_cons_self _ _).trans included⟩
  | @item address node items producer owners index result children located entry ih =>
      obtain ⟨localCursors, included⟩ := ih
      rw [sourceTasks] at included
      have child := (sourceItemTasks_entry entry address producer node
        ((ResponsePositions.cursorAt localCursors node.path).getD 0) 0).2
      simp only [Nat.zero_add] at child
      exact ⟨_, child.trans included⟩

/-- Every scheduler task has a source label with its exact occurrence, producer, and
payload. Witness: the located source inventory and, for streams, indexed entry lookup.
-/
theorem sourceTasks_task {work occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (cursors : ResponsePositions.Cursors)
    : ∃ task ∈ sourceTasks [] none cursors work,
        task.occurrence = occurrence
        ∧ task.producer = producer
        ∧ task.payload = payload := by
  cases StructuralEquivalence.taskAt_of_current known with
  | @executionGroup address groups path result children producer owners located =>
      obtain ⟨_, included⟩ := sourceTasks_located located.toCurrent cursors
      rw [sourceTasks] at included
      exact ⟨⟨.executionGroup address, producer, .object path result, 0⟩,
        included.subset (List.mem_cons_self), rfl, rfl, rfl⟩
  | @item address node items producer owners index result children located entry =>
      obtain ⟨localCursors, included⟩ := sourceTasks_located located.toCurrent cursors
      rw [sourceTasks] at included
      have member := (sourceItemTasks_entry entry address producer node
        ((ResponsePositions.cursorAt localCursors node.path).getD 0) 0).1
      simp only [Nat.zero_add] at member
      exact ⟨_, included.subset member, rfl, rfl, rfl⟩

/-- Disjoint flattened source positions separate any two distinct task labels. Witness:
list pairwise disjointness, using either relative order of the two member labels.
-/
theorem sourceTask_positions_disjoint {tasks : List SourceTask}
    (disjoint : (tasks.flatMap (SourceTask.positions true)).Nodup)
    {left right : SourceTask} (leftMember : left ∈ tasks) (rightMember : right ∈ tasks)
    (different : left.occurrence ≠ right.occurrence)
    {path : ResponsePath} (inLeft : path ∈ left.positions true)
    (inRight : path ∈ right.positions true)
    : False := by
  induction tasks with
  | nil => simp at leftMember
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.nodup_append] at disjoint
      rcases List.mem_cons.mp leftMember with equal | leftMember
      · subst left
        rcases List.mem_cons.mp rightMember with equal | rightMember
        · subst right; exact different rfl
        · exact disjoint.2.2 path inLeft path
            (List.mem_flatMap.mpr ⟨right, rightMember, inRight⟩) rfl
      · rcases List.mem_cons.mp rightMember with equal | rightMember
        · subst right
          exact disjoint.2.2 path inRight path
            (List.mem_flatMap.mpr ⟨left, leftMember, inLeft⟩) rfl
        · exact ih disjoint.2.1 leftMember rightMember

/-- Distinct value publications have disjoint source positions. Witness: task lookup,
source ownership, and the independent one-shot publication theorem. This is a source
position claim; HistoryStreamCursors and QueryDisjointness supply the wire bridge.
-/
theorem Explains.publication_source_disjoint
    {work groups streams events matching failures cursors}
    (explained : Explains work groups streams events matching failures)
    (disjoint
      : ((sourceTasks [] none cursors work).flatMap (SourceTask.positions true)).Nodup)
    {left right first second firstTask secondTask}
    (firstAt : events[left]? = some first) (firstValue : IsValue first)
    (secondAt : events[right]? = some second) (secondValue : IsValue second)
    (different : left ≠ right)
    (firstMember : firstTask ∈ sourceTasks [] none cursors work)
    (secondMember : secondTask ∈ sourceTasks [] none cursors work)
    (firstMatch : firstTask.occurrence = matching left)
    (secondMatch : secondTask.occurrence = matching right)
    {path} (inFirst : path ∈ firstTask.positions true)
    (inSecond : path ∈ secondTask.positions true)
    : False := by
  apply sourceTask_positions_disjoint disjoint firstMember secondMember _ inFirst inSecond
  intro equal
  apply different
  exact explained.publication_unique firstAt firstValue secondAt secondValue
    (firstMatch.symm.trans (equal.trans secondMatch))

end GraphQL.IncrementalDelivery.Correctness
