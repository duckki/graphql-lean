import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceTaskIdentity
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceCursorOrigins

/-! The source inventory contains exactly the scheduler's structural task occurrences. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths

/-- Every label in a stream inventory belongs to a specific item or its child subtree.
Witness: list membership induction preserves the selected entry and both item offsets.
-/
theorem sourceItemTasks_member {address producer node index ordinal items task}
    (member : task ∈ sourceItemTasks address producer node index ordinal items)
    : ∃ offset result children,
        items[offset]? = some (result, children)
        ∧ let item : SourceTask :=
            ⟨
              .item address (ordinal + offset),
              producer,
              .item node result,
              index + offset
            ⟩
          task = item
          ∨ task
            ∈ sourceTasks (address ++ [ordinal + offset])
                (some item.occurrence) item.cursors children := by
  induction items generalizing index ordinal with
  | nil => simp [sourceItemTasks] at member
  | cons head rest ih =>
      rcases head with ⟨result, children⟩
      rw [sourceItemTasks] at member
      rcases List.mem_cons.mp member with same | member
      · exact ⟨0, result, children, rfl, Or.inl (by simpa using same)⟩
      · rcases List.mem_append.mp member with member | member
        · exact ⟨0, result, children, rfl, Or.inr (by simpa using member)⟩
        · obtain ⟨offset, result, children, entry, selected⟩ := ih member
          refine ⟨offset + 1, result, children, entry, ?_⟩
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using selected

/-- Every source label describes a real scheduler task with exactly its stored producer
and payload. Witness: structural task lookup, recursively preserving absolute addresses.
-/
theorem sourceTasks_known {root address work producer owners}
    (located : Located root address work producer owners)
    (cursors : ResponsePositions.Cursors) {task}
    (member : task ∈ sourceTasks address producer cursors work)
    : ∃ taskOwners,
        TaskAt root task.occurrence taskOwners task.producer task.payload := by
  cases work with
  | empty => simp [sourceTasks] at member
  | append left right =>
      rw [sourceTasks] at member
      rcases List.mem_append.mp member with member | member
      · exact sourceTasks_known (.left located) cursors member
      · exact sourceTasks_known (.right located) cursors member
  | deferred groups path result children =>
      rw [sourceTasks] at member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, .deferred located⟩
      · exact sourceTasks_known (.deferred located) _ member
  | stream node items =>
      obtain ⟨offset, result, children, entry, selected⟩ := sourceItemTasks_member member
      simp only [Nat.zero_add] at selected
      rcases selected with rfl | selected
      · exact ⟨_, .item located entry⟩
      · have smaller := List.sizeOf_lt_of_mem (List.mem_of_getElem? entry)
        exact sourceTasks_known (.item located entry) _ selected
termination_by sizeOf work
decreasing_by all_goals simp_all; omega

/-- A source label's seed witness is independent of which lookup proof recovers it.
Witness: scheduler provenance followed by functional occurrence lookup in the inventory.
-/
theorem sourceTasks_seeded {cursors work slices task}
    (seeded : WorkCursorSeed cursors work slices)
    (member : task ∈ sourceTasks [] none cursors work)
    : task.Seeded cursors (sourceTasks [] none cursors work) := by
  obtain ⟨owners, known⟩ := sourceTasks_known .root cursors member
  obtain ⟨other, otherMember, same, _, _, seed⟩ := sourceTasks_task_seeded seeded known
  have equal := sourceTasks_same otherMember member same
  simpa only [equal] using seed

/-- Every published task identifies exactly one source label, including equal-valued
items. Witness: publication provenance, total source lookup, and occurrence uniqueness.
-/
theorem Explains.published_sourceTask {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {occurrence} (published : Published matching events occurrence)
    (cursors : ResponsePositions.Cursors)
    : ∃ task,
        (task ∈ sourceTasks [] none cursors work ∧ task.occurrence = occurrence)
        ∧ ∀ other,
            other ∈ sourceTasks [] none cursors work
            → other.occurrence = occurrence
            → other = task := by
  obtain ⟨_, _, _, known, _⟩ := explained.published_task published
  obtain ⟨task, member, same, _, _⟩ := sourceTasks_task known cursors
  exact ⟨task, ⟨member, same⟩, fun other otherMember equal =>
    sourceTasks_same otherMember member (equal.trans same.symm)⟩

end GraphQL.IncrementalDelivery.Correctness
