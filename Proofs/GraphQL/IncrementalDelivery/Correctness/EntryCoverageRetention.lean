import Proofs.GraphQL.IncrementalDelivery.Correctness.EntryCoverageAssembly

/-! Typed failure coverage survives retaining completed fields and streamed items as work. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A retained execution group exposes its fields and preserves child failures
-----------------------------------------------------------------------------------------

/-- A successful group's source inventory is exactly its local prepared field inventory.
Witness: the group's own payload supplies initial fields, and its children receive those
payload cursors. This is independent of the enclosing response's cursor environment.
-/
theorem sourcePositions_executionGroup_ok (containers : Bool)
    (cursors : ResponsePositions.Cursors) (groups : List DeferredFragment)
    (path : ResponsePath) (initial : List (Name × ResponseValue)) (errors : Nat)
    (children : Work) {cause : Option Nat}
    : (sourceTasks [] none cursors
        (.executionGroup groups path { result := .ok (initial, errors), cause }
          children)).flatMap
        (SourceTask.positions containers)
      = preparedFieldPositions containers path initial children := by
  simp only [sourceTasks, List.flatMap_cons, SourceTask.positions, SourceTask.cursors,
    TaskOutcome.deliveryResult, DeliveryPaths.result, Semantics.MixedPaths.resultCursors, preparedFieldPositions,
    List.nil_append]
  rw [sourceTasks_positions_relabel containers children
    (ResponsePositions.fieldCursors path initial) [0] [] (some (.executionGroup [])) none]

/-- Retaining work beneath an execution group preserves its typed failure explanation.
Witness: payload-preserving structural embedding at the group's child edge.
-/
theorem EntryExplained.executionGroup_child {available children entry}
    (explained : EntryExplained available children entry) (groups : List DeferredFragment)
    (path : ResponsePath) (result : TaskOutcome (List (Name × ResponseValue)))
    : EntryExplained available (.executionGroup groups path result children) entry := by
  rcases explained with delivered | failed
  · exact Or.inl delivered
  · obtain ⟨occurrence, owners, producer, payload, known, fails, related⟩ := failed
    obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_located known
      (StructuralEquivalence.Located.executionGroup .root).toCurrent
    exact Or.inr ⟨occurrence, owners, producer, payload, embedded, fails, related⟩

/-- Coverage inside successful deferred fields survives their retention as one group.
Witness: the exact group inventory plus child-task embedding. Counted errors, nullable
reference values, and failed descendant tasks are all allowed; no delivery is assumed.
-/
theorem EntriesCovered.executionGroup {containers reference path children}
    (initial : List (Name × ResponseValue)) (errors : Nat) {cause : Option Nat}
    (covered
      : EntriesCovered containers reference
          (preparedFieldPositions containers path initial children) children)
    (groups : List DeferredFragment) (cursors : ResponsePositions.Cursors)
    : EntriesCovered containers reference
        ((sourceTasks [] none cursors
            (.executionGroup groups path { result := .ok (initial, errors), cause }
              children)).flatMap
          (SourceTask.positions containers))
        (.executionGroup groups path { result := .ok (initial, errors), cause }
          children) := by
  rw [sourcePositions_executionGroup_ok]
  intro entry member visible
  exact (covered entry member visible).executionGroup_child groups path { result := .ok (initial, errors), cause }

-----------------------------------------------------------------------------------------
-- Deferred work partitions combine at the same ambient cursor environment
-----------------------------------------------------------------------------------------

/-- Covered retained partitions combine without inventing an initial response slice.
Witness: canonical source-position concatenation and actual failure-task embeddings. Both
partitions use the same ambient cursors, as when collecting deferred execution groups.
-/
theorem EntriesCovered.combine_sources
    {containers leftReference rightReference cursors left right}
    (leftCovered
      : EntriesCovered containers leftReference
          ((sourceTasks [] none cursors left).flatMap (SourceTask.positions containers))
          left)
    (rightCovered
      : EntriesCovered containers rightReference
          ((sourceTasks [] none cursors right).flatMap (SourceTask.positions containers))
          right)
    : EntriesCovered containers (leftReference ++ rightReference)
        ((sourceTasks [] none cursors (.combine left right)).flatMap
          (SourceTask.positions containers)) (.combine left right) := by
  rw [sourcePositions_combine]
  apply EntriesCovered.append_iff.mpr
  exact ⟨(leftCovered.combine_left right).available_mono
      (fun _ member => List.mem_append_left _ member),
    (rightCovered.combine_right left).available_mono
      (fun _ member => List.mem_append_right _ member)⟩

-----------------------------------------------------------------------------------------
-- Every actual retained stream item keeps its value and its payload-seeded child work
-----------------------------------------------------------------------------------------

/-- A successful retained item's available positions occur in the actual source inventory.
Witness: item-list descent to its structural ordinal, keeping the absolute starting index
and that payload's child cursors. Other items may succeed or fail and are not inspected.
-/
theorem preparedValuePositions_in_sourceItems (containers : Bool)
    (address : Address) (producer : Option Occurrence) (node : DeliveryNode)
    (index ordinal : Nat) (items : List (TaskOutcome ResponseValue × Work)) (offset : Nat)
    (initial : ResponseValue) (errors : Nat) (children : Work) {cause : Option Nat}
    (found : items[offset]? = some ({ result := .ok (initial, errors), cause }, children))
    : (preparedValuePositions containers (node.path ++ [.index (index + offset)])
        initial children).Subset
        ((sourceItemTasks address producer node index ordinal items).flatMap
          (SourceTask.positions containers)) := by
  induction items generalizing offset index ordinal with
  | nil => simp at found
  | cons head tail ih =>
      cases offset with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst head
          simp only [sourceItemTasks, List.flatMap_cons, List.flatMap_append,
            SourceTask.positions, SourceTask.cursors, Semantics.MixedPaths.resultCursors,
            TaskOutcome.deliveryResult, DeliveryPaths.result, preparedValuePositions, Nat.add_zero]
          rw [sourceTasks_positions_relabel containers children
            (ResponsePositions.listCursors (node.path ++ [ResponsePathSegment.index index])
              initial)
            (address ++ [ordinal]) [] (some (.item address ordinal)) none]
          intro position member
          simp only [List.mem_append] at member ⊢
          rcases member with initial | future
          · exact Or.inl initial
          · exact Or.inr (Or.inl future)
      | succ offset =>
          simp only [List.getElem?_cons_succ] at found
          have included := ih (index + 1) (ordinal + 1) offset found
          have indices : index + 1 + offset = index + offset.succ := by omega
          rw [indices] at included
          intro position member
          have present := included member
          simp only [sourceItemTasks, List.flatMap_cons, List.flatMap_append,
            List.mem_append]
          exact Or.inr (Or.inr present)

/-- A stream cursor connects a retained item's absolute positions to the enclosing work.
Witness: the actual successful cursor lookup and its source-item membership certificate.
No default-to-zero cursor or stream timing assumption is used.
-/
theorem preparedValuePositions_in_stream
    {containers cursors node index items offset initial errors children cause}
    (cursor : ResponsePositions.cursorAt cursors node.path = some index)
    (found : items[offset]? = some ({ result := .ok (initial, errors), cause }, children))
    : (preparedValuePositions containers (node.path ++ [.index (index + offset)])
        initial children).Subset
        ((sourceTasks [] none cursors (.stream node items)).flatMap
          (SourceTask.positions containers)) := by
  simp only [sourceTasks, cursor, Option.getD_some]
  exact preparedValuePositions_in_sourceItems containers [] none node index 0 items offset
    initial errors children found

/-- Retaining a child's work beneath an actual stream item preserves its failure payload.
Witness: structural embedding at the found item ordinal; the failure attachment and typed
null ancestry are unchanged, independently of preceding items' outcomes.
-/
theorem EntryExplained.streamItem_child {available children entry}
    (explained : EntryExplained available children entry) (node : DeliveryNode)
    (items : List (TaskOutcome ResponseValue × Work)) (offset : Nat)
    (result : TaskOutcome ResponseValue)
    (found : items[offset]? = some (result, children))
    : EntryExplained available (.stream node items) entry := by
  rcases explained with delivered | failed
  · exact Or.inl delivered
  · obtain ⟨occurrence, owners, producer, payload, known, fails, related⟩ := failed
    obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_located known
      (StructuralEquivalence.Located.item .root found).toCurrent
    exact Or.inr ⟨occurrence, owners, producer, payload, embedded, fails, related⟩

/-- A covered successful retained item stays covered inside the stream's actual work.
Witness: absolute-index source inclusion and child-failure embedding at the same actual
item. The item may contain counted errors or partial data; no zero-error premise is used.
-/
theorem EntriesCovered.streamItem
    {containers reference cursors node index items offset initial errors children cause}
    (covered
      : EntriesCovered containers reference
          (preparedValuePositions containers (node.path ++ [.index (index + offset)])
            initial children) children)
    (cursor : ResponsePositions.cursorAt cursors node.path = some index)
    (found : items[offset]? = some ({ result := .ok (initial, errors), cause }, children))
    : EntriesCovered containers reference
        ((sourceTasks [] none cursors (.stream node items)).flatMap
          (SourceTask.positions containers)) (.stream node items) := by
  intro entry member visible
  exact ((covered entry member visible).streamItem_child node items offset
    { result := .ok (initial, errors), cause } found).available_mono
      (preparedValuePositions_in_stream cursor found)

end GraphQL.IncrementalDelivery.Correctness
