import Proofs.GraphQL.IncrementalDelivery.Correctness.CursorOwnership

/-! Published stream tasks share a source list only when they belong to the same stream. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths

/-- Items at one structural stream address have the same node and producer. Witness:
the unique work-location lookup; their payloads and ordinals may differ.
-/
theorem itemTask_metadata
    {work address first second owners more producer parent
      left right leftResult rightResult}
    (hl : TaskAt work (.item address first) owners producer (.item left leftResult))
    (hr : TaskAt work (.item address second) more parent (.item right rightResult))
    : left = right ∧ producer = parent := by
  obtain ⟨node, items, enclosing, result, children, located, _, _, payload⟩ := hl
  obtain ⟨node', items', enclosing', result', children', located', _, _, payload'⟩ := hr
  have same := Option.some.inj (located.symm.trans located')
  simp only [WorkLocation.mk.injEq, Work.stream.injEq] at same
  exact ⟨(Payload.item.inj payload).1.trans
    (same.1.1.trans (Payload.item.inj payload').1.symm), same.2.1⟩

/-- A successful item's source slice includes its own indexed position, even for null,
an empty object, or an empty list. Witness: containers are retained in true-mode slices.
-/
theorem SourceTask.item_position {task : SourceTask} {node result}
    (payload : task.payload = .item node result) (success : result.isOk = true)
    : node.path ++ [.index task.index] ∈ task.positions true := by
  rw [SourceTask.positions, payload]
  cases result with
  | error _ => contradiction
  | ok pair =>
      rcases pair with ⟨value, errors⟩
      cases value <;> simp [DeliveryPaths.result, ResponsePositions.value]

/-- A successful published item recovers its stream descriptor and indexed source path.
Witness: structural task provenance plus the actual successful publication outcome.
-/
theorem Explains.published_item {work groups streams events matching failures cursors}
    (explained : Explains work groups streams events matching failures)
    {task address ordinal}
    (member : task ∈ sourceTasks [] none cursors work)
    (same : task.occurrence = .item address ordinal)
    (published : Published matching events task.occurrence)
    : ∃ node result,
        task.payload = .item node result
        ∧ result.isOk = true
        ∧ node.path ++ [.index task.index] ∈ task.positions true := by
  obtain ⟨owners, known⟩ := sourceTasks_known .root cursors member
  obtain ⟨otherOwners, parent, payload, actual, success⟩ :=
    explained.published_task published
  have payloadSame := (known.unique actual).2.2
  rw [same] at known
  obtain ⟨node, items, enclosing, result, children, _, _, _, payload⟩ := known
  refine ⟨node, result, payload, ?_, ?_⟩
  · rw [← payloadSame, payload] at success
    cases result <;> simp_all [Payload.failure, Except.isOk, Except.toBool]
  · apply SourceTask.item_position payload
    rw [← payloadSame, payload] at success
    cases result <;> simp_all [Payload.failure, Except.isOk, Except.toBool]

/-- A publication of any stream item includes a publication of its initial ordinal.
Witness: either the item itself is ordinal zero or the predecessor-chain theorem.
-/
theorem Explains.published_first_item {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {address ordinal} (published : Published matching events (.item address ordinal))
    : Published matching events (.item address 0) := by
  obtain ⟨index, event, selected, value, same⟩ := published
  cases ordinal with
  | zero => exact ⟨index, event, selected, value, same⟩
  | succ ordinal =>
      obtain ⟨earlier, first, _, atEarlier, firstValue, matched⟩ :=
        explained.item_earlier selected value same (by omega : 0 < ordinal + 1)
      exact ⟨earlier, first, atEarlier, firstValue, matched⟩

/-- Two published stream occurrences with the same list path have the same structural
stream address. Witness: both first items publish; a unique list seed makes their first
source positions identical, so source disjointness rules out two different occurrences.
-/
theorem Explains.stream_address_unique
    {work groups streams events matching failures initial slices positions}
    (explained : Explains work groups streams events matching failures)
    (seeded : WorkCursorSeed initial work slices)
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    {left right leftAddress rightAddress leftOrdinal rightOrdinal
      leftNode rightNode leftResult rightResult}
    (leftMember : left ∈ sourceTasks [] none initial work)
    (rightMember : right ∈ sourceTasks [] none initial work)
    (leftOccurrence : left.occurrence = .item leftAddress leftOrdinal)
    (rightOccurrence : right.occurrence = .item rightAddress rightOrdinal)
    (leftPayload : left.payload = .item leftNode leftResult)
    (rightPayload : right.payload = .item rightNode rightResult)
    (leftPublished : Published matching events left.occurrence)
    (rightPublished : Published matching events right.occurrence)
    (samePath : leftNode.path = rightNode.path)
    : leftAddress = rightAddress := by
  have firstPublished := Explains.published_first_item explained
    (leftOccurrence ▸ leftPublished)
  have secondPublished := Explains.published_first_item explained
    (rightOccurrence ▸ rightPublished)
  obtain ⟨first, ⟨firstMember, firstOccurrence⟩, _⟩ :=
    Explains.published_sourceTask explained firstPublished initial
  obtain ⟨second, ⟨secondMember, secondOccurrence⟩, _⟩ :=
    Explains.published_sourceTask explained secondPublished initial
  have firstPub : Published matching events first.occurrence :=
    firstOccurrence.symm ▸ firstPublished
  have secondPub : Published matching events second.occurrence :=
    secondOccurrence.symm ▸ secondPublished
  obtain ⟨firstNode, firstResult, firstPayload, _, firstPosition⟩ :=
    Explains.published_item explained firstMember firstOccurrence firstPub
  obtain ⟨secondNode, secondResult, secondPayload, _, secondPosition⟩ :=
    Explains.published_item explained secondMember secondOccurrence secondPub
  obtain ⟨_, leftTask⟩ := sourceTasks_known .root initial leftMember
  obtain ⟨_, rightTask⟩ := sourceTasks_known .root initial rightMember
  obtain ⟨_, firstTask⟩ := sourceTasks_known .root initial firstMember
  obtain ⟨_, secondTask⟩ := sourceTasks_known .root initial secondMember
  rw [leftOccurrence, leftPayload] at leftTask
  rw [rightOccurrence, rightPayload] at rightTask
  rw [firstOccurrence, firstPayload] at firstTask
  rw [secondOccurrence, secondPayload] at secondTask
  have leftNodeSame := (itemTask_metadata leftTask firstTask).1
  have rightNodeSame := (itemTask_metadata rightTask secondTask).1
  have firstSeed := sourceTasks_seeded seeded firstMember
  have secondSeed := sourceTasks_seeded seeded secondMember
  simp only [SourceTask.Seeded, firstOccurrence, firstPayload, Nat.add_zero] at firstSeed
  simp only [SourceTask.Seeded, secondOccurrence, secondPayload, Nat.add_zero] at secondSeed
  obtain ⟨before, start, origin, cursor, firstIndex⟩ := firstSeed
  obtain ⟨after, next, otherOrigin, otherCursor, secondIndex⟩ := secondSeed
  have paths : firstNode.path = secondNode.path := by
    simpa only [← leftNodeSame, ← rightNodeSame] using samePath
  rw [← paths] at otherCursor
  have sameStart := (origin.lookup_unique initialHistory disjoint otherOrigin cursor
    otherCursor).2.2
  by_cases different : leftAddress = rightAddress
  · exact different
  apply False.elim
  have differentTasks : first.occurrence ≠ second.occurrence := by
    rw [firstOccurrence, secondOccurrence]
    intro equal
    exact different (Occurrence.item.inj equal).1
  apply sourceTask_positions_disjoint (List.nodup_append.mp disjoint).2.1
    firstMember secondMember differentTasks firstPosition
  simpa only [paths, firstIndex, secondIndex, sameStart] using secondPosition

end GraphQL.IncrementalDelivery.Correctness
