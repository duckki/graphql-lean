import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceCursorReplay

/-! Causal publication and unique list ownership preserve cursors across interleaving. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths

/-- A source label carrying an item payload has an item occurrence. Witness: invert its
real scheduler task; deferred occurrences can only carry object payloads.
-/
theorem sourceTask_item_occurrence {initial work task node result}
    (member : task ∈ sourceTasks [] none initial work)
    (payload : task.payload = .item node result)
    : ∃ address ordinal, task.occurrence = .item address ordinal := by
  obtain ⟨_, known⟩ := sourceTasks_known .root initial member
  rw [payload] at known
  cases occurrence : task.occurrence with
  | deferred address =>
      rw [occurrence] at known
      obtain ⟨_, _, _, _, _, _, _, impossible⟩ := known
      cases impossible
  | item address ordinal => exact ⟨address, ordinal, rfl⟩

/-- A value event's matched source label is available at its exact observed index.
Witness: publication provenance and the source inventory's unique occurrence lookup.
-/
theorem publication_sourceTask {work groups streams events matching failures initial}
    (explained : Explains work groups streams events matching failures)
    {index event} (selected : events[index]? = some event) (value : IsValue event)
    : ∃ task ∈ sourceTasks [] none initial work, task.occurrence = matching index := by
  obtain ⟨task, ⟨member, same⟩, _⟩ := Explains.published_sourceTask explained
    ⟨index, event, selected, value, rfl⟩ initial
  exact ⟨task, member, same⟩

/-- An intervening publication outside this list's producer and stream cannot write its
cursor. Witness: other payloads cannot introduce the list, and another published stream
cannot advance it. Control outputs introduce no cursors.
-/
theorem sourceEventCursors_avoid
    {work groups streams events matching failures initial slices positions}
    (explained : Explains work groups streams events matching failures)
    (seeded : WorkCursorSeed initial work slices)
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    {task address ordinal node result producer seed start index event}
    (member : task ∈ sourceTasks [] none initial work)
    (occurrence : task.occurrence = .item address ordinal)
    (payload : task.payload = .item node result)
    (published : Published matching events task.occurrence)
    (origin : CursorOrigin initial (sourceTasks [] none initial work) producer seed)
    (cursor : ResponsePositions.cursorAt seed node.path = some start)
    (selected : events[index]? = some event)
    (notProducer : IsValue event → producer ≠ some (matching index))
    (notStream : IsValue event → ∀ ordinal, matching index ≠ .item address ordinal)
    : ∀ entry ∈
        sourceEventCursors (sourceTasks [] none initial work) matching index event,
        entry.1 ≠ node.path := by
  have classified : IsValue event ∨ ¬IsValue event := by cases event <;> simp [IsValue]
  rcases classified with value | control
  · obtain ⟨other, otherMember, otherOccurrence⟩ := publication_sourceTask explained selected value
    rw [sourceEventCursors_value value otherMember otherOccurrence]
    have introductions := origin.no_other_introduction initialHistory disjoint cursor
      otherMember (by simpa only [otherOccurrence] using notProducer value)
    cases otherPayload : other.payload with
    | object path completed =>
        simpa only [SourceTask.cursorUpdates, otherPayload] using introductions
    | item otherNode completed =>
        intro entry belongs
        simp only [SourceTask.cursorUpdates, otherPayload, List.mem_cons] at belongs
        rcases belongs with rfl | belongs
        · intro equal
          obtain ⟨otherAddress, otherOrdinal, otherShape⟩ :=
            sourceTask_item_occurrence otherMember otherPayload
          have otherPublished : Published matching events other.occurrence :=
            ⟨index, event, selected, value, otherOccurrence.symm⟩
          have same := Explains.stream_address_unique explained seeded initialHistory
            disjoint member otherMember occurrence otherShape payload otherPayload
            published otherPublished equal.symm
          exact notStream value otherOrdinal
            (otherOccurrence.symm.trans (otherShape.trans (congrArg
              (fun route => Occurrence.item route otherOrdinal) same.symm)))
        · exact introductions entry belongs
  · simp only [sourceEventCursors_control control, List.not_mem_nil, false_implies,
      implies_true]

/-- A known stream cursor survives a supplied interval that excludes its producer and
stream publications. Witness: per-event noninterference and finite cursor replay.
-/
theorem sourceHistoryCursors_interval
    {work groups streams events matching failures initial slices positions}
    (explained : Explains work groups streams events matching failures)
    (seeded : WorkCursorSeed initial work slices)
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    {task address ordinal node result producer seed start lower upper}
    (member : task ∈ sourceTasks [] none initial work)
    (occurrence : task.occurrence = .item address ordinal)
    (payload : task.payload = .item node result)
    (published : Published matching events task.occurrence)
    (origin : CursorOrigin initial (sourceTasks [] none initial work) producer seed)
    (cursor : ResponsePositions.cursorAt seed node.path = some start)
    (ordered : lower ≤ upper)
    (notProducer
      : ∀ index event,
          lower ≤ index
          → index < upper
          → events[index]? = some event
          → IsValue event
          → producer ≠ some (matching index))
    (notStream
      : ∀ index event,
          lower ≤ index
          → index < upper
          → events[index]? = some event
          → IsValue event
          → ∀ ordinal, matching index ≠ .item address ordinal)
    : ResponsePositions.cursorAt
        (sourceHistoryCursors (sourceTasks [] none initial work) matching events initial
          upper)
        node.path
      = ResponsePositions.cursorAt
          (sourceHistoryCursors (sourceTasks [] none initial work) matching events initial
            lower)
          node.path := by
  apply sourceHistoryCursors_preserve ordered
  intro index event lowerBound upperBound selected
  exact sourceEventCursors_avoid explained seeded initialHistory disjoint member occurrence
    payload published origin cursor selected
    (notProducer index event lowerBound upperBound selected)
    (notStream index event lowerBound upperBound selected)

/-- No stream item precedes its ordinal-zero publication. Witness: exact correspondence
between ordinal order and output-index order, even if outputs from other streams interleave.
-/
theorem no_stream_before_first {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {cut current address index event} (atCut : events[cut]? = some current)
    (cutValue : IsValue current) (cutMatch : matching cut = .item address 0)
    (earlier : index < cut) (selected : events[index]? = some event)
    (value : IsValue event)
    : ∀ ordinal, matching index ≠ .item address ordinal := by
  intro ordinal same
  have impossible := (explained.item_order selected value same atCut cutValue cutMatch).mp earlier
  omega

/-- No publication of this stream fits strictly between adjacent ordinal publications.
Witness: exact item order would require a natural ordinal strictly between n and n+1.
-/
theorem no_stream_between_items {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {left first right second address ordinal index event}
    (atLeft : events[left]? = some first) (leftValue : IsValue first)
    (leftMatch : matching left = .item address ordinal)
    (atRight : events[right]? = some second) (rightValue : IsValue second)
    (rightMatch : matching right = .item address (ordinal + 1))
    (afterLeft : left < index) (beforeRight : index < right)
    (selected : events[index]? = some event) (value : IsValue event)
    : ∀ next, matching index ≠ .item address next := by
  intro next same
  have lower := (explained.item_order atLeft leftValue leftMatch selected value same).mp afterLeft
  have upper := (explained.item_order selected value same atRight rightValue rightMatch).mp beforeRight
  omega

/-- A producer cannot publish again at or after a later cut. Witness: its earlier
publication and one-shot occurrence matching, not payload or delivery-owner inequality.
-/
theorem no_producer_after {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {producer cut index event}
    (before : Published matching (events.take cut) producer)
    (later : cut ≤ index) (selected : events[index]? = some event) (value : IsValue event)
    : some producer ≠ some (matching index) := by
  obtain ⟨earlier, previous, earlierBound, atEarlier, previousValue, same⟩ := before.before
  intro equal
  have repeated := explained.publication_unique atEarlier previousValue selected value
    (same.trans (Option.some.inj equal))
  omega

end GraphQL.IncrementalDelivery.Correctness
