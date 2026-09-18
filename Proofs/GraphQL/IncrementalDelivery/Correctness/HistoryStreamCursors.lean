import Proofs.GraphQL.IncrementalDelivery.Correctness.HistoryCursorPreservation

/-! Every admitted item publication sees its exact source index in prefix cursor replay. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths

/-- Cursor replay before a stream publication yields its absolute source index.
Witness: ordinal zero follows its initial/producer seed; later ordinals follow the
preceding item. One-shot publication, stream order, and source ownership exclude every
intervening write to the list cursor. Interrupted and failing histories are included.
-/
theorem sourceHistoryCursors_item
    {work groups streams events matching failures initial slices positions}
    (explained : Explains work groups streams events matching failures)
    (seeded : WorkCursorSeed initial work slices)
    (initialHistory : CursorHistory initial positions)
    (disjoint
      : (positions
          ++ (sourceTasks [] none initial work).flatMap
              (SourceTask.positions true)).Nodup)
    {task address ordinal node result cut event}
    (member : task ∈ sourceTasks [] none initial work)
    (occurrence : task.occurrence = .item address ordinal)
    (payload : task.payload = .item node result)
    (selected : events[cut]? = some event) (value : IsValue event)
    (matched : task.occurrence = matching cut)
    : ResponsePositions.cursorAt
        (sourceHistoryCursors (sourceTasks [] none initial work) matching events initial
          cut)
        node.path
      = some task.index := by
  have taskSeed := sourceTasks_seeded seeded member
  simp only [SourceTask.Seeded, occurrence, payload] at taskSeed
  obtain ⟨seed, start, origin, cursor, index⟩ := taskSeed
  have published : Published matching events task.occurrence :=
    ⟨cut, event, selected, value, matched.symm⟩
  have cutMatch := matched.symm.trans occurrence
  obtain ⟨owners, taskKnown⟩ := sourceTasks_known .root initial member
  cases ordinal with
  | zero =>
      simp only [Nat.add_zero] at index
      cases producerEq : task.producer with
      | none =>
          rw [producerEq] at origin
          change seed = initial at origin
          subst seed
          have preserved := sourceHistoryCursors_interval explained seeded initialHistory
            disjoint member occurrence payload published (producer := none) rfl cursor
            (lower := 0) (Nat.zero_le cut)
            (fun _ _ _ _ _ _ => by simp)
            (fun _ _ _ earlier atOther isValue =>
              no_stream_before_first explained selected value cutMatch earlier atOther isValue)
          rw [preserved, sourceHistoryCursors]
          simpa only [index] using cursor
      | some parent =>
          rw [producerEq] at origin
          obtain ⟨creator, creatorMember, creatorOccurrence, seedEq⟩ := origin
          rw [matched, producerEq] at taskKnown
          obtain ⟨prior, previous, earlier, atPrior, priorValue, priorMatch⟩ :=
            explained.producer_before selected value taskKnown
          have creatorMatch : creator.occurrence = matching prior :=
            creatorOccurrence.trans priorMatch.symm
          have priorLookup : ResponsePositions.cursorAt
              (sourceHistoryCursors (sourceTasks [] none initial work) matching events
                initial (prior + 1)) node.path = some start := by
            rw [sourceHistoryCursors_step atPrior,
              sourceEventCursors_value priorValue creatorMember creatorMatch]
            exact SourceTask.cursorUpdates_introduce (seedEq ▸ cursor)
          have priorPublished : Published matching (events.take (prior + 1)) parent :=
            ⟨prior, previous, (List.getElem?_take_of_lt (by omega)).trans atPrior,
              priorValue, priorMatch⟩
          have preserved := sourceHistoryCursors_interval explained seeded initialHistory
            disjoint member occurrence payload published
            (producer := some parent) ⟨creator, creatorMember, creatorOccurrence, seedEq⟩
            cursor (lower := prior + 1) (by omega : prior + 1 ≤ cut)
            (fun _ _ after _ selected value =>
              no_producer_after explained priorPublished after selected value)
            (fun _ _ _ earlier atOther isValue =>
              no_stream_before_first explained selected value cutMatch earlier atOther isValue)
          rw [preserved]
          simpa only [index] using priorLookup
  | succ ordinal =>
      obtain ⟨prior, previous, earlier, atPrior, priorValue, priorMatch⟩ :=
        explained.item_predecessor selected value cutMatch
      obtain ⟨priorTask, priorMember, priorMatched⟩ :=
        publication_sourceTask (initial := initial) explained atPrior priorValue
      have priorOccurrence := priorMatched.trans priorMatch
      have priorPublished : Published matching events priorTask.occurrence :=
        ⟨prior, previous, atPrior, priorValue, priorMatched.symm⟩
      obtain ⟨priorNode, priorResult, priorPayload, _, _⟩ :=
        Explains.published_item explained priorMember priorOccurrence priorPublished
      obtain ⟨priorOwners, priorKnown⟩ := sourceTasks_known .root initial priorMember
      have currentKnown := taskKnown
      have previousKnown := priorKnown
      rw [occurrence, payload] at currentKnown
      rw [priorOccurrence, priorPayload] at previousKnown
      obtain ⟨sameNode, sameProducer⟩ := itemTask_metadata currentKnown previousKnown
      have priorSeed := sourceTasks_seeded seeded priorMember
      simp only [SourceTask.Seeded, priorOccurrence, priorPayload] at priorSeed
      obtain ⟨before, first, priorOrigin, priorCursor, priorIndex⟩ := priorSeed
      rw [← sameNode] at priorCursor
      have sameStart := (origin.lookup_unique initialHistory disjoint priorOrigin cursor
        priorCursor).2.2
      have nextIndex : priorTask.index + 1 = task.index := by omega
      have priorLookup : ResponsePositions.cursorAt
          (sourceHistoryCursors (sourceTasks [] none initial work) matching events
            initial (prior + 1)) node.path = some task.index := by
        rw [sourceHistoryCursors_step atPrior,
          sourceEventCursors_value priorValue priorMember priorMatched, sameNode]
        simpa only [nextIndex]
          using SourceTask.cursorUpdates_stream
            (current :=
              sourceHistoryCursors
                (sourceTasks [] none initial work) matching events initial prior)
            priorPayload
      have noProducer : ∀ index event, prior + 1 ≤ index → index < cut
          → events[index]? = some event → IsValue event
          → task.producer ≠ some (matching index) := by
        intro index event after _ selected value
        cases producerEq : task.producer with
        | none => simp
        | some parent =>
            have priorProducer : priorTask.producer = some parent :=
              sameProducer.symm.trans producerEq
            rw [priorMatched, priorProducer] at priorKnown
            obtain ⟨creatorIndex, creatorEvent, creatorEarlier, creatorAt,
                creatorValue, creatorMatch⟩ :=
              explained.producer_before atPrior priorValue priorKnown
            have creatorPublished : Published matching (events.take (prior + 1)) parent :=
              ⟨creatorIndex, creatorEvent,
                (List.getElem?_take_of_lt (by omega)).trans creatorAt,
                creatorValue, creatorMatch⟩
            exact no_producer_after explained creatorPublished after selected value
      have preserved := sourceHistoryCursors_interval explained seeded initialHistory
        disjoint member occurrence payload published origin cursor
        (lower := prior + 1) (by omega : prior + 1 ≤ cut) noProducer
        (fun _ _ after before atOther isValue => no_stream_between_items explained
          atPrior priorValue priorMatch selected value cutMatch
          (by omega) before atOther isValue)
      rw [preserved]
      exact priorLookup

end GraphQL.IncrementalDelivery.Correctness
