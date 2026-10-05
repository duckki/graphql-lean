import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SettlementClosures

/-! Separate a notice carrier from settlements accepted immediately after that carrier. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Carrier eligibility precedes the next settlement inventory
-----------------------------------------------------------------------------------------

/-- The prefix including an actual carrier is explained before its later settlements.
Witness: restrict to the carrier's starting boundary, then append that permitted event with
the same failure inventory. Settlements at the new output-prefix length are not included.
-/
theorem Explains.after_carrier_before_settlements
    {work groups streams events matching failures index event}
    (explained : Explains work groups streams events matching failures)
    (selected : events[index]? = some event)
    : Explains work groups streams (events.take (index + 1)) matching
        (failures.filter (fun entry => entry.1 ≤ index)) := by
  have bounded := Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1
  have length := List.length_take_of_le bounded
  have combined : Explains work groups streams (events.take index ++ events.drop index)
      matching failures := by simpa only [List.take_append_drop] using explained
  have shorter := combined.prefix
  rw [length] at shorter
  have allowed := explained.2.2 index event selected
  rw [← eventAllowed_filter (bound := index) (by rw [length]; exact Nat.le_refl _)] at allowed
  have extended := shorter.append_event allowed
  simpa only [List.take_add_one, selected, Option.toList_some] using extended

/-- Healthy accounting before the next settlements excludes every future own failure.
Witness: a visible record contradicts health. An omitted record has a cut after the cutoff,
so every retained cancellation is among its licensing predecessors, including at an equal
output boundary. Accounting would contradict its uncancelled license or failed payload.
The accounting prefix may include the carrier immediately following `cutoff`.
-/
theorem Explains.healthy_accounted_no_recorded_failure_before_next_settlements
    {work groups streams events matching failures index cutoff ref}
    (explained : Explains work groups streams events matching failures)
    (adjacent : index ≤ cutoff + 1)
    (healthy
      : ¬NodeFailed work matching (events.take index)
          (failures.filter (fun entry => entry.1 ≤ cutoff)) ref)
    (accounted
      : NodeAccounted work matching (events.take index)
          (failures.filter (fun entry => entry.1 ≤ cutoff)) ref)
    : ¬HasRecordedFailure work failures events.length ref := by
  intro recorded
  obtain ⟨occurrence, owners, settled, ⟨producer, payload, known⟩, member⟩ := recorded
  obtain ⟨entry, included, same⟩ := List.mem_map.mp settled
  have inCuts := (List.mem_filter.mp included).1
  have actual : (entry.1, occurrence) ∈ failures := by simpa only [← same] using inCuts
  by_cases retained : entry.1 ≤ cutoff
  · have kept : (entry.1, occurrence) ∈ failures.filter (fun entry => entry.1 ≤ cutoff) :=
      List.mem_filter.mpr ⟨actual, by simpa using retained⟩
    have reached := of_decide_eq_true (List.mem_filter.mp included).2
    by_cases before : entry.1 ≤ (events.take index).length
    · exact healthy (NodeFailed.task known member (mem_failedBefore kept before))
    · have later : index < entry.1 := by
        simp only [List.length_take] at before
        omega
      have originalAccounted := TaskAccounted.more_failures
        (accounted occurrence owners ⟨producer, payload, known⟩ member)
        (fun _ selected => (List.mem_filter.mp selected).1)
      exact explained.recorded_task_unaccounted_before_cut actual later originalAccounted
  · obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp actual
    rw [equal] at explained accounted
    have license := explained.2.1 before entry.1 occurrence after rfl
    have strictly : cutoff < entry.1 := by omega
    have earlier : index ≤ entry.1 := by omega
    have visible := explained.2.1.filter_before_settlement strictly
    rcases accounted occurrence owners ⟨producer, payload, known⟩ member with cancelled
      | published
    · rw [visible] at cancelled
      have old : TaskCancelled work matching (events.take index) before occurrence :=
        cancelled.mono (fun _ selected => (List.mem_filter.mp selected).1)
      have extension := old.append ((events.take entry.1).drop index)
      have first : (events.take entry.1).take index = events.take index := by
        rw [List.take_take, Nat.min_eq_left earlier]
      rw [← first, List.take_append_drop] at extension
      exact license.2.2.2 extension
    · apply explained.failed_unpublished (occurrence := occurrence)
        (mem_failedBefore (by simp) (Nat.le_refl entry.1))
      simpa only [List.take_append_drop] using published.append (events.drop index)

end GraphQL.IncrementalDelivery.WorkQueueSemantics
