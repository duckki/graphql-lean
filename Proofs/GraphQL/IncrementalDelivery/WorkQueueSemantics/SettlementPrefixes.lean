import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.HistoryExtension

/-! Separate an accepted settlement from the earlier cuts licensing it. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Earlier outputs inspect only earlier settlements
-----------------------------------------------------------------------------------------

/-- Every settlement after a selected entry has a cut at least as large as its cut.
Witness: split the ordered failure witness at the later entry; the selected entry is
among its licensing predecessors. Equal cuts retain their settlement order.
-/
theorem FailureWitness.later_cut_ge
    {work initial matching events before cut occurrence after}
    (witness
      : FailureWitness work initial matching events
          (before ++ (cut, occurrence) :: after))
    {entry} (member : entry ∈ (cut, occurrence) :: after)
    : cut ≤ entry.1 := by
  rcases List.mem_cons.mp member with rfl | member
  · exact Nat.le_refl _
  · obtain ⟨earlier, later, equal⟩ := List.mem_iff_append.mp member
    have facts := witness (before ++ (cut, occurrence) :: earlier) entry.1 entry.2 later
      (by simp only [equal, List.append_assoc, List.cons_append])
    exact facts.2.1 (cut, occurrence) (by simp)

/-- Outputs strictly before a settlement see none of that settlement or its successors.
Witness: the ordered cut bound rejects their filter entries, including equal-cut siblings.
-/
theorem FailureWitness.filter_before_settlement
    {work initial matching events before cut occurrence after index}
    (witness
      : FailureWitness work initial matching events
          (before ++ (cut, occurrence) :: after))
    (earlier : index < cut)
    : (before ++ (cut, occurrence) :: after).filter (fun entry => entry.1 ≤ index)
      = before.filter (fun entry => entry.1 ≤ index) := by
  have rejected : ((cut, occurrence) :: after).filter (fun entry => entry.1 ≤ index) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    have bound := witness.later_cut_ge member
    simp only [decide_eq_true_eq]
    omega
  simp only [List.filter_append, rejected, List.append_nil]

/-- The output prefix at a settlement is explained by its licensing predecessors alone.
Witness: earlier cuts remain licensed, and every earlier output ignores the selected
settlement and all later entries. This does not assume open owners or termination.
-/
theorem Explains.before_settlement
    {work groups streams events matching before cut occurrence after}
    (explained
      : Explains work groups streams events matching
          (before ++ (cut, occurrence) :: after))
    : Explains work groups streams (events.take cut) matching before := by
  have facts := explained.2.1 before cut occurrence after rfl
  have bounded := facts.1
  refine ⟨explained.1, ?_, ?_⟩
  · intro earlier boundary task later equal
    have licensed := explained.2.1 earlier boundary task
      (later ++ (cut, occurrence) :: after)
      (by simp only [equal, List.append_assoc, List.cons_append])
    have beforeCut := facts.2.1 (boundary, task) (by simp [equal])
    refine ⟨by simp only [List.length_take]; omega, licensed.2.1, ?_, ?_⟩
    · simpa only [List.take_take, Nat.min_eq_left beforeCut] using licensed.2.2.1
    · simpa only [List.take_take, Nat.min_eq_left beforeCut] using licensed.2.2.2
  · refine ⟨explained.reportingFailures.filter (fun entry => entry.1 ≤ cut), ?_, ?_, ?_⟩
    · have full : FailureReportingWitness work ((groups ++ streams).map DeliveryNode.ref)
          (events.take cut ++ events.drop cut) explained.reportingFailures := by
        simpa only [List.take_append_drop] using explained.reportingFacts.1
      simpa only [List.length_take, Nat.min_eq_left bounded] using full.prefix
    · intro boundary task member
      have beforeCut := facts.2.1 (boundary, task) member
      obtain ⟨availableCut, present, earlier⟩ := explained.reportingFacts.2.1 boundary task
        (List.mem_append_left _ member)
      exact ⟨availableCut,
        List.mem_filter.mpr ⟨present, by simpa using Nat.le_trans earlier beforeCut⟩,
        earlier⟩
    intro index event selected
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have earlier : index < cut := by simp only [List.length_take] at within; omega
    have original : events[index]? = some event := by
      simpa only [List.getElem?_take_of_lt earlier] using selected
    have allowed := explained.eventAllowed index event original
    have visible := explained.2.1.filter_before_settlement
      (index := (events.take index).length) (by simp only [List.length_take]; omega)
    simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt earlier), EventAllowed,
      visible,
      failedBefore_filter _ (show (events.take index).length ≤ cut by
        simp only [List.length_take]; omega)]
      using allowed

end GraphQL.IncrementalDelivery.WorkQueueSemantics
