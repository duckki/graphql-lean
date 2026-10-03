import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupOpenness

/-! Proof-side placement at reported failure boundaries; cancellation licensing is separate. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Choose the first observable failure of a contributing owner after a candidate cut
-----------------------------------------------------------------------------------------

/-- At `index`, a failed group or stream reports an owner of the supplied occurrence. -/
def FailureReportAt (work : Execution.Work) (events : List Execution.WorkQueueEvent)
    (occurrence : Occurrence) (index : Nat)
    : Prop :=
  ∃ node errors,
    (events[index]? = some (.groupFailure node errors)
      ∨ events[index]? = some (.streamFailure node errors))
    ∧ ∃ owners, TaskHasOwners work occurrence owners ∧ node.ref ∈ owners

/-- A report position is within the actual event list.
Witness: either failure constructor is present at that index.
-/
theorem FailureReportAt.bound {work events occurrence index}
    (report : FailureReportAt work events occurrence index)
    : index < events.length := by
  obtain ⟨node, errors, event, _⟩ := report
  rcases event with group | stream
  · exact (List.getElem?_eq_some_iff.mp group).1
  · exact (List.getElem?_eq_some_iff.mp stream).1

/-- Find the first reported owner failure at or after the supplied candidate boundary.
This finite search chooses proof evidence only; it changes neither inputs nor outputs.
-/
noncomputable def firstReportedFailureCut (work : Execution.Work)
    (events : List Execution.WorkQueueEvent) (entry : Nat × Occurrence)
    : Option Nat := by
  classical
  exact (List.range events.length).findIdx?
    (fun index => decide (entry.1 ≤ index ∧ FailureReportAt work events entry.2 index))

/-- A selected report is bounded, no earlier than its candidate, and minimal among reports.
Witness: the standard first-index search characterization on the list of output indices.
-/
theorem firstReportedFailureCut_spec {work events entry index}
    (selected : firstReportedFailureCut work events entry = some index)
    : index < events.length
      ∧ entry.1 ≤ index
      ∧ FailureReportAt work events entry.2 index
      ∧ ∀ earlier,
          entry.1 ≤ earlier
          → FailureReportAt work events entry.2 earlier
          → index ≤ earlier := by
  classical
  obtain ⟨bound, report, minimal⟩ := List.findIdx?_eq_some_iff_getElem.mp selected
  simp only [List.getElem_range, decide_eq_true_eq] at report minimal
  refine ⟨by simpa using bound, report.1, report.2, ?_⟩
  intro earlier after reportAt
  exact Nat.le_of_not_lt (fun later => minimal earlier later ⟨after, reportAt⟩)

/-- Any reported owner at or after a candidate guarantees a selected boundary no later.
Witness: a missing search result would exclude the known report; minimality bounds a hit.
-/
theorem firstReportedFailureCut_exists {work events entry index}
    (after : entry.1 ≤ index) (report : FailureReportAt work events entry.2 index)
    : ∃ cut, firstReportedFailureCut work events entry = some cut ∧ cut ≤ index := by
  classical
  cases selected : firstReportedFailureCut work events entry with
  | none =>
      have absent := List.findIdx?_eq_none_iff.mp selected index
        (List.mem_range.mpr report.bound)
      simp [after, report] at absent
  | some cut =>
      exact ⟨cut, rfl, (firstReportedFailureCut_spec selected).2.2.2 _ after report⟩

/-- A least eligible report identifies the selected cut exactly.
Witness: the first-index search succeeds there and rejects every earlier index.
-/
theorem firstReportedFailureCut_eq_some {work events entry index}
    (after : entry.1 ≤ index) (report : FailureReportAt work events entry.2 index)
    (least
      : ∀ earlier,
          entry.1 ≤ earlier
          → FailureReportAt work events entry.2 earlier
          → index ≤ earlier)
    : firstReportedFailureCut work events entry = some index := by
  classical
  apply List.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨by simpa using report.bound, ?_, ?_⟩
  · simpa only [List.getElem_range, decide_eq_true_eq] using And.intro after report
  · intro earlier before
    simp only [List.getElem_range, decide_eq_true_eq]
    intro reported
    exact Nat.not_le_of_lt before (least earlier reported.1 reported.2)

/-- Move one candidate to its first reported owner failure, omitting unreported candidates.
Omission preserves reported counts, not necessarily all causal cancellation evidence.
-/
noncomputable def placeReportedFailure (work : Execution.Work)
    (events : List Execution.WorkQueueEvent) (entry : Nat × Occurrence)
    : Option (Nat × Occurrence) :=
  (firstReportedFailureCut work events entry).map (fun index => (index, entry.2))

/-- A candidate with no eligible failed-owner report is omitted by the search.
Witness: every output index fails the search predicate.
-/
theorem firstReportedFailureCut_eq_none {work events entry}
    (unreported : ∀ index, entry.1 ≤ index → ¬FailureReportAt work events entry.2 index)
    : firstReportedFailureCut work events entry = none := by
  classical
  apply List.findIdx?_eq_none_iff.mpr
  intro index _
  simp only [decide_eq_false_iff_not]
  exact fun report => unreported index report.1 report.2

/-- Place retained candidates at their first reports and order them by output index.
This is a count-preserving candidate construction, not yet a licensed failure witness.
-/
noncomputable def reportedFailureCuts (work : Execution.Work)
    (events : List Execution.WorkQueueEvent) (failures : FailureCuts)
    : FailureCuts :=
  (failures.filterMap (placeReportedFailure work events)).mergeSort
    (fun left right => left.1 ≤ right.1)

/-- Sorted placement contains exactly the selected candidates.
Witness: merge sort permutes its input without altering cut positions or occurrences.
-/
theorem reportedFailureCuts_perm (work : Execution.Work)
    (events : List Execution.WorkQueueEvent) (failures : FailureCuts)
    : (reportedFailureCuts work events failures).Perm
        (failures.filterMap (placeReportedFailure work events)) :=
  List.mergeSort_perm _ _

/-- Every placed entry comes from a candidate and retains its task occurrence.
Witness: membership in the sorted filter-map supplies the original entry and search hit.
-/
theorem reportedFailureCuts_origin {work events failures entry}
    (member : entry ∈ reportedFailureCuts work events failures)
    : ∃ original ∈ failures,
        entry.2 = original.2
        ∧ firstReportedFailureCut work events original = some entry.1 := by
  obtain ⟨original, old, selected⟩ := List.mem_filterMap.mp
    ((reportedFailureCuts_perm work events failures).mem_iff.mp member)
  obtain ⟨index, found, equal⟩ := Option.map_eq_some_iff.mp selected
  cases equal
  exact ⟨original, old, rfl, found⟩

/-- A selected report remains present after sorting the placement list.
Witness: insert its filter-map membership through the sort permutation.
-/
theorem reportedFailureCuts_mem {work events failures entry index}
    (member : entry ∈ failures)
    (selected : firstReportedFailureCut work events entry = some index)
    : (index, entry.2) ∈ reportedFailureCuts work events failures := by
  apply (reportedFailureCuts_perm work events failures).mem_iff.mpr
  exact List.mem_filterMap.mpr ⟨entry, member, by simp [placeReportedFailure, selected]⟩

/-- Placed boundaries are nondecreasing, including shared-owner ties.
Witness: merge sort with the total transitive order on output indices.
-/
theorem reportedFailureCuts_ordered (work : Execution.Work)
    (events : List Execution.WorkQueueEvent) (failures : FailureCuts)
    : (reportedFailureCuts work events failures).Pairwise
        (fun left right => left.1 ≤ right.1) := by
  have trans (left middle right : Nat × Occurrence)
      : decide (left.1 ≤ middle.1) = true → decide (middle.1 ≤ right.1) = true →
          decide (left.1 ≤ right.1) = true := by
    simp only [decide_eq_true_eq]
    exact Nat.le_trans
  have total (left right : Nat × Occurrence)
      : (decide (left.1 ≤ right.1) || decide (right.1 ≤ left.1)) = true := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using Nat.le_total left.1 right.1
  simpa only [reportedFailureCuts, decide_eq_true_eq]
    using List.pairwise_mergeSort trans total
      (failures.filterMap (placeReportedFailure work events))

/-- Placement retains occurrence uniqueness even when several cuts move to the same index.
Witness: filter-map never changes an occurrence, and sorting only permutes the results.
-/
theorem reportedFailureCuts_unique {work events failures}
    (unique : (failures.map Prod.snd).Nodup)
    : ((reportedFailureCuts work events failures).map Prod.snd).Nodup := by
  apply ((reportedFailureCuts_perm work events failures).map Prod.snd).nodup_iff.mpr
  apply List.pairwise_map.mpr
  apply (List.pairwise_map.mp unique).filterMap (placeReportedFailure work events)
  intro left right distinct placedLeft selectedLeft placedRight selectedRight
  obtain ⟨leftIndex, _, leftEq⟩ := Option.map_eq_some_iff.mp selectedLeft
  obtain ⟨rightIndex, _, rightEq⟩ := Option.map_eq_some_iff.mp selectedRight
  cases leftEq
  cases rightEq
  exact distinct

-----------------------------------------------------------------------------------------
-- Later placement retains precisely the contributions needed by each failed closure
-----------------------------------------------------------------------------------------

/-- No placed cut becomes visible earlier than its original candidate.
Witness: the selected report is no earlier than the source candidate boundary.
-/
theorem reportedFailureCuts_visible_subset (work : Execution.Work)
    (events : List Execution.WorkQueueEvent) (failures : FailureCuts) (index : Nat)
    : (failedBefore (reportedFailureCuts work events failures) index).Subset
        (failedBefore failures index) := by
  intro occurrence member
  obtain ⟨placed, visible, same⟩ := List.mem_map.mp member
  obtain ⟨original, old, retained, selected⟩ :=
    reportedFailureCuts_origin (List.mem_filter.mp visible).1
  have bound := (firstReportedFailureCut_spec selected).2.1
  have byNow : placed.1 ≤ index := by simpa using (List.mem_filter.mp visible).2
  exact List.mem_map.mpr
    ⟨
      original,
      List.mem_filter.mpr ⟨old, by simpa using Nat.le_trans bound byNow⟩,
      retained.symm.trans same
    ⟩

/-- Every visible contributing failure is placed by the failed-owner report that needs it.
Witness: that very report is a candidate for the first-report search, so the selected cut
is no later. No claim about the causal effect of omitted candidates is needed for counts.
-/
theorem reportedFailureCuts_covers_report {work events failures occurrence index}
    (visible : occurrence ∈ failedBefore failures index)
    (report : FailureReportAt work events occurrence index)
    : occurrence ∈ failedBefore (reportedFailureCuts work events failures) index := by
  obtain ⟨entry, member, same⟩ := List.mem_map.mp visible
  obtain ⟨old, before⟩ := List.mem_filter.mp member
  have after : entry.1 ≤ index := by simpa using before
  obtain ⟨cut, selected, bound⟩ := firstReportedFailureCut_exists after (same ▸ report)
  exact List.mem_map.mpr
    ⟨
      (cut, entry.2),
      List.mem_filter.mpr ⟨reportedFailureCuts_mem old selected, by simpa using bound⟩,
      same
    ⟩

/-- Removing only noncontributors from a distinct failure list preserves its error total.
Witness: restrict the original contribution function; omitted summands are zero, and
the retained list is a permutation of a membership filter of the original list.
-/
theorem nodeErrors_restrict {work failed selected ref errors}
    (counts : NodeErrors work failed ref errors) (failedUnique : failed.Nodup)
    (selectedUnique : selected.Nodup) (included : selected.Subset failed)
    (complete
      : ∀ occurrence ∈ failed,
          ∀ owners,
            TaskHasOwners work occurrence owners → ref ∈ owners → occurrence ∈ selected)
    : NodeErrors work selected ref errors := by
  classical
  obtain ⟨contribution, known, total⟩ := counts
  let kept := fun occurrence => decide (occurrence ∈ selected)
  have same : (failed.filter kept).Perm selected := by
    apply (List.perm_ext_iff_of_nodup (failedUnique.filter _) selectedUnique).mpr
    intro occurrence
    simp only [List.mem_filter, kept, decide_eq_true_eq]
    exact ⟨And.right, fun member => ⟨included member, member⟩⟩
  have zero : ((failed.filter (fun occurrence => !kept occurrence)).map contribution).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro count member
    obtain ⟨occurrence, retained, rfl⟩ := List.mem_map.mp member
    obtain ⟨owners, producer, payload, task, amount⟩ := known occurrence
      (List.mem_filter.mp retained).1
    have omitted : occurrence ∉ selected := by
      simpa [kept] using (List.mem_filter.mp retained).2
    have nonowner : ref ∉ owners := fun owner => omitted
      (complete occurrence (List.mem_filter.mp retained).1 owners ⟨producer, payload, task⟩ owner)
    simpa [nonowner] using amount
  refine ⟨contribution, fun occurrence member => known occurrence (included member), ?_⟩
  have partition := ((List.filter_append_perm kept failed).map contribution).sum_nat
  rw [List.map_append, List.sum_append, zero, Nat.add_zero,
    (same.map contribution).sum_nat] at partition
  exact total.trans partition.symm

/-- Any failed-owner event retains its exact total after first-report placement.
Witness: placement is a distinct subset of the visible old failures and retains every
contributor to this closure, so only zero summands can disappear.
-/
theorem reportedFailureCuts_nodeErrors {work events failures index node errors}
    (unique : (failures.map Prod.snd).Nodup)
    (counts : NodeErrors work (failedBefore failures index) node.ref errors)
    (atEvent
      : events[index]? = some (.groupFailure node errors)
        ∨ events[index]? = some (.streamFailure node errors))
    : NodeErrors work (failedBefore (reportedFailureCuts work events failures) index)
        node.ref errors := by
  apply nodeErrors_restrict counts
    ((List.filter_sublist.map Prod.snd).nodup unique)
    ((List.filter_sublist.map Prod.snd).nodup (reportedFailureCuts_unique unique))
    (reportedFailureCuts_visible_subset work events failures index)
  intro occurrence member owners task owner
  exact reportedFailureCuts_covers_report member ⟨node, errors, atEvent, owners, task, owner⟩

/-- First-report placement preserves a complete inventory and all reported error totals.
Witness: retained candidates keep their failed descriptors and reachability; report
indices give bounds, sorting gives order, and contributor coverage preserves both totals.
Unreported candidates may be omitted, so this does not yet preserve all causal evidence.
-/
theorem CompleteFailureInventory.reported {work events failures}
    (inventory : CompleteFailureInventory work events failures)
    : CompleteFailureInventory work events
        (reportedFailureCuts work events failures) := by
  refine ⟨reportedFailureCuts_ordered work events failures,
    reportedFailureCuts_unique inventory.2.1, ?_, ?_, ?_⟩
  · intro entry member
    obtain ⟨original, old, same, selected⟩ := reportedFailureCuts_origin member
    have oldKnown := inventory.2.2.1 original old
    exact ⟨Nat.le_of_lt (firstReportedFailureCut_spec selected).1,
      same ▸ oldKnown.2.1, same ▸ oldKnown.2.2⟩
  · intro index node errors atEvent
    exact reportedFailureCuts_nodeErrors inventory.2.1
      (inventory.2.2.2.1 index node errors atEvent) (.inl atEvent)
  · intro index node errors atEvent
    exact reportedFailureCuts_nodeErrors inventory.2.1
      (inventory.2.2.2.2 index node errors atEvent) (.inr atEvent)

-----------------------------------------------------------------------------------------
-- Actual replay supplies open owners at every placed cut without output admission
-----------------------------------------------------------------------------------------

/-- Every reported candidate in actual generated replay has an open contributing owner.
Witness: each selected boundary is an actual failed-group or failed-stream closure;
the independently proved implementation openness theorems apply at precisely that index.
-/
theorem createWorkQueue_reportedFailureCuts_open {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) (failures : FailureCuts)
    : let queue := State.initialize (Work.fromExecution work)
      let events := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∀ entry ∈ reportedFailureCuts work events failures,
        ∃ owners,
          TaskHasOwners work entry.2 owners
          ∧ ∃ ref ∈ owners,
              Open
                ((queue.initialGroups ++ queue.initialStreams).map
                  Execution.DeliveryNode.ref)
                (events.take entry.1) ref := by
  intro queue events entry member
  obtain ⟨original, _, same, selected⟩ := reportedFailureCuts_origin member
  obtain ⟨node, errors, atEvent, owners, task, owner⟩ :=
    (firstReportedFailureCut_spec selected).2.2.1
  refine ⟨owners, same ▸ task, node.ref, owner, ?_⟩
  rcases atEvent with group | stream
  · exact createWorkQueue_runNormalized_groupFailureOpenAt generated valid group
  · exact createWorkQueue_runNormalized_streamOpenAt generated valid stream List.mem_cons_self

/-- Actual replay has an ordered, exact-count failure inventory with open owners.
Witness: place the existing complete inventory at first reports. This is not a
FailureWitness: cancellation licensing and preservation of earlier carrier facts remain.
-/
theorem createWorkQueue_reportedFailureInventory_exists {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := State.initialize (Work.fromExecution work)
      let events := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∃ failures : FailureCuts,
        CompleteFailureInventory work events failures
        ∧ ∀ entry ∈ failures,
            ∃ owners,
              TaskHasOwners work entry.2 owners
              ∧ ∃ ref ∈ owners,
                  Open
                    ((queue.initialGroups ++ queue.initialStreams).map
                      Execution.DeliveryNode.ref)
                    (events.take entry.1) ref := by
  obtain ⟨failures, inventory⟩ :=
    createWorkQueue_completeFailureInventory_exists generated valid started
  exact ⟨_, inventory.reported, createWorkQueue_reportedFailureCuts_open generated valid failures⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
