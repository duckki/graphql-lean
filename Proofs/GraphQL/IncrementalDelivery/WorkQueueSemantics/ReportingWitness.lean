import GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! Projections of existential reporting evidence. The selected inventory is proof-only;
it is not retained by an executable queue or used to choose runtime errors.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

/-- Every available rejection has been exposed by the observed output boundary. -/
theorem FailureReportingWitness.cut_le {work initial events reported entry}
    (witness : FailureReportingWitness work initial events reported)
    (member : entry ∈ reported)
    : entry.1 ≤ events.length := by
  obtain ⟨before, after, same⟩ := List.mem_iff_append.mp member
  exact (witness before entry.1 entry.2 after same).1

/-- Distinct causal occurrences also supply a reporting witness at their causal cuts. -/
theorem FailureWitness.reporting {work initial matching events failures}
    (witness : FailureWitness work initial matching events failures)
    (distinct : (failures.map Prod.snd).Nodup)
    : FailureReportingWitness work initial events failures := by
  intro before cut occurrence after same
  have facts := witness before cut occurrence after same
  refine ⟨facts.1, facts.2.1, ?_, facts.2.2.1⟩
  rw [same, List.map_append, List.map_cons] at distinct
  intro member
  exact (List.nodup_append.mp distinct).2.2 occurrence member occurrence (by simp) rfl

/-- Identical cuts satisfy availability; this also preserves explanations that used
the stronger exact-entry sublist requirement.
-/
theorem CausalFailuresAvailable.of_sublist {failures reported : FailureCuts}
    (included : failures.Sublist reported)
    : CausalFailuresAvailable failures reported := by
  intro cut occurrence member
  exact ⟨cut, included.subset member, Nat.le_refl _⟩

/-- Additional available rejections retain the evidence for each causal occurrence. -/
theorem CausalFailuresAvailable.reporting_mono {failures reported more : FailureCuts}
    (available : CausalFailuresAvailable failures reported)
    (included : reported.Subset more)
    : CausalFailuresAvailable failures more := by
  intro cut occurrence member
  obtain ⟨availableCut, present, earlier⟩ := available cut occurrence member
  exact ⟨availableCut, included present, earlier⟩

/-- Every causal failure available through a boundary can be reported through it. -/
theorem CausalFailuresAvailable.failedBefore_subset {failures reported : FailureCuts}
    (available : CausalFailuresAvailable failures reported) (bound : Nat)
    : (failedBefore failures bound).Subset (failedBefore reported bound) := by
  intro occurrence member
  simp only [failedBefore, List.mem_map, List.mem_filter, decide_eq_true_eq] at member ⊢
  obtain ⟨⟨cut, occurrence⟩, ⟨member, bounded⟩, rfl⟩ := member
  obtain ⟨availableCut, present, earlier⟩ := available cut occurrence member
  exact ⟨(availableCut, occurrence), ⟨present, Nat.le_trans earlier bounded⟩, rfl⟩

/-- Restricting both inventories to a boundary preserves their causal availability link. -/
theorem CausalFailuresAvailable.prefix {failures reported : FailureCuts}
    (available : CausalFailuresAvailable failures reported) (bound : Nat)
    : CausalFailuresAvailable (failures.filter (fun entry => entry.1 ≤ bound))
        (reported.filter (fun entry => entry.1 ≤ bound)) := by
  intro cut occurrence member
  obtain ⟨member, bounded⟩ := List.mem_filter.mp member
  obtain ⟨availableCut, present, earlier⟩ := available cut occurrence member
  exact ⟨
    availableCut,
    List.mem_filter.mpr
      ⟨present, by simpa using Nat.le_trans earlier (of_decide_eq_true bounded)⟩,
    earlier
  ⟩

/-- Recording a causal failure reuses its already available reporting occurrence. -/
theorem CausalFailuresAvailable.record {failures reported : FailureCuts}
    (available : CausalFailuresAvailable failures reported)
    {cut availableCut occurrence}
    (present : (availableCut, occurrence) ∈ reported) (earlier : availableCut ≤ cut)
    : CausalFailuresAvailable (failures ++ [(cut, occurrence)]) reported := by
  intro nextCut nextOccurrence member
  rcases List.mem_append.mp member with old | added
  · exact available nextCut nextOccurrence old
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp added)
    exact ⟨availableCut, present, earlier⟩

/-- A distinct causal inventory can serve as all reporting evidence for a history. -/
theorem Explains.of_causal_failures {work groups streams events matching failures}
    (initialized : Initializes work groups streams)
    (witness
      : FailureWitness work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (distinct : (failures.map Prod.snd).Nodup)
    (allowed
      : ∀ index event,
          events[index]? = some event
          → EventAllowed work ((groups ++ streams).map DeliveryNode.ref) matching
              (events.take index) failures event)
    : Explains work groups streams events matching failures :=
  ⟨
    initialized,
    witness,
    failures,
    witness.reporting distinct,
    CausalFailuresAvailable.of_sublist (List.Sublist.refl _),
    allowed
  ⟩

/-- Select the existing reporting witness of an explained history for dependent proofs. -/
noncomputable def Explains.reportingFailures
    {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    : FailureCuts :=
  Classical.choose explained.2.2

/-- The selected reporting inventory has precisely the public witness's obligations. -/
theorem Explains.reportingFacts {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    : FailureReportingWitness work ((groups ++ streams).map DeliveryNode.ref) events
        explained.reportingFailures
      ∧ CausalFailuresAvailable failures explained.reportingFailures
      ∧ ∀ index event,
          events[index]? = some event
          → EventAllowed work ((groups ++ streams).map DeliveryNode.ref) matching
              (events.take index) failures event explained.reportingFailures :=
  Classical.choose_spec explained.2.2

/-- Each observed atom obeys the accounting rules with that same reporting inventory. -/
theorem Explains.eventAllowed {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    (index : Nat) (event : WorkQueueEvent) (selected : events[index]? = some event)
    : EventAllowed work ((groups ++ streams).map DeliveryNode.ref) matching
        (events.take index) failures event explained.reportingFailures :=
  explained.reportingFacts.2.2 index event selected

end GraphQL.IncrementalDelivery.WorkQueueSemantics
