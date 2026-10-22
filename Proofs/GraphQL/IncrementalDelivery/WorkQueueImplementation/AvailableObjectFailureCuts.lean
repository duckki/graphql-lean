import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceObjectFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReportingCauseCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OrderedFailureCuts

/-! Object failure availability combines source settlements and actual aggregate reports. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Retain both notification and report-cause availability at their actual output positions.
The retained source inventory supplies provenance, not an assumed callback-prefix order. -/
noncomputable def objectFailureCandidates (work : Execution.Work) (offset : Nat)
    (blocks : List SourceOutputBlock)
    : FailureCuts :=
  interleaveFailureCuts (sourceObjectFailureCuts offset blocks)
    (groupReportCandidateCuts work (blocks.filterMap Prod.fst) offset
      (blocks.flatMap Prod.snd))

/-- Every object candidate retains its original source or report position. -/
theorem objectFailureCandidates_partition (work : Execution.Work) (offset : Nat)
    (blocks : List SourceOutputBlock)
    : (objectFailureCandidates work offset blocks).Perm
        (groupReportCandidateCuts work (blocks.filterMap Prod.fst) offset
            (blocks.flatMap Prod.snd)
          ++ sourceObjectFailureCuts offset blocks) :=
  interleaveFailureCuts_partition _ _

/-- Notification and aggregate-report candidates are ordered at their unchanged cuts. -/
theorem objectFailureCandidates_ordered (work : Execution.Work) (offset : Nat)
    (blocks : List SourceOutputBlock)
    : (objectFailureCandidates work offset blocks).Pairwise
        (fun left right => left.1 ≤ right.1) :=
  interleaveFailureCuts_ordered (sourceObjectFailureCuts_ordered _ _)
    (groupReportCandidateCuts_ordered _ _ _ _)

/-- Keep each failed occurrence at its first demonstrated availability cut.
An aggregate may expose a cached rejection before its own notification callback. -/
noncomputable def availableObjectFailureCuts (work : Execution.Work) (offset : Nat)
    (blocks : List SourceOutputBlock)
    : FailureCuts :=
  firstReportingCuts [] (objectFailureCandidates work offset blocks)

/-- Availability selection preserves the original ordered candidate positions. -/
theorem availableObjectFailureCuts_ordered (work : Execution.Work) (offset : Nat)
    (blocks : List SourceOutputBlock)
    : (availableObjectFailureCuts work offset blocks).Pairwise
        (fun left right => left.1 ≤ right.1) :=
  (objectFailureCandidates_ordered _ _ _).sublist (firstReportingCuts_sublist _ _)

/-- Repeated reports and callbacks do not duplicate a reporting occurrence. -/
theorem availableObjectFailureCuts_unique (work : Execution.Work) (offset : Nat)
    (blocks : List SourceOutputBlock)
    : ((availableObjectFailureCuts work offset blocks).map Prod.snd).Nodup :=
  firstReportingCuts_distinct _ _

/-- Each available occurrence comes from a notification or a selected report cause. -/
theorem availableObjectFailureCuts_origin {work offset blocks entry}
    (member : entry ∈ availableObjectFailureCuts work offset blocks)
    : entry ∈ sourceObjectFailureCuts offset blocks
      ∨ entry
        ∈ groupReportCandidateCuts work (blocks.filterMap Prod.fst) offset
            (blocks.flatMap Prod.snd) := by
  have raw := (firstReportingCuts_sublist _ _).subset member
  exact Or.symm (List.mem_append.mp
    ((objectFailureCandidates_partition work offset blocks).mem_iff.mp raw))

/-- Every available cut lies inside the actual observed output interval. -/
theorem availableObjectFailureCuts_bounds {work offset blocks entry}
    (member : entry ∈ availableObjectFailureCuts work offset blocks)
    : offset ≤ entry.1 ∧ entry.1 ≤ offset + (blocks.flatMap Prod.snd).length := by
  rcases availableObjectFailureCuts_origin member with source | report
  · exact sourceObjectFailureCuts_bounds _ _ _ source
  · exact groupReportCandidateCuts_bounds _ _ _ _ _ report

/-- Each aggregate cause is available by its own report, even if its callback comes later. -/
theorem availableObjectFailureCuts_contributions {work : Execution.Work}
    {blocks : List SourceOutputBlock}
    (totals : SourceBlocksHaveFailureTotals work [] blocks) (offset : Nat)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent : (blocks.flatMap Prod.snd)[index]? = some (.groupFailure group errors))
    : ∃ parts : List (Occurrence × Nat),
        parts ≠ []
        ∧ (parts.map Prod.fst).Nodup
        ∧ (parts.map Prod.snd).sum = errors
        ∧ ∀ occurrence count,
            (occurrence, count) ∈ parts
            → occurrence
                ∈ failedBefore (availableObjectFailureCuts work offset blocks)
                    (offset + index)
              ∧ ∃ owners producer path,
                  TaskAt work occurrence owners producer (.object path (.error count))
                  ∧ group.ref ∈ owners := by
  have sources
      : GroupFailureSources work (blocks.filterMap Prod.fst) group.ref errors := by
    simpa only [List.nil_append] using totals _ _ (List.mem_of_getElem? atEvent)
  have chosen := groupReportSourceParts_spec sources
  refine ⟨groupReportSourceParts work (blocks.filterMap Prod.fst) group.ref errors,
    chosen.1, chosen.2.1, chosen.2.2.1, ?_⟩
  intro occurrence count member
  refine ⟨?_, (chosen.2.2.2 occurrence count member).2⟩
  have raw := groupReportCandidateCuts_atReport (offset := offset) atEvent member
  have included : (offset + index, occurrence)
      ∈ objectFailureCandidates work offset blocks :=
    (objectFailureCandidates_partition work offset blocks).mem_iff.mpr
      (List.mem_append_left _ raw)
  obtain ⟨kept, retained, same, earlier⟩ := firstReportingCuts_earlier (seen := [])
    (objectFailureCandidates_ordered _ _ _) included (by simp)
  have identity : kept = (kept.1, occurrence) := Prod.ext rfl same
  exact mem_failedBefore (identity ▸ retained) earlier

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
