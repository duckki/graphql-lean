import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReportingCutSelection

/-! Report-cause availability cuts retain actual failure-completion output positions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Choose an exact aggregate explanation when source provenance supplies one.
This finite witness is proof evidence; no cause list is added to a runtime group or notice. -/
noncomputable def groupReportSourceParts (work : Execution.Work)
    (inputs : List GraphEvent) (ref : NodeRef) (errors : Nat)
    : List (Occurrence × Nat) := by
  classical
  exact if evidence : GroupFailureSources work inputs ref errors then Classical.choose evidence
    else []

/-- Chosen parts retain their exact total, distinct identities and genuine source payloads. -/
theorem groupReportSourceParts_spec {work inputs ref errors}
    (sources : GroupFailureSources work inputs ref errors)
    : groupReportSourceParts work inputs ref errors ≠ []
      ∧ ((groupReportSourceParts work inputs ref errors).map Prod.fst).Nodup
      ∧ ((groupReportSourceParts work inputs ref errors).map Prod.snd).sum = errors
      ∧ ∀ occurrence count,
          (occurrence, count) ∈ groupReportSourceParts work inputs ref errors
          → GraphEvent.taskFailure occurrence count ∈ inputs
            ∧ ∃ owners producer path,
                TaskAt work occurrence owners producer (.object path (.error count))
                ∧ ref ∈ owners := by
  classical
  unfold groupReportSourceParts
  split
  · exact Classical.choose_spec sources
  · contradiction

/-- One failed group supplies reporting candidates at its own completion cut. -/
noncomputable def reportCutsAt (work : Execution.Work) (inputs : List GraphEvent)
    (cut : Nat)
    : WorkQueueEvent → FailureCuts
  | .groupFailure group errors =>
      (groupReportSourceParts work inputs group.ref errors).map
        (fun part => (cut, part.1))
  | _ => []

/-- Every local report candidate keeps exactly the supplied output cut. -/
theorem reportCutsAt_cut (work : Execution.Work) (inputs : List GraphEvent)
    (cut : Nat) (event : WorkQueueEvent)
    : ∀ entry ∈ reportCutsAt work inputs cut event, entry.1 = cut := by
  intro entry member
  cases event <;> simp only [reportCutsAt, List.not_mem_nil] at member
  obtain ⟨part, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Collect reporting candidates at actual atomic output positions, without moving events. -/
noncomputable def groupReportCandidateCuts (work : Execution.Work)
    (inputs : List GraphEvent) (offset : Nat)
    : List WorkQueueEvent → FailureCuts
  | [] => []
  | event :: rest =>
      reportCutsAt work inputs offset event
      ++ groupReportCandidateCuts work inputs (offset + 1) rest

/-- Report candidates lie within their original observed output interval. -/
theorem groupReportCandidateCuts_bounds (work : Execution.Work) (inputs : List GraphEvent)
    (offset : Nat) (events : List WorkQueueEvent)
    : ∀ entry ∈ groupReportCandidateCuts work inputs offset events,
        offset ≤ entry.1 ∧ entry.1 ≤ offset + events.length := by
  induction events generalizing offset with
  | nil => simp [groupReportCandidateCuts]
  | cons event rest ih =>
      intro entry member
      rcases List.mem_append.mp member with here | later
      · rw [reportCutsAt_cut work inputs offset event entry here]
        simp
      · have bound := ih (offset + 1) entry later
        simp only [List.length_cons]
        omega

/-- Report candidates are ordered by their unchanged output cuts. -/
theorem groupReportCandidateCuts_ordered (work : Execution.Work)
    (inputs : List GraphEvent) (offset : Nat) (events : List WorkQueueEvent)
    : (groupReportCandidateCuts work inputs offset events).Pairwise
        (fun left right => left.1 ≤ right.1) := by
  induction events generalizing offset with
  | nil => exact .nil
  | cons event rest ih =>
      apply List.pairwise_append.mpr
      refine ⟨?_, ih (offset + 1), ?_⟩
      · apply List.pairwise_of_forall_mem_list
        intro first firstMember second secondMember
        rw [reportCutsAt_cut work inputs offset event first firstMember,
          reportCutsAt_cut work inputs offset event second secondMember]
        exact Nat.le_refl _
      · intro first firstMember second secondMember
        rw [reportCutsAt_cut work inputs offset event first firstMember]
        exact Nat.le_trans (Nat.le_add_right _ _)
          (groupReportCandidateCuts_bounds work inputs (offset + 1) rest second secondMember).1

/-- Every chosen cause is available as a reporting candidate by its own completion event. -/
theorem groupReportCandidateCuts_atReport {work inputs offset events index group errors}
    (selected : events[index]? = some (WorkQueueEvent.groupFailure group errors))
    {part : Occurrence × Nat}
    (member : part ∈ groupReportSourceParts work inputs group.ref errors)
    : (offset + index, part.1) ∈ groupReportCandidateCuts work inputs offset events := by
  induction events generalizing offset index with
  | nil => simp at selected
  | cons event rest ih =>
      cases index with
      | zero =>
          obtain rfl := Option.some.inj selected
          exact List.mem_append_left _ (List.mem_map.mpr ⟨part, member, by simp⟩)
      | succ index =>
          have later := ih (offset := offset + 1) selected
          apply List.mem_append_right
          simpa only [Nat.add_assoc, Nat.add_comm 1 index] using later

/-- Each report candidate identifies the actual completion and one exact chosen cause. -/
theorem groupReportCandidateCuts_origin {work inputs offset events entry}
    (member : entry ∈ groupReportCandidateCuts work inputs offset events)
    : ∃ index group errors count,
        events[index]? = some (WorkQueueEvent.groupFailure group errors)
        ∧ entry.1 = offset + index
        ∧ (entry.2, count) ∈ groupReportSourceParts work inputs group.ref errors := by
  induction events generalizing offset with
  | nil => cases member
  | cons event rest ih =>
      rcases List.mem_append.mp member with here | later
      · cases event <;> simp only [reportCutsAt, List.not_mem_nil] at here
        obtain ⟨part, included, same⟩ := List.mem_map.mp here
        subst entry
        exact ⟨0, _, _, part.2, rfl, by simp, included⟩
      · obtain ⟨index, group, errors, count, selected, cut, cause⟩ := ih later
        refine ⟨index + 1, group, errors, count, selected, ?_, cause⟩
        omega

/-- The first selected reporting cut of every report cause is no later than that report. -/
theorem firstGroupReportCuts_atReport {work inputs events index group errors}
    (selected : events[index]? = some (WorkQueueEvent.groupFailure group errors))
    {part : Occurrence × Nat}
    (member : part ∈ groupReportSourceParts work inputs group.ref errors)
    : ∃ cut,
        (cut, part.1)
          ∈ firstReportingCuts [] (groupReportCandidateCuts work inputs 0 events)
        ∧ cut ≤ index := by
  have raw := groupReportCandidateCuts_atReport (offset := 0) selected member
  obtain ⟨kept, retained, same, earlier⟩ := firstReportingCuts_earlier (seen := [])
    (groupReportCandidateCuts_ordered work inputs 0 events) raw (by simp)
  have identity : kept = (kept.1, part.1) := Prod.ext rfl same
  exact ⟨kept.1, identity ▸ retained, by simpa only [Nat.zero_add] using earlier⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
