import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveRecordingCorrespondence

/-! Primitive recording regressions and exact general construction targets.
The earlier nullable fault is retained through fatal settlement and bubbling;
neither cancellation nor another propagation can forget or re-record it. -/

namespace AlternativeRecordingChecks

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

private def prior : Report ResponseValue := .fault [7, 0] (.ok (.null, 1))
private def fatal : Report ResponseValue := .fault [7, 1] (.error 1)
private def joined := Report.combine (fun left _ => left) prior fatal
private def rebubbled := (joined.catchNull id).nonNull [7]

private theorem recording : ReportRecording rebubbled rebubbled := by
  have head := ReportCutTrace.fault [7, 0] (.ok (.null, 1) : Result ResponseValue)
  have tail := ReportCutTrace.fault [7, 1] (.error 1 : Result ResponseValue)
  exact ((ReportCutTrace.combine (fun left _ => left) head tail).catchNull id
          |>.nonNull [7]).recording
    (by decide)

example : rebubbled.outcome = .error 2 := rfl

example
    : ∃ actions omitted,
        OriginReplay rebubbled.origins {} actions
          ⟨rebubbled.origins, rebubbled.origins, omitted⟩
        ∧ actions.filterMap OriginAction.recorded? = [([7, 0], 0), ([7, 1], 0)] := by
  obtain ⟨actions, omitted, history, _, _⟩ := recording
  refine ⟨actions ++ [.settle rebubbled.origins], omitted, history, ?_⟩
  have records : (actions ++ [OriginAction.settle rebubbled.origins]).filterMap OriginAction.recorded?
      = rebubbled.origins := by simpa only [List.nil_append] using (history.recorded_trace).symm
  exact records.trans (by decide)

private def alreadyRecorded : OriginLedger :=
  ⟨[([7, 0], 0), ([7, 1], 0)], [([7, 0], 0), ([7, 1], 0)], []⟩

-- A legal continuation cannot remove a previously recorded error.
example (actions : List OriginAction) (after : OriginLedger)
    (history : OriginReplay rebubbled.origins alreadyRecorded actions after)
    : ([7, 0], 0) ∈ after.recorded :=
  history.preserves_record (by decide)

-- A prior record cannot be justified away by calling its cone cancelled.
example (after : OriginLedger)
    : ¬OriginStep rebubbled.origins alreadyRecorded
        (.cancel ⟨[7, 0], 1⟩ [([7, 0], 0)]) after := by
  intro step
  exact step.cancel_excludes_records
    (by intros; assumption)
    ([7, 0], 0)
    (by simp)
    (by decide)

-- Bubbling has no primitive record action, and a second record is forbidden.
example : OriginAction.recorded? (.bubble rebubbled.origins) = none := rfl

example (after : OriginLedger)
    : ¬OriginStep rebubbled.origins alreadyRecorded (.record ([7, 0], 0)) after := by
  intro step
  cases step with
  | record origin member started fresh => exact fresh (by decide)

example : RecursiveRecordingCorrespondence := recursiveRecordingCorrespondence_holds

#print axioms recursiveRecordingCorrespondence_holds
#print axioms ReportCutTrace.recording
#print axioms OriginReplay.omission_boundary
#print axioms OriginReplay.preserves_record
#print axioms OriginReplay.recorded_trace
#print axioms ReportRecording.observation
#print axioms recording

end AlternativeRecordingChecks
