import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginAnnotations
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingResultRefinement

/-! Primitive-origin composition for recursively paired completions. The relation
requires actual child origin coverage, not merely smaller aggregate counts. These
conditional edges do not construct the recursive executor comparison or a native
recording history. In particular, subsequence coverage alone does not license omission. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open ScheduledErrors (ResultRefines SameData countedErrors)

-----------------------------------------------------------------------------------------
-- Reports preserve originating references, data/status and error presence together
-----------------------------------------------------------------------------------------

def ReportRefines (cut eager : Report α) : Prop :=
  ResultRefines cut.outcome eager.outcome ∧ cut.origins.Sublist eager.origins

theorem ReportRefines.refl (report : Report α) : ReportRefines report report :=
  ⟨ResultRefines.refl _, List.Sublist.refl _⟩

theorem ReportRefines.combine (f : α → β → γ)
    {left eagerLeft : Report α} {right eagerRight : Report β}
    (head : ReportRefines left eagerLeft) (tail : ReportRefines right eagerRight)
    : ReportRefines (Report.combine f left right)
        (Report.combine f eagerLeft eagerRight) :=
  ⟨head.1.combine f tail.1, head.2.append tail.2⟩

theorem ReportRefines.map (f : α → β) {left right : Report α}
    (known : ReportRefines left right)
    : ReportRefines (left.map f) (right.map f) := by
  refine ⟨?_, known.2⟩
  have payload := known.1.completion_map f
    (left := { result := left.outcome }) (right := { result := right.outcome })
  cases hl : left.outcome <;> cases hr : right.outcome <;>
    simpa only [Completion.map, Completion.error, Report.map, hl, hr] using payload

theorem ReportRefines.catchNull (f : α → ResponseValue) {left right : Report α}
    (known : ReportRefines left right)
    : ReportRefines (left.catchNull f) (right.catchNull f) := by
  refine ⟨?_, known.2⟩
  have payload := known.1.catchNull f
    (left := { result := left.outcome }) (right := { result := right.outcome })
  cases hl : left.outcome <;> cases hr : right.outcome <;>
    simpa only [Completion.catchNull, Report.catchNull, hl, hr] using payload

/-- Zero-error equivalence synchronizes the only branch that mints a new non-null
origin. Positive child faults retain their original references through bubbling. -/
theorem ReportRefines.nonNull (route : List Nat) {left right : Report ResponseValue}
    (known : ReportRefines left right)
    : ReportRefines (left.nonNull route) (right.nonNull route) := by
  refine ⟨?_, ?_⟩
  · have payload := known.1.nonNull
      (left := { result := left.outcome }) (right := { result := right.outcome })
    cases hl : nonNullCompletion left.outcome
    <;> cases hr : nonNullCompletion right.outcome
    <;> simpa only [Report.nonNull_outcome, Completion.nonNull, Completion.error, hl, hr]
      using payload
  · obtain ⟨left, leftOrigins, leftAccounts⟩ := left
    obtain ⟨right, rightOrigins, rightAccounts⟩ := right
    rcases left with errors | ⟨value, errors⟩
    <;> rcases right with eagerErrors | ⟨eagerValue, eagerErrors⟩
    <;> simp_all only [ReportRefines, ResultRefines, SameData, countedErrors, false_and]
    · exact known.2
    · obtain ⟨⟨rfl, bounded, zero⟩, origins⟩ := known
      cases value <;> cases errors <;> cases eagerErrors <;>
        simp_all [Report.nonNull, Report.fault]

/-- A fatal cut propagates the actual head references, rather than allocating a
new primitive at the parent or reconstructing identities from its count. -/
theorem ReportRefines.fatal_cut (f : α → β → γ) (wrap : α → γ)
    {left eagerLeft : Report α} (right : Report β) {errors : Nat}
    (known : ReportRefines left eagerLeft) (fatal : left.outcome = .error errors)
    (positive : 0 < errors)
    : ReportRefines (left.map wrap) (Report.combine f eagerLeft right) := by
  refine ⟨?_, List.sublist_append_of_sublist_left known.2⟩
  have payload := known.1
  rw [fatal] at payload
  simpa only [Report.map, fatal, Report.combine]
    using payload.fatal_cut f right.outcome positive

-----------------------------------------------------------------------------------------
-- Retained task/item reports are compared at the same structural positions
-----------------------------------------------------------------------------------------

mutual
  /-- Origin-only structural relation. Delivery metadata is deliberately left to
  the existing WorkRefines/key-map certificate, not silently equated here. -/
  inductive WorkOriginsRefine : RecordedWork → RecordedWork → Prop where
    | empty : WorkOriginsRefine .empty .empty
    | combine {left right eagerLeft eagerRight} (head : WorkOriginsRefine left eagerLeft)
      (tail : WorkOriginsRefine right eagerRight)
      : WorkOriginsRefine (.combine left right) (.combine eagerLeft eagerRight)
    | executionGroup
      {groups eagerGroups path eagerPath report eagerReport children eagerChildren}
      (payload : ReportRefines report.toReport eagerReport.toReport)
      (nested : WorkOriginsRefine children eagerChildren)
      : WorkOriginsRefine (.executionGroup groups path report children)
          (.executionGroup eagerGroups eagerPath eagerReport eagerChildren)
    | stream {node eagerNode items eagerItems}
      (nested : ItemOriginsRefine items eagerItems)
      : WorkOriginsRefine (.stream node items) (.stream eagerNode eagerItems)

  inductive ItemOriginsRefine
      : List (RecordedOutcome ResponseValue × RecordedWork)
        → List (RecordedOutcome ResponseValue × RecordedWork) → Prop where
    | nil : ItemOriginsRefine [] []
    | cons {report eagerReport children eagerChildren rest eagerRest}
      (payload : ReportRefines report.toReport eagerReport.toReport)
      (nested : WorkOriginsRefine children eagerChildren)
      (tail : ItemOriginsRefine rest eagerRest)
      : ItemOriginsRefine ((report, children) :: rest)
          ((eagerReport, eagerChildren) :: eagerRest)
end

mutual
  theorem WorkOriginsRefine.origins {left right} (known : WorkOriginsRefine left right)
      : left.origins.Sublist right.origins := by
    cases known with
    | empty => exact .refl _
    | combine head tail =>
        simpa only [RecordedWork.origins] using head.origins.append tail.origins
    | executionGroup payload nested =>
        simpa only [RecordedWork.origins] using payload.2.append nested.origins
    | stream nested => simpa only [RecordedWork.origins] using nested.origins
  termination_by sizeOf left

  theorem ItemOriginsRefine.origins {left right} (known : ItemOriginsRefine left right)
      : (left.flatMap (fun item => item.1.origins ++ item.2.origins)).Sublist
          (right.flatMap (fun item => item.1.origins ++ item.2.origins)) := by
    cases known with
    | nil => exact .refl _
    | cons payload nested tail =>
        exact (payload.2.append nested.origins).append tail.origins
  termination_by sizeOf left
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def CompletionOriginsRefine (left right : RecordedCompletion α) : Prop :=
  ReportRefines left.report right.report ∧ WorkOriginsRefine left.work right.work

theorem CompletionOriginsRefine.origins {left right : RecordedCompletion α}
    (known : CompletionOriginsRefine left right)
    : left.origins.Sublist right.origins :=
  known.1.2.append known.2.origins

theorem CompletionOriginsRefine.pure (value : α)
    : CompletionOriginsRefine (.pure value) (.pure value) :=
  ⟨ReportRefines.refl _, .empty⟩

theorem CompletionOriginsRefine.fault (route : List Nat) (outcome : Result α)
    : CompletionOriginsRefine (.fault route outcome) (.fault route outcome) :=
  ⟨ReportRefines.refl _, .empty⟩

theorem CompletionOriginsRefine.combine (f : α → β → γ)
    {left eagerLeft : RecordedCompletion α} {right eagerRight : RecordedCompletion β}
    (head : CompletionOriginsRefine left eagerLeft)
    (tail : CompletionOriginsRefine right eagerRight)
    : CompletionOriginsRefine (RecordedCompletion.combine f left right)
        (RecordedCompletion.combine f eagerLeft eagerRight) := by
  have payload := head.1.combine f tail.1
  have agreement := payload.1.1
  cases hl : (Report.combine f left.report right.report).outcome
  <;> cases hr : (Report.combine f eagerLeft.report eagerRight.report).outcome
  <;> simp_all only [SameData]
  <;> simp only [CompletionOriginsRefine, RecordedCompletion.combine, hl, hr]
  · exact ⟨payload, .empty⟩
  · exact ⟨payload, .combine head.2 tail.2⟩

theorem CompletionOriginsRefine.map (f : α → β) {left right : RecordedCompletion α}
    (known : CompletionOriginsRefine left right)
    : CompletionOriginsRefine (left.map f) (right.map f) := by
  have agreement := known.1.1.1
  cases hl : left.report.outcome <;> cases hr : right.report.outcome
  <;> simp_all only [SameData]
  <;> simp only [CompletionOriginsRefine, RecordedCompletion.map, hl, hr]
  · exact ⟨known.1.map f, .empty⟩
  · exact ⟨known.1.map f, known.2⟩

theorem CompletionOriginsRefine.catchNull (f : α → ResponseValue)
    {left right : RecordedCompletion α} (known : CompletionOriginsRefine left right)
    : CompletionOriginsRefine (left.catchNull f) (right.catchNull f) := by
  have agreement := known.1.1.1
  cases hl : left.report.outcome <;> cases hr : right.report.outcome
  <;> simp_all only [SameData]
  <;> simp only [CompletionOriginsRefine, RecordedCompletion.catchNull, hl, hr]
  · exact ⟨known.1.catchNull f, .empty⟩
  · exact ⟨known.1.catchNull f, known.2⟩

theorem CompletionOriginsRefine.nonNull (route : List Nat)
    {left right : RecordedCompletion ResponseValue}
    (known : CompletionOriginsRefine left right)
    : CompletionOriginsRefine (left.nonNull route) (right.nonNull route) := by
  have payload := known.1.nonNull route
  have agreement := payload.1.1
  cases hl : (left.report.nonNull route).outcome
  <;> cases hr : (right.report.nonNull route).outcome
  <;> simp_all only [SameData]
  <;> simp only [CompletionOriginsRefine, RecordedCompletion.nonNull, hl, hr]
  · exact ⟨payload, .empty⟩
  · exact ⟨payload, known.2⟩

/-- A parent fatal cut needs only the retained head report. Both policies discard
future Work, while the cut keeps every head reference and skips the eager suffix. -/
theorem CompletionOriginsRefine.fatal_cut (f : α → β → γ) (wrap : α → γ)
    {left eagerLeft : RecordedCompletion α} (right : RecordedCompletion β) {errors : Nat}
    (known : ReportRefines left.report eagerLeft.report)
    (fatal : left.report.outcome = .error errors) (positive : 0 < errors)
    : CompletionOriginsRefine (left.map wrap)
        (RecordedCompletion.combine f eagerLeft right) := by
  have payload := known.fatal_cut f wrap right.report fatal positive
  have agreement := known.1.1
  rw [fatal] at agreement
  cases eagerFatal : eagerLeft.report.outcome with
  | error count =>
      cases later : right.report.outcome <;>
        simp only [CompletionOriginsRefine, RecordedCompletion.map,
          RecordedCompletion.combine, Report.combine, fatal, eagerFatal, later, Result.combine]
      all_goals simp only [Report.combine, eagerFatal, later, Result.combine] at payload
      all_goals exact ⟨payload, .empty⟩
  | ok value => simp [eagerFatal, SameData] at agreement

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
