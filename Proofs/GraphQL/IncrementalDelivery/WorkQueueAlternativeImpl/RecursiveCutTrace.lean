import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralReachedCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.EagerOriginUniqueness

/-! Proof-only control-flow evidence for the actual paired recursive executors.
Only a fatal sibling branch creates a cut. Primitive faults, aggregation and
bubbling remain separate constructors; future reports have separate derivations.
The root construction, not a native/environment premise, supplies this evidence. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution

inductive ReportCutTrace : {α : Type} → Report α → Report α → Prop where
  | pure (value : α) : ReportCutTrace (.pure value) (.pure value)
  | fault (route : List Nat) (outcome : Result α)
    : ReportCutTrace (.fault route outcome) (.fault route outcome)
  | combine (f : α → β → γ) {left eagerLeft : Report α} {right eagerRight : Report β}
    (head : ReportCutTrace left eagerLeft) (tail : ReportCutTrace right eagerRight)
    : ReportCutTrace (Report.combine f left right) (Report.combine f eagerLeft eagerRight)
  | map (f : α → β) {cut eager : Report α} (child : ReportCutTrace cut eager)
    : ReportCutTrace (cut.map f) (eager.map f)
  | catchNull (f : α → ResponseValue) {cut eager : Report α}
    (child : ReportCutTrace cut eager)
    : ReportCutTrace (cut.catchNull f) (eager.catchNull f)
  | nonNull (route : List Nat) {cut eager : Report ResponseValue}
    (child : ReportCutTrace cut eager)
    : ReportCutTrace (cut.nonNull route) (eager.nonNull route)
  | fatalCut (f : α → β → γ) (wrap : α → γ) {cut eagerHead : Report α}
    (eagerTail : Report β) (route : List Nat) (errors : Nat)
    (head : ReportCutTrace cut eagerHead) (fatal : cut.outcome = .error errors)
    (positive : 0 < errors) (headScope : Scoped (route ++ [0]) cut.origins)
    (tailScope : Scoped (route ++ [1]) eagerTail.origins)
    : ReportCutTrace (cut.map wrap) (Report.combine f eagerHead eagerTail)

theorem ReportCutTrace.refines {cut eager : Report α} (trace : ReportCutTrace cut eager)
    : ReportRefines cut eager := by
  induction trace with
  | pure value => exact .refl _
  | fault route outcome => exact .refl _
  | combine f head tail ihHead ihTail => exact ihHead.combine f ihTail
  | map f child ih => exact ih.map f
  | catchNull f child ih => exact ih.catchNull f
  | nonNull route child ih => exact ih.nonNull route
  | fatalCut f wrap eagerTail route errors head fatal positive headScope tailScope ih =>
      exact ih.fatal_cut f wrap eagerTail fatal positive

/-- Every site in the constructed derivation is a positive fatal sibling cut;
every missing identity is inside one of its skipped suffix cones. -/
def CutAccounted (cut eager : List Origin) (sites : List SiblingCut) : Prop :=
  (∀ origin ∈ omittedOrigins cut eager, WithinCuts sites origin)
  ∧ ∀ site ∈ sites, 0 < site.errors

theorem CutAccounted.append {cut eager rest eagerRest sites restSites}
    (head : CutAccounted cut eager sites) (tail : CutAccounted rest eagerRest restSites)
    : CutAccounted (cut ++ rest) (eager ++ eagerRest) (sites ++ restSites) := by
  refine ⟨?_, ?_⟩
  · intro origin member
    rcases append_omitted_within head.1 tail.1 origin member with earlier | later
    · exact earlier.left
    · exact later.right
  · intro site member
    rcases List.mem_append.mp member with earlier | later
    · exact head.2 site earlier
    · exact tail.2 site later

theorem ReportCutTrace.accounting {cut eager : Report α}
    (trace : ReportCutTrace cut eager)
    : ∃ sites, CutAccounted cut.origins eager.origins sites := by
  induction trace with
  | pure value => exact ⟨[], by simp [CutAccounted, omittedOrigins_self]⟩
  | fault route outcome => exact ⟨[], by simp [CutAccounted, omittedOrigins_self]⟩
  | combine f head tail ihHead ihTail =>
      obtain ⟨sites, known⟩ := ihHead
      obtain ⟨rest, later⟩ := ihTail
      exact ⟨sites ++ rest, known.append later⟩
  | map f child ih => exact ih
  | catchNull f child ih => exact ih
  | nonNull route child ih =>
      obtain ⟨sites, known⟩ := ih
      refine ⟨sites, ?_, known.2⟩
      rw [child.refines.nonNull_omitted route]
      exact known.1
  | fatalCut f wrap eagerTail route errors head fatal positive headScope tailScope ih =>
      obtain ⟨sites, known⟩ := ih
      refine ⟨sites ++ [⟨route ++ [1], errors⟩], ?_, ?_⟩
      · intro origin member
        rcases fatal_cut_omitted_within f wrap eagerTail route headScope tailScope known.1 origin member
          with earlier | later
        · exact earlier.left
        · exact ⟨⟨route ++ [1], errors⟩, by simp, later⟩
      · intro site member
        rcases List.mem_append.mp member with earlier | later
        · exact known.2 site earlier
        · have same := List.mem_singleton.mp later
          subst site
          exact positive

mutual
  inductive WorkCutTrace : RecordedWork → RecordedWork → Prop where
    | empty : WorkCutTrace .empty .empty
    | combine {left eagerLeft right eagerRight}
      (head : WorkCutTrace left eagerLeft) (tail : WorkCutTrace right eagerRight)
      : WorkCutTrace (.combine left right) (.combine eagerLeft eagerRight)
    | executionGroup
      {groups eagerGroups path eagerPath report eagerReport children eagerChildren}
      (head : ReportCutTrace report eagerReport)
      (nested : WorkCutTrace children eagerChildren)
      : WorkCutTrace (.executionGroup groups path report children)
          (.executionGroup eagerGroups eagerPath eagerReport eagerChildren)
    | stream {node eagerNode items eagerItems} (nested : ItemsCutTrace items eagerItems)
      : WorkCutTrace (.stream node items) (.stream eagerNode eagerItems)

  inductive ItemsCutTrace
      : List (Report ResponseValue × RecordedWork)
        → List (Report ResponseValue × RecordedWork) → Prop where
    | nil : ItemsCutTrace [] []
    | cons {report eagerReport children eagerChildren rest eagerRest}
      (head : ReportCutTrace report eagerReport)
      (nested : WorkCutTrace children eagerChildren) (tail : ItemsCutTrace rest eagerRest)
      : ItemsCutTrace ((report, children) :: rest)
          ((eagerReport, eagerChildren) :: eagerRest)
end

mutual
  theorem WorkCutTrace.refines {cut eager} (trace : WorkCutTrace cut eager)
      : WorkOriginsRefine cut eager := by
    cases trace with
    | empty => exact .empty
    | combine head tail => exact .combine head.refines tail.refines
    | executionGroup head nested => exact .executionGroup head.refines nested.refines
    | stream nested => exact .stream nested.refines
  termination_by sizeOf cut

  theorem ItemsCutTrace.refines {cut eager} (trace : ItemsCutTrace cut eager)
      : ItemOriginsRefine cut eager := by
    cases trace with
    | nil => exact .nil
    | cons head nested tail => exact .cons head.refines nested.refines tail.refines
  termination_by sizeOf cut
  decreasing_by all_goals simp_wf; omega
end

mutual
  theorem WorkCutTrace.accounting {cut eager} (trace : WorkCutTrace cut eager)
      : ∃ sites, CutAccounted cut.origins eager.origins sites := by
    cases trace with
    | empty =>
        exact ⟨[], by simp [CutAccounted, RecordedWork.origins, omittedOrigins_self]⟩
    | combine head tail =>
        obtain ⟨sites, known⟩ := head.accounting
        obtain ⟨rest, later⟩ := tail.accounting
        exact ⟨
          sites ++ rest,
          by simpa only [RecordedWork.origins] using known.append later
        ⟩
    | executionGroup head nested =>
        obtain ⟨sites, known⟩ := head.accounting
        obtain ⟨rest, later⟩ := nested.accounting
        exact ⟨
          sites ++ rest,
          by simpa only [RecordedWork.origins] using known.append later
        ⟩
    | stream nested =>
        simpa only [RecordedWork.origins, itemOrigins] using nested.accounting
  termination_by sizeOf cut

  theorem ItemsCutTrace.accounting {cut eager} (trace : ItemsCutTrace cut eager)
      : ∃ sites, CutAccounted (itemOrigins cut) (itemOrigins eager) sites := by
    cases trace with
    | nil => exact ⟨[], by simp [CutAccounted, itemOrigins, omittedOrigins_self]⟩
    | cons head nested tail =>
        obtain ⟨sites, known⟩ := head.accounting
        obtain ⟨nestedSites, nestedKnown⟩ := nested.accounting
        obtain ⟨rest, later⟩ := tail.accounting
        exact ⟨(sites ++ nestedSites) ++ rest, (known.append nestedKnown).append later⟩
  termination_by sizeOf cut
  decreasing_by all_goals simp_wf; omega
end

def CompletionCutTrace (cut eager : RecordedCompletion α) : Prop :=
  ReportCutTrace cut.report eager.report ∧ WorkCutTrace cut.work eager.work

theorem CompletionCutTrace.refines {cut eager : RecordedCompletion α}
    (trace : CompletionCutTrace cut eager)
    : CompletionOriginsRefine cut eager :=
  ⟨trace.1.refines, trace.2.refines⟩

theorem CompletionCutTrace.pure (value : α)
    : CompletionCutTrace (.pure value) (.pure value) :=
  ⟨.pure value, .empty⟩

theorem CompletionCutTrace.fault (route : List Nat) (outcome : Result α)
    : CompletionCutTrace (.fault route outcome) (.fault route outcome) :=
  ⟨.fault route outcome, .empty⟩

theorem CompletionCutTrace.combine (f : α → β → γ) {left eagerLeft : RecordedCompletion α}
    {right eagerRight : RecordedCompletion β} (head : CompletionCutTrace left eagerLeft)
    (tail : CompletionCutTrace right eagerRight)
    : CompletionCutTrace (RecordedCompletion.combine f left right)
        (RecordedCompletion.combine f eagerLeft eagerRight) := by
  have payload := ReportCutTrace.combine f head.1 tail.1
  have agreement := payload.refines.1.1
  cases hl : (Report.combine f left.report right.report).outcome
  <;> cases hr : (Report.combine f eagerLeft.report eagerRight.report).outcome
  <;> simp_all only [ScheduledErrors.SameData]
  <;> simp only [CompletionCutTrace, RecordedCompletion.combine, hl, hr]
  · exact ⟨payload, .empty⟩
  · exact ⟨payload, .combine head.2 tail.2⟩

theorem CompletionCutTrace.map (f : α → β) {left right : RecordedCompletion α}
    (known : CompletionCutTrace left right)
    : CompletionCutTrace (left.map f) (right.map f) := by
  have agreement := known.1.refines.1.1
  cases hl : left.report.outcome <;> cases hr : right.report.outcome
  <;> simp_all only [ScheduledErrors.SameData]
  <;> simp only [CompletionCutTrace, RecordedCompletion.map, hl, hr]
  · exact ⟨known.1.map f, .empty⟩
  · exact ⟨known.1.map f, known.2⟩

theorem CompletionCutTrace.catchNull (f : α → ResponseValue)
    {left right : RecordedCompletion α} (known : CompletionCutTrace left right)
    : CompletionCutTrace (left.catchNull f) (right.catchNull f) := by
  have agreement := known.1.refines.1.1
  cases hl : left.report.outcome <;> cases hr : right.report.outcome
  <;> simp_all only [ScheduledErrors.SameData]
  <;> simp only [CompletionCutTrace, RecordedCompletion.catchNull, hl, hr]
  · exact ⟨known.1.catchNull f, .empty⟩
  · exact ⟨known.1.catchNull f, known.2⟩

theorem CompletionCutTrace.nonNull (route : List Nat)
    {left right : RecordedCompletion ResponseValue}
    (known : CompletionCutTrace left right)
    : CompletionCutTrace (left.nonNull route) (right.nonNull route) := by
  have payload := ReportCutTrace.nonNull route known.1
  have agreement := payload.refines.1.1
  cases hl : (left.report.nonNull route).outcome
  <;> cases hr : (right.report.nonNull route).outcome
  <;> simp_all only [ScheduledErrors.SameData]
  <;> simp only [CompletionCutTrace, RecordedCompletion.nonNull, hl, hr]
  · exact ⟨payload, .empty⟩
  · exact ⟨payload, known.2⟩

theorem CompletionCutTrace.fatal_cut (f : α → β → γ) (wrap : α → γ)
    {left eagerLeft : RecordedCompletion α} (right : RecordedCompletion β)
    (route : List Nat) {errors : Nat} (head : ReportCutTrace left.report eagerLeft.report)
    (fatal : left.report.outcome = .error errors) (positive : 0 < errors)
    (headScope : Scoped (route ++ [0]) left.report.origins)
    (tailScope : Scoped (route ++ [1]) right.report.origins)
    : CompletionCutTrace (left.map wrap)
        (RecordedCompletion.combine f eagerLeft right) := by
  have payload := ReportCutTrace.fatalCut f wrap right.report route errors head fatal positive headScope tailScope
  have agreement := head.refines.1.1
  rw [fatal] at agreement
  cases eagerFatal : eagerLeft.report.outcome with
  | error count =>
      cases later : right.report.outcome <;>
        simp only [CompletionCutTrace, RecordedCompletion.map, RecordedCompletion.combine,
          Report.combine, fatal, eagerFatal, later, Result.combine]
      all_goals simp only [Report.combine, eagerFatal, later, Result.combine] at payload
      all_goals exact ⟨payload, .empty⟩
  | ok value => simp [eagerFatal, ScheduledErrors.SameData] at agreement

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
