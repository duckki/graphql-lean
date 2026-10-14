import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginRefinement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginScopes

/-! Exact ghost origin differences and the fatal sibling-cut composition edge.
Missing eager references are identified by their primitive identities, not just by
the count gap. A child omission and an unexecuted sibling cone remain distinct.
This module does not derive a whole-run cut trace or native cancellation evidence. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open ScheduledErrors (countedErrors)

def omittedOrigins (cut eager : List Origin) : List Origin :=
  eager.filter (fun origin => !cut.contains origin)

theorem mem_omittedOrigins {origin : Origin} {cut eager : List Origin}
    : origin ∈ omittedOrigins cut eager ↔ origin ∈ eager ∧ origin ∉ cut := by
  simp [omittedOrigins]

theorem omittedOrigins_self (origins : List Origin)
    : omittedOrigins origins origins = [] := by
  simp [omittedOrigins, List.filter_eq_nil_iff]

theorem append_omitted_within
    {cutLeft eagerLeft cutRight eagerRight : List Origin}
    {allowedLeft allowedRight : Origin → Prop}
    (head : ∀ origin ∈ omittedOrigins cutLeft eagerLeft, allowedLeft origin)
    (tail : ∀ origin ∈ omittedOrigins cutRight eagerRight, allowedRight origin)
    : ∀ origin ∈ omittedOrigins (cutLeft ++ cutRight) (eagerLeft ++ eagerRight),
        allowedLeft origin ∨ allowedRight origin := by
  intro origin member
  obtain ⟨present, absent⟩ := mem_omittedOrigins.mp member
  rcases List.mem_append.mp present with earlier | later
  · exact Or.inl (head origin (mem_omittedOrigins.mpr
      ⟨earlier, fun inside => absent (List.mem_append_left _ inside)⟩))
  · exact Or.inr (tail origin (mem_omittedOrigins.mpr
      ⟨later, fun inside => absent (List.mem_append_right _ inside)⟩))

/-- Combining reports cannot introduce another explanation for missing origins.
The missing parent identity must already be missing from the corresponding child. -/
theorem combine_omitted_within (f : α → β → γ)
    {cutLeft eagerLeft : Report α} {cutRight eagerRight : Report β}
    {allowedLeft allowedRight : Origin → Prop}
    (head
      : ∀ origin ∈ omittedOrigins cutLeft.origins eagerLeft.origins, allowedLeft origin)
    (tail
      : ∀ origin ∈ omittedOrigins cutRight.origins eagerRight.origins,
          allowedRight origin)
    : ∀ origin ∈
        omittedOrigins (Report.combine f cutLeft cutRight).origins
          (Report.combine f eagerLeft eagerRight).origins,
        allowedLeft origin ∨ allowedRight origin :=
  append_omitted_within head tail

/-- The fresh wrapper origin is introduced on both sides or neither; it is not
another omitted child error. Positive-error bubbling keeps the same missing identities. -/
theorem ReportRefines.nonNull_omitted (route : List Nat)
    {cut eager : Report ResponseValue} (known : ReportRefines cut eager)
    : omittedOrigins (cut.nonNull route).origins (eager.nonNull route).origins
      = omittedOrigins cut.origins eager.origins := by
  obtain ⟨cut, cutOrigins, cutAccounts⟩ := cut
  obtain ⟨eager, eagerOrigins, eagerAccounts⟩ := eager
  rcases cut with errors | ⟨value, errors⟩
  <;> rcases eager with eagerErrors | ⟨eagerValue, eagerErrors⟩
  <;> simp_all only [ReportRefines, ScheduledErrors.ResultRefines,
    ScheduledErrors.SameData, countedErrors, false_and]
  · rfl
  · obtain ⟨⟨rfl, bounded, zero⟩, origins⟩ := known
    cases value <;> cases errors <;> cases eagerErrors <;>
      simp_all [Report.nonNull, Report.fault, omittedOrigins]
    have cutEmpty : cutOrigins = [] := List.length_eq_zero_iff.mp cutAccounts
    have eagerEmpty : eagerOrigins = [] := List.length_eq_zero_iff.mp eagerAccounts
    rw [cutEmpty, eagerEmpty]
    simp [List.filter_eq_nil_iff]

theorem omittedOrigins_partition {cut eager : List Origin}
    (coverage : cut.Sublist eager) (unique : eager.Nodup)
    : cut.length + (omittedOrigins cut eager).length = eager.length := by
  obtain ⟨missing, permutation⟩ := coverage.exists_perm_append
  have disjoint := (List.nodup_append.mp (permutation.nodup unique)).2.2
  have retained : cut.filter (fun origin => !cut.contains origin) = [] := by
    simp [List.filter_eq_nil_iff]
  have omitted : missing.filter (fun origin => !cut.contains origin) = missing := by
    apply List.filter_eq_self.mpr
    intro origin member
    have outside : origin ∉ cut := by
      intro present
      exact disjoint origin present origin member rfl
    simpa using outside
  have filtered := List.Perm.filter (fun origin => !cut.contains origin) permutation
  simp only [List.filter_append, retained, omitted, List.nil_append] at filtered
  simpa only [omittedOrigins, List.length_append, filtered.length_eq]
    using permutation.length_eq.symm

/-- The error-count gap equals exactly the omitted unique originating references.
This accounts for a given coverage proof; it does not justify those omissions. -/
theorem ReportRefines.omitted_count {cut eager : Report α}
    (known : ReportRefines cut eager) (unique : eager.origins.Nodup)
    : countedErrors cut.outcome + (omittedOrigins cut.origins eager.origins).length
      = countedErrors eager.outcome := by
  simpa only [cut.accounts, eager.accounts] using omittedOrigins_partition known.2 unique

theorem ReportRefines.no_new_origins {cut eager : Report α}
    (known : ReportRefines cut eager) {origin : Origin} (present : origin ∈ cut.origins)
    : origin ∈ eager.origins :=
  known.2.subset present

/-- Every missing parent reference is either already missing inside the actual
head comparison or belongs to the unexecuted tail. Disjoint call cones make this
an exact classification, so a preceding head error cannot be blamed on the tail. -/
theorem fatal_cut_omitted (f : α → β → γ) (wrap : α → γ)
    {cut eagerHead : Report α} (eagerTail : Report β) (route : List Nat)
    (headScope : Scoped (route ++ [0]) cut.origins)
    (tailScope : Scoped (route ++ [1]) eagerTail.origins)
    : omittedOrigins (cut.map wrap).origins (Report.combine f eagerHead eagerTail).origins
      = omittedOrigins cut.origins eagerHead.origins ++ eagerTail.origins := by
  have tailOutside : eagerTail.origins.filter (fun origin => !cut.origins.contains origin)
      = eagerTail.origins := by
    apply List.filter_eq_self.mpr
    intro origin member
    have outside : origin ∉ cut.origins := by
      intro present
      exact Scoped.separated route origin.1 (headScope.within origin present)
        (tailScope.within origin member)
    simpa using outside
  simp only [omittedOrigins, Report.map, Report.combine, List.filter_append, tailOutside]

/-- The new sibling omissions are in its precise structural cone. This edge needs
an actual child omission law; it does not assume or prove native cancellation. -/
theorem fatal_cut_omitted_within (f : α → β → γ) (wrap : α → γ)
    {cut eagerHead : Report α} (eagerTail : Report β) (route : List Nat)
    {allowed : Origin → Prop}
    (headScope : Scoped (route ++ [0]) cut.origins)
    (tailScope : Scoped (route ++ [1]) eagerTail.origins)
    (childOmitted
      : ∀ origin ∈ omittedOrigins cut.origins eagerHead.origins, allowed origin)
    : ∀ origin ∈
        omittedOrigins (cut.map wrap).origins
          (Report.combine f eagerHead eagerTail).origins,
        allowed origin ∨ (route ++ [1]).IsPrefix origin.1 := by
  rw [fatal_cut_omitted f wrap eagerTail route headScope tailScope]
  intro origin member
  rcases List.mem_append.mp member with earlier | later
  · exact Or.inl (childOmitted origin earlier)
  · exact Or.inr (tailScope.within origin later)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
