import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureEquivalence

/-! Choose informative object-failure cuts without changing executable source handling.
The selection is existential proof evidence about histories, not an additional runtime guard.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A source failure can add a group cause while at least one contributor is uninvalidated.
This concerns group invalidation only; historical cancellation licensing remains separate.
-/
def InformativeFailure (work : Execution.Work) (before : List Occurrence)
    (occurrence : Occurrence)
    : Prop :=
  ∃ owners ref,
    TaskHasOwners work occurrence owners
    ∧ ref ∈ owners
    ∧ ¬GroupInvalidated work before ref

/-- Keep source cuts that add a group cause, retaining their original indices and order.
No source input, queue state, output event, or error count is changed by this proof selection.
-/
noncomputable def selectObjectFailureCuts (work : Execution.Work)
    (before : List Occurrence)
    : FailureCuts → FailureCuts
  | [] => []
  | entry :: rest =>
      letI := Classical.propDecidable (InformativeFailure work before entry.2)
      if InformativeFailure work before entry.2 then
        entry :: selectObjectFailureCuts work (before ++ [entry.2]) rest
      else
        selectObjectFailureCuts work before rest

/-- Every retained cut has an uninvalidated contributor under its exact selected prefix. -/
def InformativeFailureCuts (work : Execution.Work) : List Occurrence → FailureCuts → Prop
  | _, [] => True
  | before, entry :: rest =>
      InformativeFailure work before entry.2
      ∧ InformativeFailureCuts work (before ++ [entry.2]) rest

/-- The selection retains a subsequence, including zero-width settlement boundaries. -/
theorem selectObjectFailureCuts_sublist (work : Execution.Work) (before : List Occurrence)
    (cuts : FailureCuts)
    : (selectObjectFailureCuts work before cuts).Sublist cuts := by
  classical
  induction cuts generalizing before with
  | nil => exact .refl _
  | cons entry rest ih =>
      rw [selectObjectFailureCuts]
      split
      · exact (ih _).cons_cons entry
      · exact (ih _).cons entry

/-- The retained cuts satisfy their proof-side contributor criterion in source order. -/
theorem selectObjectFailureCuts_informative (work : Execution.Work)
    (before : List Occurrence) (cuts : FailureCuts)
    : InformativeFailureCuts work before (selectObjectFailureCuts work before cuts) := by
  classical
  induction cuts generalizing before with
  | nil => trivial
  | cons entry rest ih =>
      rw [selectObjectFailureCuts]
      split
      · exact ⟨‹InformativeFailure work before entry.2›, ih _⟩
      · exact ih _

/-- An ordered split exposes the exact selected predecessors of its next informative cut. -/
theorem InformativeFailureCuts.atCut {work initial before after cut occurrence}
    (informative
      : InformativeFailureCuts work initial (before ++ (cut, occurrence) :: after))
    : InformativeFailure work (initial ++ before.map Prod.snd) occurrence := by
  induction before generalizing initial with
  | nil => simpa only [List.map_nil, List.append_nil] using informative.1
  | cons entry rest ih =>
      simpa only [List.map_cons, List.append_assoc, List.singleton_append]
        using ih informative.2

/-- A rejected candidate adds no group invalidation, even before later source failures.
Witness: replace each use of its direct failure token by the same owner's earlier cause.
This does not assert equality of error sums or license a cancelled settlement.
-/
theorem uninformativeFailure_redundant {work before occurrence}
    (rejected : ¬InformativeFailure work before occurrence) (after : List Occurrence)
    (ref : NodeRef)
    : GroupInvalidated work (before ++ occurrence :: after) ref
      ↔ GroupInvalidated work (before ++ after) ref := by
  classical
  constructor
  · intro failure
    induction failure with
    | @task task owners ref known owner member =>
        rcases List.mem_append.mp member with earlier | later
        · exact .task known owner (List.mem_append_left _ earlier)
        · rcases List.mem_cons.mp later with same | later
          · subst task
            have prior : GroupInvalidated work before ref := by
              apply Classical.byContradiction
              intro healthy
              exact rejected ⟨owners, ref, known, owner, healthy⟩
            exact prior.mono (List.subset_append_left _ _)
          · exact .task known owner (List.mem_append_right _ later)
    | groupDependency known member _ ih => exact .groupDependency known member ih
  · intro failure
    apply failure.mono
    intro task member
    rcases List.mem_append.mp member with earlier | later
    · exact List.mem_append_left _ earlier
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ later)

/-- Removing redundant candidates preserves the complete group-invalidation closure.
Witness: retained cuts extend both histories; skipped cuts are redundant before every
later suffix. Group causality is preserved without identifying the two occurrence lists.
-/
theorem selectObjectFailureCuts_groupInvalidated (work : Execution.Work)
    (before : List Occurrence) (cuts : FailureCuts) (ref : NodeRef)
    : GroupInvalidated work (before ++ cuts.map Prod.snd) ref
      ↔ GroupInvalidated work
          (before ++ (selectObjectFailureCuts work before cuts).map Prod.snd) ref := by
  classical
  induction cuts generalizing before with
  | nil => rfl
  | cons entry rest ih =>
      rw [selectObjectFailureCuts]
      split
      · simpa only [List.map_cons, List.append_assoc, List.singleton_append]
          using ih (before ++ [entry.2])
      · exact (uninformativeFailure_redundant ‹¬InformativeFailure work before entry.2›
          (rest.map Prod.snd) ref).trans (ih before)

/-- The same selection preserves invalidation of taskless ancestor registration records. -/
theorem selectObjectFailureCuts_groupRecordInvalidated (work : Execution.Work)
    (before : List Occurrence) (cuts : FailureCuts) (ref : NodeRef)
    : GroupRecordInvalidated work (before ++ cuts.map Prod.snd) ref
      ↔ GroupRecordInvalidated work
          (before ++ (selectObjectFailureCuts work before cuts).map Prod.snd) ref :=
  groupRecordInvalidated_congr (selectObjectFailureCuts_groupInvalidated work before cuts)
    ref

/-- Selection composes at an exact source prefix, retaining its chosen predecessor list.
Witness: the same contributor criterion is evaluated with the selected prefix on both sides.
-/
theorem selectObjectFailureCuts_append (work : Execution.Work) (initial : List Occurrence)
    (left right : FailureCuts)
    : selectObjectFailureCuts work initial (left ++ right)
      = selectObjectFailureCuts work initial left
        ++ selectObjectFailureCuts work
            (initial ++ (selectObjectFailureCuts work initial left).map Prod.snd)
            right := by
  classical
  induction left generalizing initial with
  | nil => simp [selectObjectFailureCuts]
  | cons entry rest ih =>
      simp only [List.cons_append, selectObjectFailureCuts]
      split
      · simpa only [List.cons_append, List.map_cons, List.append_assoc,
          List.singleton_append, List.nil_append]
          using congrArg (entry :: ·) (ih (initial ++ [entry.2]))
      · exact ih initial

/-- On ordered cuts, selection commutes with restriction to an output boundary.
Witness: a later cut and its entire suffix lie beyond the boundary; earlier cuts use
exactly the same selected predecessor inventory in both traversals.
-/
theorem selectObjectFailureCuts_filterCut (work : Execution.Work)
    (initial : List Occurrence) (cuts : FailureCuts) (bound : Nat)
    (ordered : cuts.Pairwise (fun left right => left.1 ≤ right.1))
    : (selectObjectFailureCuts work initial cuts).filter (fun entry => entry.1 ≤ bound)
      = selectObjectFailureCuts work initial
          (cuts.filter (fun entry => entry.1 ≤ bound)) := by
  classical
  induction cuts generalizing initial with
  | nil => rfl
  | cons entry rest ih =>
      have orderedRest := (List.pairwise_cons.mp ordered).2
      by_cases within : entry.1 ≤ bound
      · simp only [List.filter_cons, decide_eq_true within, ↓reduceIte,
          selectObjectFailureCuts]
        split
        · simpa only [List.filter_cons, decide_eq_true within, ↓reduceIte]
            using congrArg (entry :: ·) (ih _ orderedRest)
        · exact ih _ orderedRest
      · have empty : (entry :: rest).filter (fun entry => entry.1 ≤ bound) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro candidate member
          have lower : entry.1 ≤ candidate.1 := by
            rcases List.mem_cons.mp member with rfl | tail
            · exact Nat.le_refl _
            · exact (List.pairwise_cons.mp ordered).1 candidate tail
          simp only [decide_eq_true_eq]
          omega
        rw [empty, selectObjectFailureCuts]
        apply List.filter_eq_nil_iff.mpr
        intro candidate member
        have raw := (selectObjectFailureCuts_sublist work initial (entry :: rest)).subset member
        have lower : entry.1 ≤ candidate.1 := by
          rcases List.mem_cons.mp raw with rfl | tail
          · exact Nat.le_refl _
          · exact (List.pairwise_cons.mp ordered).1 candidate tail
        simp only [decide_eq_true_eq]
        omega

/-- Selection preserves group invalidation at every actual output boundary.
Witness: restriction commutes with selection, and the finite-prefix closure theorem
then applies to exactly the failures visible at that boundary.
-/
theorem selectObjectFailureCuts_failedBefore_groupInvalidated (work : Execution.Work)
    (initial : List Occurrence) (cuts : FailureCuts) (bound ref : Nat)
    (ordered : cuts.Pairwise (fun left right => left.1 ≤ right.1))
    : GroupInvalidated work (initial ++ failedBefore cuts bound) ref
      ↔ GroupInvalidated work
          (initial ++ failedBefore (selectObjectFailureCuts work initial cuts) bound)
          ref := by
  unfold failedBefore
  rw [selectObjectFailureCuts_filterCut work initial cuts bound ordered]
  exact selectObjectFailureCuts_groupInvalidated work initial _ ref

/-- Taskless registration invalidation is likewise preserved at each output boundary. -/
theorem selectObjectFailureCuts_failedBefore_groupRecordInvalidated
    (work : Execution.Work) (initial : List Occurrence) (cuts : FailureCuts)
    (bound ref : Nat) (ordered : cuts.Pairwise (fun left right => left.1 ≤ right.1))
    : GroupRecordInvalidated work (initial ++ failedBefore cuts bound) ref
      ↔ GroupRecordInvalidated work
          (initial ++ failedBefore (selectObjectFailureCuts work initial cuts) bound)
          ref :=
  groupRecordInvalidated_congr
    (fun key =>
      selectObjectFailureCuts_failedBefore_groupInvalidated work initial cuts
        bound key ordered) ref

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
