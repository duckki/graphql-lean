import GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! Keep the first availability cut of each failed occurrence without changing runtime replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Retain each reporting occurrence at its first candidate cut.
`seen` is proof-side recursion state, not an implementation cache or source requirement. -/
noncomputable def firstReportingCuts (seen : List Occurrence) (cuts : FailureCuts)
    : FailureCuts := by
  classical
  exact match cuts with
    | [] => []
    | entry :: rest =>
        if entry.2 ∈ seen then firstReportingCuts seen rest
        else entry :: firstReportingCuts (entry.2 :: seen) rest
termination_by cuts.length

/-- First-occurrence selection preserves the original candidate order and cut positions. -/
theorem firstReportingCuts_sublist (seen : List Occurrence) (cuts : FailureCuts)
    : (firstReportingCuts seen cuts).Sublist cuts := by
  classical
  induction cuts generalizing seen with
  | nil => simp [firstReportingCuts]
  | cons entry rest ih =>
      simp only [firstReportingCuts]
      split
      · exact (ih seen).cons entry
      · exact (ih (entry.2 :: seen)).cons_cons entry

/-- Selected entries never repeat an occurrence already retained before this recursion. -/
theorem firstReportingCuts_excludes (seen : List Occurrence) (cuts : FailureCuts)
    : ∀ entry ∈ firstReportingCuts seen cuts, entry.2 ∉ seen := by
  classical
  induction cuts generalizing seen with
  | nil => simp [firstReportingCuts]
  | cons head rest ih =>
      simp only [firstReportingCuts]
      split
      · exact ih seen
      · rename_i fresh
        intro entry member
        rcases List.mem_cons.mp member with same | later
        · subst entry; exact fresh
        · intro earlier
          exact ih (head.2 :: seen) entry later (List.mem_cons_of_mem _ earlier)

/-- The selected reporting inventory contains each occurrence at most once. -/
theorem firstReportingCuts_distinct (seen : List Occurrence) (cuts : FailureCuts)
    : ((firstReportingCuts seen cuts).map Prod.snd).Nodup := by
  classical
  induction cuts generalizing seen with
  | nil => simp [firstReportingCuts]
  | cons head rest ih =>
      simp only [firstReportingCuts]
      split
      · exact ih seen
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, ih (head.2 :: seen)⟩
        intro member
        obtain ⟨entry, included, same⟩ := List.mem_map.mp member
        exact firstReportingCuts_excludes (head.2 :: seen) rest entry included
          (List.mem_cons.mpr (.inl same))

/-- Every unseen candidate has a selected copy of its occurrence at an earlier or equal cut.
Ordered candidates therefore retain availability when later duplicate observations vanish. -/
theorem firstReportingCuts_earlier {cuts : FailureCuts} {seen : List Occurrence}
    (ordered : cuts.Pairwise (fun left right => left.1 ≤ right.1))
    {entry : Nat × Occurrence} (member : entry ∈ cuts) (fresh : entry.2 ∉ seen)
    : ∃ kept ∈ firstReportingCuts seen cuts, kept.2 = entry.2 ∧ kept.1 ≤ entry.1 := by
  classical
  induction cuts generalizing seen with
  | nil => cases member
  | cons head rest ih =>
      have order := List.pairwise_cons.mp ordered
      by_cases prior : head.2 ∈ seen
      · simp only [firstReportingCuts, prior, ↓reduceIte]
        rcases List.mem_cons.mp member with same | later
        · subst entry; exact (fresh prior).elim
        · exact ih order.2 later fresh
      · simp only [firstReportingCuts, prior, ↓reduceIte]
        rcases List.mem_cons.mp member with same | later
        · subst entry
          exact ⟨head, List.mem_cons_self, rfl, Nat.le_refl _⟩
        · by_cases same : head.2 = entry.2
          · exact ⟨head, List.mem_cons_self, same, order.1 entry later⟩
          · have unseen : entry.2 ∉ head.2 :: seen := by
              intro earlier
              rcases List.mem_cons.mp earlier with equal | old
              · exact same equal.symm
              · exact fresh old
            obtain ⟨kept, selected, identity, before⟩ := ih order.2 later unseen
            exact ⟨kept, List.mem_cons_of_mem _ selected, identity, before⟩

/-- Licensed candidate metadata yields a fresh reporting witness after first-cut selection.
Reporting permits already covered failures; no causal cancellation premise is imposed. -/
theorem firstReportingCuts_witness {work initial events cuts}
    (ordered : cuts.Pairwise (fun left right => left.1 ≤ right.1))
    (known
      : ∀ entry ∈ cuts,
          entry.1 ≤ events.length
          ∧ ∃ owners producer payload,
              TaskAt work entry.2 owners producer payload
              ∧ payload.failure.isSome = true
              ∧ Reachable work entry.2
              ∧ ∃ ref ∈ owners, ref ∈ announcedRefs initial (events.take entry.1))
    : FailureReportingWitness work initial events (firstReportingCuts [] cuts) := by
  intro before cut occurrence after split
  have member : (cut, occurrence) ∈ firstReportingCuts [] cuts := by simp [split]
  have facts := known _ ((firstReportingCuts_sublist [] cuts).subset member)
  refine ⟨facts.1, ?_, ?_, facts.2⟩
  · have order := ordered.sublist (firstReportingCuts_sublist [] cuts)
    rw [split] at order
    intro earlier earlierMember
    exact (List.pairwise_append.mp order).2.2 earlier earlierMember _ List.mem_cons_self
  · have distinct := firstReportingCuts_distinct [] cuts
    rw [split, List.map_append, List.map_cons] at distinct
    intro prior
    exact (List.nodup_append.mp distinct).2.2 _ prior _ List.mem_cons_self rfl

/-- Causal candidates retain reporting availability at or before their own cuts. -/
theorem firstReportingCuts_causalAvailable {cuts causal}
    (ordered : cuts.Pairwise (fun left right => left.1 ≤ right.1))
    (included : causal.Subset cuts)
    : CausalFailuresAvailable causal (firstReportingCuts [] cuts) := by
  intro cut occurrence member
  obtain ⟨kept, retained, same, earlier⟩ :=
    firstReportingCuts_earlier (seen := []) ordered (included member) (by simp)
  have identity : kept = (kept.1, occurrence) := Prod.ext rfl same
  exact ⟨kept.1, identity ▸ retained, earlier⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
