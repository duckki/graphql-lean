import GraphQL.Theories.SelectionConditions

/-! Order-independent characterization of canonical Boolean conjunctions. -/

namespace GraphQL
namespace SelectionConditions

private def BooleanLiteral.BeforeOrEqual (left right : BooleanLiteral) : Prop :=
  left.orderedBeforeOrEqual right = true

private theorem BooleanLiteral.BeforeOrEqual.name_le
    {left right : BooleanLiteral} (hbefore : left.BeforeOrEqual right)
    : left.variableName ≤ right.variableName := by
  unfold BooleanLiteral.BeforeOrEqual BooleanLiteral.orderedBeforeOrEqual at hbefore
  split at hbefore <;> rename_i hnames
  · rw [beq_iff_eq.mp hnames]
    exact String.le_refl _
  · exact of_decide_eq_true hbefore

private theorem BooleanLiteral.BeforeOrEqual.of_name_le_of_ne
    {left right : BooleanLiteral} (hle : left.variableName ≤ right.variableName)
    (hne : left.variableName ≠ right.variableName)
    : left.BeforeOrEqual right := by
  simp [BooleanLiteral.BeforeOrEqual, BooleanLiteral.orderedBeforeOrEqual,
    hne, hle]

private theorem BooleanLiteral.BeforeOrEqual.total (left right : BooleanLiteral)
    : left.BeforeOrEqual right ∨ right.BeforeOrEqual left := by
  by_cases hnames : left.variableName = right.variableName
  · cases left <;> cases right <;> simp_all [BooleanLiteral.BeforeOrEqual,
      BooleanLiteral.orderedBeforeOrEqual, BooleanLiteral.variableName,
      BooleanLiteral.requiredValue]
  · rcases String.le_total left.variableName right.variableName with hleft | hright
    · exact Or.inl (BooleanLiteral.BeforeOrEqual.of_name_le_of_ne hleft hnames)
    · exact Or.inr (BooleanLiteral.BeforeOrEqual.of_name_le_of_ne hright
        (Ne.symm hnames))

private theorem BooleanLiteral.BeforeOrEqual.trans
    {left middle right : BooleanLiteral}
    (hleft : left.BeforeOrEqual middle) (hright : middle.BeforeOrEqual right)
    : left.BeforeOrEqual right := by
  have hnames := String.le_trans hleft.name_le hright.name_le
  by_cases heq : left.variableName = right.variableName
  · have hleftMiddle : left.variableName = middle.variableName :=
      String.le_antisymm hleft.name_le (heq ▸ hright.name_le)
    have hmiddleRight : middle.variableName = right.variableName :=
      hleftMiddle.symm.trans heq
    cases left <;> cases middle <;> cases right <;>
      simp_all [BooleanLiteral.BeforeOrEqual, BooleanLiteral.orderedBeforeOrEqual,
        BooleanLiteral.variableName, BooleanLiteral.requiredValue]
  · unfold BooleanLiteral.BeforeOrEqual BooleanLiteral.orderedBeforeOrEqual
    simp [heq, hnames]

private theorem BooleanLiteral.BeforeOrEqual.antisymm
    {left right : BooleanLiteral}
    (hleft : left.BeforeOrEqual right) (hright : right.BeforeOrEqual left)
    : left = right := by
  have hnames := String.le_antisymm hleft.name_le hright.name_le
  cases left <;> cases right <;>
    simp_all [BooleanLiteral.BeforeOrEqual, BooleanLiteral.orderedBeforeOrEqual,
      BooleanLiteral.variableName, BooleanLiteral.requiredValue]

private theorem insertBooleanLiteral_mem_iff
    (literal : BooleanLiteral) (source target : List BooleanLiteral)
    (hinsert : insertBooleanLiteral literal source = some target)
    : ∀ candidate, candidate ∈ target ↔ candidate = literal ∨ candidate ∈ source := by
  induction source generalizing target with
  | nil =>
      simp [insertBooleanLiteral] at hinsert
      subst target
      simp
  | cons head rest ih =>
      rw [insertBooleanLiteral] at hinsert
      split at hinsert <;> rename_i hequal
      · simp only [Option.some.injEq] at hinsert
        subst target
        have hliteral : literal = head := beq_iff_eq.mp hequal
        simp [hliteral]
      · split at hinsert
        · simp at hinsert
        · split at hinsert
          · simp only [Option.some.injEq] at hinsert
            subst target
            simp
          · cases hrest : insertBooleanLiteral literal rest with
            | none => simp [hrest] at hinsert
            | some inserted =>
                simp only [hrest, Option.some.injEq] at hinsert
                subst target
                intro candidate
                rw [List.mem_cons, ih inserted hrest candidate, List.mem_cons]
                constructor
                · rintro (rfl | heq | hmem)
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inl heq
                  · exact Or.inr (Or.inr hmem)
                · rintro (rfl | rfl | hmem)
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr hmem)

private theorem insertBooleanLiteral_nodup
    (literal : BooleanLiteral) (source target : List BooleanLiteral)
    (hsource : source.Nodup)
    (hpairwise : source.Pairwise BooleanLiteral.BeforeOrEqual)
    (hinsert : insertBooleanLiteral literal source = some target)
    : target.Nodup := by
  induction source generalizing target with
  | nil =>
      simp [insertBooleanLiteral] at hinsert
      subst target
      simp
  | cons head rest ih =>
      rw [insertBooleanLiteral] at hinsert
      split at hinsert <;> rename_i hequal
      · simp only [Option.some.injEq] at hinsert
        subst target
        exact hsource
      · split at hinsert
        · simp at hinsert
        · split at hinsert <;> rename_i hbefore
          · simp only [Option.some.injEq] at hinsert
            subst target
            have hsourceParts := List.nodup_cons.mp hsource
            have hpairwiseParts := List.pairwise_cons.mp hpairwise
            apply List.nodup_cons.mpr
            refine ⟨?_, hsource⟩
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hrestMem
            · exact hequal (beq_iff_eq.mpr heq)
            · have hheadBefore := hpairwiseParts.1 literal hrestMem
              have hequalHead :=
                BooleanLiteral.BeforeOrEqual.antisymm hbefore hheadBefore
              exact hequal (beq_iff_eq.mpr hequalHead)
          · cases hrest : insertBooleanLiteral literal rest with
            | none => simp [hrest] at hinsert
            | some inserted =>
                simp only [hrest, Option.some.injEq] at hinsert
                subst target
                have hsourceParts := List.nodup_cons.mp hsource
                have hpairwiseParts := List.pairwise_cons.mp hpairwise
                apply List.nodup_cons.mpr
                refine ⟨?_, ih inserted hsourceParts.2 hpairwiseParts.2 hrest⟩
                intro hmem
                rcases (insertBooleanLiteral_mem_iff literal rest inserted hrest head).mp
                    hmem with heq | hrestMem
                · exact hequal (beq_iff_eq.mpr heq.symm)
                · exact hsourceParts.1 hrestMem

private theorem insertBooleanLiteral_pairwise
    (literal : BooleanLiteral) (source target : List BooleanLiteral)
    (hsource : source.Pairwise BooleanLiteral.BeforeOrEqual)
    (hinsert : insertBooleanLiteral literal source = some target)
    : target.Pairwise BooleanLiteral.BeforeOrEqual := by
  induction source generalizing target with
  | nil =>
      simp [insertBooleanLiteral] at hinsert
      subst target
      simp
  | cons head rest ih =>
      rw [insertBooleanLiteral] at hinsert
      split at hinsert <;> rename_i hequal
      · simp only [Option.some.injEq] at hinsert
        subst target
        exact hsource
      · split at hinsert
        · simp at hinsert
        · split at hinsert <;> rename_i hbefore
          · simp only [Option.some.injEq] at hinsert
            subst target
            have hsourceParts := List.pairwise_cons.mp hsource
            apply List.pairwise_cons.mpr
            refine ⟨?_, hsource⟩
            intro candidate hcandidate
            rcases List.mem_cons.mp hcandidate with rfl | hcandidate
            · exact hbefore
            · exact BooleanLiteral.BeforeOrEqual.trans hbefore
                (hsourceParts.1 candidate hcandidate)
          · cases hrest : insertBooleanLiteral literal rest with
            | none => simp [hrest] at hinsert
            | some inserted =>
                simp only [hrest, Option.some.injEq] at hinsert
                subst target
                have hsourceParts := List.pairwise_cons.mp hsource
                apply List.pairwise_cons.mpr
                refine ⟨?_, ih inserted hsourceParts.2 hrest⟩
                intro candidate hcandidate
                rcases (insertBooleanLiteral_mem_iff literal rest inserted hrest candidate).mp
                    hcandidate with rfl | hrestMem
                · rcases BooleanLiteral.BeforeOrEqual.total head _ with h | h
                  · exact h
                  · exact False.elim (hbefore h)
                · exact hsourceParts.1 candidate hrestMem

private theorem canonicalBooleanCondition_properties
    (source target : List BooleanLiteral)
    (hcanonical : canonicalBooleanCondition source = some target)
    : target.Nodup
      ∧ target.Pairwise BooleanLiteral.BeforeOrEqual
      ∧ ∀ literal, literal ∈ target ↔ literal ∈ source := by
  induction source generalizing target with
  | nil =>
      simp [canonicalBooleanCondition] at hcanonical
      subst target
      simp
  | cons literal rest ih =>
      rw [canonicalBooleanCondition] at hcanonical
      cases hrest : canonicalBooleanCondition rest with
      | none => simp [hrest] at hcanonical
      | some restCanonical =>
          cases hinsert : insertBooleanLiteral literal restCanonical with
          | none => simp [hrest, hinsert] at hcanonical
          | some inserted =>
              have hequal : inserted = target := by
                simpa [hrest, hinsert] using hcanonical
              subst target
              rcases ih restCanonical hrest with ⟨hnodup, hpairwise, hmembers⟩
              refine ⟨insertBooleanLiteral_nodup literal restCanonical inserted hnodup
                  hpairwise hinsert,
                insertBooleanLiteral_pairwise literal restCanonical inserted hpairwise
                  hinsert, ?_⟩
              intro candidate
              rw [insertBooleanLiteral_mem_iff literal restCanonical inserted hinsert,
                hmembers]
              simp [eq_comm]

theorem canonicalBooleanCondition_eq_of_mem_iff
    {left right leftCanonical rightCanonical : List BooleanLiteral}
    (hleft : canonicalBooleanCondition left = some leftCanonical)
    (hright : canonicalBooleanCondition right = some rightCanonical)
    (hmembers : ∀ literal, literal ∈ left ↔ literal ∈ right)
    : leftCanonical = rightCanonical := by
  rcases canonicalBooleanCondition_properties left leftCanonical hleft with
    ⟨hleftNodup, hleftPairwise, hleftMembers⟩
  rcases canonicalBooleanCondition_properties right rightCanonical hright with
    ⟨hrightNodup, hrightPairwise, hrightMembers⟩
  have hperm : leftCanonical.Perm rightCanonical :=
    (List.perm_ext_iff_of_nodup hleftNodup hrightNodup).mpr fun literal => by
      rw [hleftMembers, hrightMembers]
      exact hmembers literal
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ hforward hback => hforward.antisymm hback)
    hleftPairwise hrightPairwise hperm

theorem canonicalBooleanCondition_mem_iff
    {source target : List BooleanLiteral}
    (hcanonical : canonicalBooleanCondition source = some target)
    (literal : BooleanLiteral)
    : literal ∈ target ↔ literal ∈ source :=
  (canonicalBooleanCondition_properties source target hcanonical).2.2 literal

theorem canonicalBooleanCondition_eq_of_perm
    {left right leftCanonical rightCanonical : List BooleanLiteral}
    (hleft : canonicalBooleanCondition left = some leftCanonical)
    (hright : canonicalBooleanCondition right = some rightCanonical)
    (hperm : left.Perm right)
    : leftCanonical = rightCanonical :=
  canonicalBooleanCondition_eq_of_mem_iff hleft hright fun _literal => hperm.mem_iff

private theorem insertBooleanLiteral_variableNames_nodup
    (literal : BooleanLiteral) (source target : List BooleanLiteral)
    (hnodup : (source.map BooleanLiteral.variableName).Nodup)
    (hordered : source.Pairwise BooleanLiteral.BeforeOrEqual)
    (hinsert : insertBooleanLiteral literal source = some target)
    : (target.map BooleanLiteral.variableName).Nodup := by
  induction source generalizing target with
  | nil =>
      simp [insertBooleanLiteral] at hinsert
      subst target
      simp
  | cons head rest ih =>
      rw [insertBooleanLiteral] at hinsert
      split at hinsert <;> rename_i hequal
      · cases Option.some.inj hinsert
        exact hnodup
      · split at hinsert <;> rename_i hcomplement
        · simp at hinsert
        · have hnames : literal.variableName ≠ head.variableName := by
            cases literal <;> cases head <;>
              simp_all [BooleanLiteral.complement, BooleanLiteral.variableName]
          have hnodupParts := List.nodup_cons.mp hnodup
          have horderedParts := List.pairwise_cons.mp hordered
          split at hinsert <;> rename_i hbefore
          · cases Option.some.inj hinsert
            apply List.nodup_cons.mpr
            refine ⟨?_, hnodup⟩
            intro hmember
            obtain ⟨candidate, hcandidate, hname⟩ := List.mem_map.mp hmember
            rcases List.mem_cons.mp hcandidate with rfl | hrest
            · exact hnames hname.symm
            · apply hnames
              exact String.le_antisymm (BooleanLiteral.BeforeOrEqual.name_le hbefore)
                (hname ▸ (horderedParts.1 candidate hrest).name_le)
          · cases hrest : insertBooleanLiteral literal rest with
            | none => simp [hrest] at hinsert
            | some inserted =>
                simp only [hrest, Option.some.injEq] at hinsert
                subst target
                apply List.nodup_cons.mpr
                refine ⟨?_, ih inserted hnodupParts.2 horderedParts.2 hrest⟩
                intro hmember
                obtain ⟨candidate, hcandidate, hname⟩ := List.mem_map.mp hmember
                rcases (insertBooleanLiteral_mem_iff literal rest inserted hrest candidate).mp
                    hcandidate with rfl | hsource
                · exact hnames hname
                · exact hnodupParts.1 (List.mem_map.mpr ⟨candidate, hsource, hname⟩)

-- A surviving conjunction never asks for both values of the same variable.
theorem canonicalBooleanCondition_variableNames_nodup
    {source target : List BooleanLiteral}
    (hcanonical : canonicalBooleanCondition source = some target)
    : (target.map BooleanLiteral.variableName).Nodup := by
  induction source generalizing target with
  | nil =>
      simp [canonicalBooleanCondition] at hcanonical
      subst target
      simp
  | cons literal rest ih =>
      cases hrest : canonicalBooleanCondition rest with
      | none => simp [canonicalBooleanCondition, hrest] at hcanonical
      | some restCanonical =>
          simp only [canonicalBooleanCondition, hrest] at hcanonical
          exact insertBooleanLiteral_variableNames_nodup literal restCanonical target
            (ih hrest) (canonicalBooleanCondition_properties rest restCanonical hrest).2.1
            hcanonical

end SelectionConditions
end GraphQL
