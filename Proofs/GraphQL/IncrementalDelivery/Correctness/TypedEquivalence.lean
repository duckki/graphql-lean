import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedResponse
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ReorderingSoundness

/-! Typed absolute entries determine a response up to object-field ordering.
Unique paths rule out ambiguous duplicate object keys; list indices retain order.
The hypotheses concern ordinary values, without assuming execution equivalence.
-/

namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse

open GraphQL.IncrementalDelivery.Execution (ResponsePath ResponsePathSegment)
open GraphQL.Execution

/-- Permuting response fields permutes their typed entries, by flat-map congruence. -/
theorem fields_perm_of_perm (path : ResponsePath)
    {left right : List (Name × ResponseValue)} (hp : left.Perm right)
    : (fields path left).Perm (fields path right) := by
  have hf (data : List (Name × ResponseValue)) : fields path data
      = data.flatMap (fun field => value (path ++ [.field field.1]) field.2) := by
    induction data with
    | nil => rfl
    | cons field rest ih => simp [fields, ih]
  simpa only [hf]
    using hp.flatMap_right (fun field => value (path ++ [.field field.1]) field.2)

/-- Canonical field entries preserve permutations, by map congruence. -/
theorem canonicalFields_perm_of_perm {left right : List (Name × ResponseValue)}
    (hp : left.Perm right)
    : (ResponseValue.canonicalObjectFields left).Perm
        (ResponseValue.canonicalObjectFields right) := by
  have hf (data : List (Name × ResponseValue)) : ResponseValue.canonicalObjectFields data
      = data.map (fun field => (field.1, ResponseValue.canonical field.2)) := by
    induction data with
    | nil => rfl
    | cons field rest ih => simp [ResponseValue.canonicalObjectFields, ih]
  simpa only [hf] using hp.map (fun field => (field.1, ResponseValue.canonical field.2))

mutual
  /-- Unique typed-entry permutations determine semantically equivalent values,
  by mutual induction on values, object fields, and indexed list items. -/
  theorem value_equivalent (path : ResponsePath) (left right : ResponseValue)
      (hl : ((value path left).map Prod.fst).Nodup)
      (hr : ((value path right).map Prod.fst).Nodup)
      (hp : (value path left).Perm (value path right))
      : ResponseValue.semanticEquivalent left right := by
    have ha := rootAtom_of_perm path left right hp
    cases left <;> cases right <;> simp only [rootAtom] at ha <;> try contradiction
    · rfl
    · cases ha; rfl
    · apply GraphQL.NormalForm.GroundTypeNormalization.ReorderingSoundness.semanticEquivalent_object_of_canonical_fields_perm_nodup
      · exact fields_equivalent path _ _ (List.nodup_cons.mp hl).2
          (List.nodup_cons.mp hr).2 (List.Perm.cons_inv hp)
      · exact fields_keys_nodup path _ (List.nodup_cons.mp hl).2
    · exact congrArg ResponseValue.list
        (items_equivalent path 0 _ _ (List.nodup_cons.mp hl).2
          (List.nodup_cons.mp hr).2 (List.Perm.cons_inv hp))

  /-- Unique object entries determine equivalent canonical fields, by mutual induction
  and extraction of each uniquely named child's entries. -/
  theorem fields_equivalent (path : ResponsePath)
      (left right : List (Name × ResponseValue))
      (hl : ((fields path left).map Prod.fst).Nodup)
      (hr : ((fields path right).map Prod.fst).Nodup)
      (hp : (fields path left).Perm (fields path right))
      : (ResponseValue.canonicalObjectFields left).Perm
          (ResponseValue.canonicalObjectFields right) := by
    cases left with
    | nil =>
        have he := fields_nil_of_perm path right hp
        subst right
        exact .refl _
    | cons field rest =>
        have hlkeys := fields_keys_nodup path (field :: rest) hl
        simp only [fields, List.map_append] at hl
        obtain ⟨next, hn⟩ := fields_matching path field.1 field.2 rest right hp
        have hc : (value (path ++ [.field field.1]) field.2).Perm
            (value (path ++ [.field field.1]) next) := by
          have hf := hp.filter (fun entry => (path ++ [ResponsePathSegment.field field.1]).isPrefixOf entry.1)
          change (subtree _ _).Perm (subtree _ _) at hf
          simpa only [subtree_fields_member path field.1 field.2 (field :: rest)
            hlkeys (by simp),
            subtree_fields_member path field.1 next right (fields_keys_nodup path _ hr) hn] using hf
        have hcl := (List.nodup_append.mp hl).1
        have hcr := ((value_sublist_fields path field.1 next right hn).map Prod.fst).nodup hr
        have heq := value_equivalent (path ++ [.field field.1]) field.2 next hcl hcr hc
        unfold ResponseValue.semanticEquivalent at heq
        obtain ⟨before, after, hright⟩ := List.mem_iff_append.mp hn
        have hmove : right.Perm ((field.1, next) :: (before ++ after)) := by
          rw [hright]
          exact List.perm_middle
        have hre := fields_perm_of_perm path hmove
        have hrest : (fields path rest).Perm (fields path (before ++ after)) := by
          have h := (hc.symm.append_right (fields path rest)).trans (hp.trans hre)
          exact (List.perm_append_left_iff _).mp h
        have hr' := (hre.map Prod.fst).nodup_iff.mp hr
        simp only [fields, List.map_append] at hr'
        have ih := fields_equivalent path rest (before ++ after)
          (List.nodup_append.mp hl).2.1 (List.nodup_append.mp hr').2.1 hrest
        apply List.Perm.trans _ (canonicalFields_perm_of_perm hmove).symm
        simpa only [ResponseValue.canonicalObjectFields, heq]
          using ih.cons (field.1, ResponseValue.canonical field.2)

  /-- Unique indexed entries determine equivalent ordered list items, by mutual
  induction retaining each item's absolute index. -/
  theorem items_equivalent (path : ResponsePath) (index : Nat)
      (left right : List ResponseValue)
      (hl : ((items path index left).map Prod.fst).Nodup)
      (hr : ((items path index right).map Prod.fst).Nodup)
      (hp : (items path index left).Perm (items path index right))
      : ResponseValue.canonicalList left = ResponseValue.canonicalList right := by
    cases left with
    | nil =>
        have he := items_nil_of_perm path index right hp
        subst right
        rfl
    | cons head rest =>
        cases right with
        | nil =>
            have he := items_nil_of_perm path index (head :: rest) hp.symm
            contradiction
        | cons other tail =>
            simp only [items, List.map_append] at hl hr
            have hc : (value (path ++ [.index index]) head).Perm
                (value (path ++ [.index index]) other) := by
              have hf := hp.filter (fun entry => (path ++ [ResponsePathSegment.index index]).isPrefixOf entry.1)
              change (subtree _ _).Perm (subtree _ _) at hf
              simpa only [subtree_items_cons] using hf
            have heq := value_equivalent (path ++ [.index index]) head other
              (List.nodup_append.mp hl).1 (List.nodup_append.mp hr).1 hc
            unfold ResponseValue.semanticEquivalent at heq
            have hrest : (items path (index + 1) rest).Perm (items path (index + 1) tail) :=
              (List.perm_append_left_iff _).mp ((hc.symm.append_right _).trans hp)
            have ih := items_equivalent path (index + 1) rest tail
              (List.nodup_append.mp hl).2.1 (List.nodup_append.mp hr).2.1 hrest
            simp only [ResponseValue.canonicalList, heq, ih]
end

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
