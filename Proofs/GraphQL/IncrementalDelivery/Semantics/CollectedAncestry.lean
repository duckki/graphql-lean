import Proofs.GraphQL.IncrementalDelivery.Semantics.AncestryMetadata

/-! Collection extends coherent defer ancestry without losing inherited references.
Fresh usages are inserted before their descendants, and every collected field's usage
is present in the extended local defer map.
-/

namespace GraphQL.IncrementalDelivery.Semantics.Ancestry

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem OptionalUsageAt.extend {parents next : Assignment} {start finish : Nat}
    {deferMap nextMap : DeferMap} {usage : Option DeferUsage}
    (h : OptionalUsageAt parents start deferMap usage) (he : Extends start parents next)
    (hle : start ≤ finish) (hm : (mapKeys deferMap).Subset (mapKeys nextMap))
    : OptionalUsageAt next finish nextMap usage :=
  fun actual ha => (h actual ha).extend he hle hm

theorem getNewDeferMap_keeps_keys (usages : List DeferUsage) (path : ResponsePath)
    (deferMap : DeferMap)
    : (mapKeys deferMap).Subset (mapKeys (getNewDeferMap usages path deferMap)) := by
  rw [getNewDeferMap_keys]
  exact List.subset_append_left _ _

def Collected (parents : Assignment) (start : Nat) (deferMap : DeferMap)
    (path : ResponsePath) (output : FieldCollection × Nat)
    : Prop :=
  start ≤ output.2
  ∧ ∃ next,
      Extends start parents next
      ∧ Valid next output.2
      ∧ MapAt next output.2 (getNewDeferMap output.1.newDeferUsages path deferMap)
      ∧ GroupsSatisfy
          (fun field =>
            OptionalUsageAt next output.2
              (getNewDeferMap output.1.newDeferUsages path deferMap) field.deferUsage)
          output.1.fields

theorem collected_empty (parents : Assignment) (state : Nat) (deferMap : DeferMap)
    (path : ResponsePath) (hv : Valid parents state) (hm : MapAt parents state deferMap)
    : Collected parents state deferMap path ({}, state) := by
  exact ⟨Nat.le_refl _, parents, Extends.refl _ _, hv, hm, by simp [GroupsSatisfy]⟩

theorem collected_append {first middle : Assignment} {start mid finish : Nat}
    {deferMap : DeferMap} {path : ResponsePath} {left right : FieldCollection}
    (hlm : start ≤ mid) (he : Extends start first middle) (_hv : Valid middle mid)
    (_hm : MapAt middle mid (getNewDeferMap left.newDeferUsages path deferMap))
    (hf
      : GroupsSatisfy
          (fun field =>
            OptionalUsageAt middle mid
              (getNewDeferMap left.newDeferUsages path deferMap) field.deferUsage)
          left.fields)
    (hr
      : Collected middle mid (getNewDeferMap left.newDeferUsages path deferMap) path
          (right, finish))
    : Collected first start deferMap path (left.append right, finish) := by
  obtain ⟨hmf, next, hn, hnv, hnm, hnf⟩ := hr
  refine ⟨Nat.le_trans hlm hmf, next, he.trans hn hlm, hnv, ?_, ?_⟩
  · simpa only [FieldCollection.append, getNewDeferMap_append] using hnm
  · simp only [FieldCollection.append, getNewDeferMap_append]
    apply groupsSatisfy_merge _ _ _ _ hnf
    intro group hg field hfield
    exact (hf group hg field hfield).extend hn hmf (getNewDeferMap_keeps_keys _ _ _)

mutual
  theorem collectSelection_ancestry (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selection : Selection)
      (usage : Option DeferUsage) (parents : Assignment) (state : Nat)
      (deferMap : DeferMap) (path : ResponsePath)
      (hv : Valid parents state) (hm : MapAt parents state deferMap)
      (hu : OptionalUsageAt parents state deferMap usage)
      : Collected parents state deferMap path
          ((collectSelection schema variables parentType source usage selection).run
            state) := by
    cases selection with
    | field name fieldName arguments directives children =>
        cases ha : selectionDirectivesAllowBool variables directives
        · simpa [collectSelection, ha] using collected_empty parents state deferMap path hv hm
        · simp only [collectSelection, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            StateT.run_pure, id_pure_eq]
          exact ⟨Nat.le_refl _, parents, Extends.refl _ _, hv, hm,
            by simpa [GroupsSatisfy, getNewDeferMap] using hu⟩
    | inlineFragment condition directives children =>
        cases ha : selectionDirectivesAllowBool variables directives
        · simpa [collectSelection, ha] using collected_empty parents state deferMap path hv hm
        · cases ht : condition.all (doesFragmentTypeApplyBool schema parentType source)
          · simpa [collectSelection, ha, ht] using collected_empty parents state deferMap path hv hm
          · cases hd : activeDefer? variables directives with
            | none =>
                simpa [collectSelection, ha, ht, hd]
                  using collectFields_ancestry schema variables parentType source children
                    usage parents state deferMap path hv hm hu
            | some label =>
                let ancestors := (usage.map (fun parent => parent.key :: parent.ancestors)).getD []
                let fresh : DeferUsage := { key := state, label, ancestors }
                let next := allocate parents state ancestors
                let nextMap := getNewDeferMap [fresh] path deferMap
                have hn := mapAt_allocate parents state path deferMap usage label hm hu
                have hnv : Valid next (state + 1) := allocate_valid parents state usage hv
                  (fun u hm => ⟨(hu u hm).1, (hu u hm).2.1⟩)
                have hc := collectFields_ancestry schema variables parentType source children (some fresh)
                  next (state + 1) nextMap path hnv hn.1 (by intro u hu; cases hu; exact hn.2)
                obtain ⟨hle, final, he, hfinal, hmap, hfields⟩ := hc
                simp only [collectSelection, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  ht, hd, freshExecutionKey, run_bind, StateT.run_pure, id_pure_eq,
                  StateT.run_get, StateT.run_set]
                refine ⟨Nat.le_trans (Nat.le_succ state) hle, final,
                  (allocate_extends parents state ancestors).trans he (Nat.le_succ state),
                  hfinal, ?_, ?_⟩
                · simpa only [nextMap, fresh, ancestors, getNewDeferMap, List.foldl_cons,
                    List.foldl_nil] using hmap
                · simpa only [nextMap, fresh, ancestors, getNewDeferMap, List.foldl_cons,
                    List.foldl_nil] using hfields
  termination_by sizeOf selection

  theorem collectFields_ancestry (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (usage : Option DeferUsage) (parents : Assignment) (state : Nat)
      (deferMap : DeferMap) (path : ResponsePath)
      (hv : Valid parents state) (hm : MapAt parents state deferMap)
      (hu : OptionalUsageAt parents state deferMap usage)
      : Collected parents state deferMap path
          ((collectFields schema variables parentType source selections usage).run
            state) := by
    cases selections with
    | nil => simpa [collectFields] using collected_empty parents state deferMap path hv hm
    | cons selection rest =>
        obtain ⟨hle, next, he, hnv, hnm, hnf⟩ := collectSelection_ancestry schema variables parentType
          source selection usage parents state deferMap path hv hm hu
        have ht := collectFields_ancestry schema variables parentType source rest usage next
          ((collectSelection schema variables parentType source usage selection).run state).2
          _ path hnv hnm (hu.extend he hle (getNewDeferMap_keeps_keys _ _ _))
        simp only [collectFields, run_bind, StateT.run_pure, id_pure_eq]
        exact collected_append hle he hnv hnm hnf ht
  termination_by sizeOf selections
end

theorem collectSubfields_ancestry (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    (parents : Assignment) (state : Nat) (deferMap : DeferMap) (path : ResponsePath)
    (hv : Valid parents state) (hm : MapAt parents state deferMap)
    (hu : ∀ field ∈ fields, OptionalUsageAt parents state deferMap field.deferUsage)
    : Collected parents state deferMap path
        ((collectSubfields schema variables parentType source fields).run state) := by
  induction fields generalizing parents state deferMap with
  | nil =>
      simpa [collectSubfields] using collected_empty parents state deferMap path hv hm
  | cons field rest ih =>
      obtain ⟨hle, next, he, hnv, hnm, hnf⟩ := collectFields_ancestry schema variables parentType
        source field.selectionSet field.deferUsage parents state deferMap path hv hm (hu field (by simp))
      have ht := ih next _ _ hnv hnm (fun f hf =>
        (hu f (List.mem_cons_of_mem field hf)).extend he hle (getNewDeferMap_keeps_keys _ _ _))
      simp only [collectSubfields, run_bind, StateT.run_pure, id_pure_eq]
      exact collected_append hle he hnv hnm hnf ht

end GraphQL.IncrementalDelivery.Semantics.Ancestry
