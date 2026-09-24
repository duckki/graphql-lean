import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectionProperties

/-! Fresh-key ordering rules out cyclic defer ancestry during field collection. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

def UsageOrdered (usage : DeferUsage) : Prop :=
  ∀ ancestor ∈ usage.ancestors, ancestor < usage.key

def UsageBefore (state : Nat) (usage : Option DeferUsage) : Prop :=
  ∀ value ∈ usage, value.key < state ∧ UsageOrdered value

def CollectionKeys (start : Nat) (output : FieldCollection × Nat) : Prop :=
  start ≤ output.2
  ∧ GroupsSatisfy (fun field => UsageBefore output.2 field.deferUsage) output.1.fields
  ∧ ∀ usage ∈ output.1.newDeferUsages,
      start ≤ usage.key ∧ usage.key < output.2 ∧ UsageOrdered usage

theorem usageBefore_mono {left right : Nat} (usage : Option DeferUsage)
    (h : UsageBefore left usage) (hle : left ≤ right)
    : UsageBefore right usage := by
  intro value hv
  have hh := h value hv
  exact ⟨Nat.lt_of_lt_of_le hh.1 hle, hh.2⟩

theorem collectionKeys_append {start middle finish : Nat} {left right : FieldCollection}
    (hl : CollectionKeys start (left, middle))
    (hr : CollectionKeys middle (right, finish))
    : CollectionKeys start (left.append right, finish) := by
  rcases hl with ⟨hlm, hlf, hlu⟩
  rcases hr with ⟨hmf, hrf, hru⟩
  refine ⟨Nat.le_trans hlm hmf, ?_, ?_⟩
  · apply groupsSatisfy_merge
    · intro group hg field hf
      exact usageBefore_mono _ (hlf group hg field hf) hmf
    · exact hrf
  · intro usage hu
    rcases List.mem_append.mp hu with hu | hu
    · have h := hlu usage hu
      exact ⟨h.1, Nat.lt_of_lt_of_le h.2.1 hmf, h.2.2⟩
    · have h := hru usage hu
      exact ⟨Nat.le_trans hlm h.1, h.2⟩

theorem freshUsage_before (state : Nat) (parent : Option DeferUsage)
    (label : Option DirectiveLabel) (h : UsageBefore state parent)
    : UsageBefore (state + 1)
        (some
          {
            key := state
            label := label
            ancestors := (parent.map (fun usage => usage.key :: usage.ancestors)).getD []
          }) := by
  intro usage hu
  simp only [Option.mem_def, Option.some.injEq] at hu
  subst usage
  refine ⟨by dsimp only; omega, ?_⟩
  cases parent with
  | none => simp [UsageOrdered]
  | some parent =>
      have hp := h parent rfl
      intro ancestor ha
      simp only [Option.map_some, Option.getD_some, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hp.1
      · exact Nat.lt_trans (hp.2 ancestor ha) hp.1

mutual
  theorem collectSelection_keys (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selection : Selection)
      (usage : Option DeferUsage) (state : Nat) (h : UsageBefore state usage)
      : CollectionKeys state
          ((collectSelection schema variables parentType source usage selection).run
            state) := by
    cases selection with
    | field responseName fieldName arguments directives children =>
        cases ha : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, ha, CollectionKeys, GroupsSatisfy, h]
    | inlineFragment condition directives children =>
        cases ha : selectionDirectivesAllowBool variables directives
        · simp [collectSelection, ha, CollectionKeys, GroupsSatisfy]
        · cases ht : condition.all (doesFragmentTypeApplyBool schema parentType source)
          · simp [collectSelection, ha, ht, CollectionKeys, GroupsSatisfy]
          · cases hd : activeDefer? variables directives with
            | none =>
                simpa [collectSelection, ha, ht, hd]
                  using collectFields_keys schema variables parentType source children
                    usage state h
            | some label =>
                let next : DeferUsage := {
                  key := state, label := label,
                  ancestors := (usage.map (fun value => value.key :: value.ancestors)).getD [] }
                have hn : UsageBefore (state + 1) (some next) :=
                  freshUsage_before state usage label h
                have hc := collectFields_keys schema variables parentType source children
                  (some next) (state + 1) hn
                simp only [collectSelection, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  ht, hd, freshExecutionKey, run_bind, StateT.run_pure, id_pure_eq,
                  StateT.run_get, StateT.run_set]
                rcases hc with ⟨hs, hf, hu⟩
                dsimp only [next] at hs hf hu
                refine ⟨by omega, hf, ?_⟩
                intro value hv
                rcases List.mem_cons.mp hv with rfl | hv
                · exact ⟨Nat.le_refl _, by dsimp only; omega, (hn next rfl).2⟩
                · have hx := hu value hv
                  exact ⟨by omega, hx.2⟩
  termination_by sizeOf selection

  theorem collectFields_keys (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (usage : Option DeferUsage) (state : Nat) (h : UsageBefore state usage)
      : CollectionKeys state
          ((collectFields schema variables parentType source selections usage).run
            state) := by
    cases selections with
    | nil => simp [collectFields, CollectionKeys, GroupsSatisfy]
    | cons selection rest =>
        have hh := collectSelection_keys schema variables parentType source selection usage state h
        have ht := collectFields_keys schema variables parentType source rest usage
          ((collectSelection schema variables parentType source usage selection).run state).2
          (usageBefore_mono usage h hh.1)
        simp only [collectFields, run_bind, StateT.run_pure, id_pure_eq]
        exact collectionKeys_append hh ht
  termination_by sizeOf selections
end

theorem collectSubfields_keys (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    (state : Nat) (h : ∀ field ∈ fields, UsageBefore state field.deferUsage)
    : CollectionKeys state
        ((collectSubfields schema variables parentType source fields).run state) := by
  induction fields generalizing state with
  | nil => simp [collectSubfields, CollectionKeys, GroupsSatisfy]
  | cons field rest ih =>
      have hh := collectFields_keys schema variables parentType source field.selectionSet
        field.deferUsage state (h field (by simp))
      have ht := ih ((collectFields schema variables parentType source field.selectionSet
        field.deferUsage).run state).2
        (fun value hv => usageBefore_mono _ (h value (List.mem_cons_of_mem field hv)) hh.1)
      simp only [collectSubfields, run_bind, StateT.run_pure, id_pure_eq]
      exact collectionKeys_append hh ht

theorem nonempty_keys_minimum (keys : List Nat) (hne : keys ≠ [])
    : ∃ key ∈ keys, ∀ other ∈ keys, key ≤ other := by
  induction keys with
  | nil => exact False.elim (hne rfl)
  | cons key rest ih =>
      by_cases hr : rest = []
      · subst rest
        exact ⟨key, by simp, by simp⟩
      · obtain ⟨least, hl, hleast⟩ := ih hr
        by_cases hkleast : key ≤ least
        · refine ⟨key, by simp, ?_⟩
          intro other ho
          rcases List.mem_cons.mp ho with rfl | ho
          · exact Nat.le_refl _
          · exact Nat.le_trans hkleast (hleast other ho)
        · refine ⟨least, List.mem_cons_of_mem key hl, ?_⟩
          intro other ho
          rcases List.mem_cons.mp ho with rfl | ho
          · omega
          · exact hleast other ho

/-- Overlap can eliminate descendant usages, but it cannot eliminate every usage in a
nonempty deferred group whose ancestry is ordered by fresh keys.
-/
theorem filteredDeferUsageSet_nonempty (fields : List ExecutableField)
    (hne : fields ≠ [])
    (himmediate : fields.any (fun field => field.deferUsage.isNone) = false)
    (hordered : ∀ field ∈ fields, ∀ usage ∈ field.deferUsage, UsageOrdered usage)
    : getFilteredDeferUsageSet fields ≠ [] := by
  let usages := fields.filterMap ExecutableField.deferUsage
  let keys := (usages.map DeferUsage.key).eraseDups
  have hkeys : keys ≠ [] := by
    cases fields with
    | nil => exact False.elim (hne rfl)
    | cons field rest =>
        cases hu : field.deferUsage with
        | none => simp [hu] at himmediate
        | some usage =>
            have hm : usage.key ∈ keys := by simp [keys, usages, hu]
            exact List.ne_nil_of_mem hm
  obtain ⟨least, hl, hleast⟩ := nonempty_keys_minimum keys hkeys
  have hkeep : usages.any (fun usage =>
      usage.key == least && usage.ancestors.any keys.contains) = false := by
    apply List.any_eq_false.mpr
    intro usage hu hbad
    obtain ⟨field, hf, hfu⟩ := List.mem_filterMap.mp hu
    have ho := hordered field hf usage hfu
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.contains_iff_mem] at hbad
    obtain ⟨heq, ancestor, ha, hak⟩ := hbad
    have hlt := ho ancestor ha
    have hle := hleast ancestor hak
    omega
  apply List.ne_nil_of_mem (a := least)
  unfold getFilteredDeferUsageSet
  rw [himmediate]
  change least ∈ keys.filter _
  exact List.mem_filter.mpr ⟨hl, by rw [hkeep]; rfl⟩

end GraphQL.IncrementalDelivery.Semantics
