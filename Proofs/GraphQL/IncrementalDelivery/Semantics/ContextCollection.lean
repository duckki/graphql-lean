import Proofs.GraphQL.IncrementalDelivery.Semantics.Erasure

/-! Ordinary selections preserve an inherited defer context during collection. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

variable {ObjectRef : Type}

abbrev FieldInContext (usage : Option DeferUsage) (field : ExecutableField) : Prop :=
  field.deferUsage = usage
  ∧ DirectivesPlain field.directives
  ∧ SelectionsPlain field.selectionSet

abbrev FieldsInContext (usage : Option DeferUsage) (fields : List ExecutableField)
    : Prop :=
  ∀ field ∈ fields, FieldInContext usage field

abbrev GroupsInContext (usage : Option DeferUsage) (groups : CollectedFieldsMap) : Prop :=
  ∀ group ∈ groups, group.2 ≠ [] ∧ FieldsInContext usage group.2

theorem groupsInContext_add (usage : Option DeferUsage)
    (group : Name × List ExecutableField) (groups : CollectedFieldsMap)
    (hne : group.2 ≠ []) (hg : FieldsInContext usage group.2)
    (hs : GroupsInContext usage groups)
    : GroupsInContext usage (addExecutableGroup group groups) := by
  induction groups with
  | nil => simpa [addExecutableGroup, GroupsInContext] using And.intro hne hg
  | cons head rest ih =>
      have hh := hs head (by simp)
      have ht : GroupsInContext usage rest := fun g h => hs g (by simp [h])
      rcases group with ⟨key, fields⟩
      rcases head with ⟨name, existing⟩
      by_cases h : name == key
      · simp only [addExecutableGroup, h, ↓reduceIte]
        intro candidate hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · refine ⟨fun he => hh.1 (List.append_eq_nil_iff.mp he).1, ?_⟩
          intro field hf
          rcases List.mem_append.mp hf with hf | hf
          · exact hh.2 field hf
          · exact hg field hf
        · exact ht candidate hc
      · simpa [addExecutableGroup, h, GroupsInContext] using And.intro hh (ih ht)

theorem groupsInContext_merge (usage : Option DeferUsage)
    (left right : CollectedFieldsMap) (hl : GroupsInContext usage left)
    (hr : GroupsInContext usage right)
    : GroupsInContext usage (mergeExecutableGroups left right) := by
  induction right generalizing left with
  | nil => exact hl
  | cons group rest ih =>
      exact ih (addExecutableGroup group left)
        (groupsInContext_add usage group left (hr group (by simp)).1
          (hr group (by simp)).2 hl)
        (fun g h => hr g (by simp [h]))

def CollectionInContext (usage : Option DeferUsage) (state : Nat)
    (output : FieldCollection × Nat)
    : Prop :=
  output.2 = state ∧ output.1.newDeferUsages = [] ∧ GroupsInContext usage output.1.fields

theorem collectionInContext_append (usage : Option DeferUsage)
    {left right : FieldCollection} {state : Nat}
    (hl : CollectionInContext usage state (left, state))
    (hr : CollectionInContext usage state (right, state))
    : CollectionInContext usage state (left.append right, state) := by
  rcases hl with ⟨_, hln, hlp⟩
  rcases hr with ⟨_, hrn, hrp⟩
  dsimp only at hln hrn hlp hrp
  exact ⟨
    rfl,
    by simp [FieldCollection.append, hln, hrn],
    groupsInContext_merge usage _ _ hlp hrp
  ⟩

mutual
  theorem collectSelection_inContext (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selection : Selection)
      (hplain : selection.hasIncrementalDirectives = false) (usage : Option DeferUsage)
      (state : Nat)
      : CollectionInContext usage state
          ((collectSelection schema variables parentType source usage selection).run
            state) := by
    cases selection with
    | field responseName fieldName arguments directives children =>
        simp only [Selection.hasIncrementalDirectives, Bool.or_eq_false_iff] at hplain
        cases ha : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, ha, CollectionInContext, GroupsInContext,
            FieldsInContext, FieldInContext]
        simpa [List.any_eq_false, SelectionsPlain] using hplain
    | inlineFragment condition directives children =>
        simp only [Selection.hasIncrementalDirectives, Bool.or_eq_false_iff] at hplain
        have hn := (directives_plain variables directives hplain.1).2.1
        cases ha : selectionDirectivesAllowBool variables directives
        · cases condition <;>
            simp [collectSelection, ha, CollectionInContext, GroupsInContext]
        · cases condition with
          | none =>
              simpa [collectSelection, ha, hn]
                using collectFields_inContext schema variables parentType source children
                  hplain.2 usage state
          | some condition =>
              cases hc : doesFragmentTypeApplyBool schema parentType source condition
              · simp [collectSelection, ha, hc, CollectionInContext, GroupsInContext]
              · simpa [collectSelection, ha, hc, hn]
                  using collectFields_inContext schema variables parentType source
                    children hplain.2 usage state
  termination_by sizeOf selection

  theorem collectFields_inContext (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (hplain : SelectionsPlain selections) (usage : Option DeferUsage) (state : Nat)
      : CollectionInContext usage state
          ((collectFields schema variables parentType source selections usage).run
            state) := by
    cases selections with
    | nil => simp [collectFields, CollectionInContext, GroupsInContext]
    | cons selection rest =>
        simp only [SelectionsPlain, SelectionSet.hasIncrementalDirectives,
          Bool.or_eq_false_iff] at hplain
        have hh := collectSelection_inContext schema variables parentType source selection
          hplain.1 usage state
        have ht := collectFields_inContext schema variables parentType source rest
          hplain.2 usage state
        generalize hhout :
          (collectSelection schema variables parentType source usage selection).run state
          = headPair at hh
        generalize htout : (collectFields schema variables parentType source rest usage).run state
          = tailPair at ht
        rcases headPair with ⟨head, next⟩
        rcases tailPair with ⟨tail, final⟩
        rcases hh with ⟨hnext, hhn, hhp⟩
        rcases ht with ⟨hfinal, htn, htp⟩
        dsimp only at hnext hfinal
        subst next final
        have hp := collectionInContext_append usage ⟨rfl, hhn, hhp⟩ ⟨rfl, htn, htp⟩
        simpa [collectFields, run_bind, run_map, hhout, htout] using hp
  termination_by sizeOf selections
end

theorem collectSubfields_inContext (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    (usage : Option DeferUsage) (hfields : FieldsInContext usage fields) (state : Nat)
    : CollectionInContext usage state
        ((collectSubfields schema variables parentType source fields).run state) := by
  induction fields with
  | nil => simp [collectSubfields, CollectionInContext, GroupsInContext]
  | cons field rest ih =>
      have hf := hfields field (by simp)
      have hr : FieldsInContext usage rest := fun f h => hfields f (by simp [h])
      have hh := collectFields_inContext schema variables parentType source field.selectionSet
        hf.2.2 usage state
      have ht := ih hr
      generalize hhout :
        (collectFields schema variables parentType source field.selectionSet usage).run state
        = headPair at hh
      generalize htout : (collectSubfields schema variables parentType source rest).run state
        = tailPair at ht
      rcases headPair with ⟨head, next⟩
      rcases tailPair with ⟨tail, final⟩
      rcases hh with ⟨hnext, hhn, hhp⟩
      rcases ht with ⟨hfinal, htn, htp⟩
      dsimp only at hnext hfinal
      subst next final
      have hp := collectionInContext_append usage ⟨rfl, hhn, hhp⟩ ⟨rfl, htn, htp⟩
      simpa [collectSubfields, hf.1, run_bind, run_map, hhout, htout] using hp

def contextKeys (usage : Option DeferUsage) : List Nat :=
  usage.toList.map DeferUsage.key

def ContextWellFormed (usage : Option DeferUsage) : Prop :=
  ∀ value ∈ usage, value.key ∉ value.ancestors

theorem filteredUsages_inContext (usage : Option DeferUsage)
    (hvalid : ContextWellFormed usage) (fields : List ExecutableField)
    (hne : fields ≠ []) (hfields : FieldsInContext usage fields)
    : getFilteredDeferUsageSet fields = contextKeys usage := by
  cases fields with
  | nil => exact False.elim (hne rfl)
  | cons field rest =>
      have hf := (hfields field (by simp)).1
      cases usage with
      | none => simp [getFilteredDeferUsageSet, hf, contextKeys]
      | some usage =>
          have hall : ∀ f ∈ field :: rest, f.deferUsage = some usage :=
            fun f hm => (hfields f hm).1
          have hm : ∀ fs : List ExecutableField,
              (∀ f ∈ fs, f.deferUsage = some usage) →
              fs.filterMap ExecutableField.deferUsage = List.replicate fs.length usage := by
            intro fs hs
            induction fs with
            | nil => rfl
            | cons f fs ih =>
                simp only [List.filterMap_cons, hs f (by simp), List.length_cons,
                  List.replicate_succ]
                exact congrArg (List.cons usage) (ih (fun f hf => hs f (by simp [hf])))
          have ha : (field :: rest).any (fun f => f.deferUsage.isNone) = false := by
            apply List.any_eq_false.mpr
            intro f hf
            simp [hall f hf]
          have hv : usage.key ∉ usage.ancestors := hvalid usage (by simp)
          have hnot : ∀ key ∈ usage.ancestors, key ≠ usage.key := by
            intro key hk he
            exact hv (he ▸ hk)
          simp [getFilteredDeferUsageSet, ha, hm _ hall, List.map_replicate,
            List.replicate_succ, List.eraseDups_cons, contextKeys]
          exact ⟨hnot, Or.inr hnot⟩

theorem buildExecutionPlan_inContext (usage : Option DeferUsage)
    (hvalid : ContextWellFormed usage) (groups : CollectedFieldsMap)
    (hgroups : GroupsInContext usage groups)
    : buildExecutionPlan groups (contextKeys usage)
      = { collectedFieldsMap := groups } := by
  have heq : deferUsageSetsEquivalent (contextKeys usage) (contextKeys usage) = true := by
    cases usage <;> simp [contextKeys, deferUsageSetsEquivalent]
  have aux : ∀ (initial : ExecutionPlan),
      groups.foldl (fun plan group =>
        let usages := getFilteredDeferUsageSet group.2
        if deferUsageSetsEquivalent usages (contextKeys usage) then
          { plan with collectedFieldsMap := plan.collectedFieldsMap ++ [group] }
        else { plan with newCollectedFieldsMaps :=
          addExecutionPartition usages group plan.newCollectedFieldsMaps }) initial
      = { initial with collectedFieldsMap := initial.collectedFieldsMap ++ groups } := by
    induction groups with
    | nil =>
        intro initial; simp
    | cons group rest ih =>
        intro initial
        have hg := filteredUsages_inContext usage hvalid group.2
          (hgroups group (by simp)).1 (hgroups group (by simp)).2
        have hr : GroupsInContext usage rest := fun g h => hgroups g (by simp [h])
        simp only [List.foldl_cons, hg, heq, ↓reduceIte]
        simpa [List.append_assoc]
          using ih hr
            { initial with collectedFieldsMap := initial.collectedFieldsMap ++ [group] }
  simpa [buildExecutionPlan] using aux {}

/-- A different parent context places the entire uniform group list in one partition. -/
theorem buildExecutionPlan_deferred (usage : DeferUsage)
    (hvalid : ContextWellFormed (some usage)) (groups : CollectedFieldsMap)
    (hgroups : GroupsInContext (some usage) groups) (hne : groups ≠ [])
    : buildExecutionPlan groups []
      = { newCollectedFieldsMaps := [([usage.key], groups)] } := by
  have hdiff : deferUsageSetsEquivalent [usage.key] [] = false := rfl
  have hsame : deferUsageSetsEquivalent [usage.key] [usage.key] = true := by
    simp [deferUsageSetsEquivalent]
  have hg (group) (hm : group ∈ groups) : getFilteredDeferUsageSet group.2 = [usage.key] :=
    filteredUsages_inContext (some usage) hvalid group.2 (hgroups group hm).1 (hgroups group hm).2
  have aux (rest : CollectedFieldsMap)
      (hr : ∀ group ∈ rest, getFilteredDeferUsageSet group.2 = [usage.key])
      (accumulated : CollectedFieldsMap) :
      rest.foldl (fun (plan : ExecutionPlan) group =>
        let usages := getFilteredDeferUsageSet group.2
        if deferUsageSetsEquivalent usages [] then
          { plan with collectedFieldsMap := plan.collectedFieldsMap ++ [group] }
        else { plan with newCollectedFieldsMaps :=
          addExecutionPartition usages group plan.newCollectedFieldsMaps })
        { newCollectedFieldsMaps := [([usage.key], accumulated)] }
      = { newCollectedFieldsMaps := [([usage.key], accumulated ++ rest)] } := by
    induction rest generalizing accumulated with
    | nil => simp
    | cons group rest ih =>
        simp only [List.foldl_cons, hr group (by simp), hdiff, Bool.false_eq_true,
          ↓reduceIte, addExecutionPartition, hsame]
        simpa [List.append_assoc]
          using ih (fun g hm => hr g (by simp [hm])) (accumulated ++ [group])
  cases groups with
  | nil => exact False.elim (hne rfl)
  | cons group rest =>
      unfold buildExecutionPlan
      simp only [List.foldl_cons, hg group (by simp), hdiff, Bool.false_eq_true,
        ↓reduceIte, addExecutionPartition]
      simpa using aux rest (fun g hm => hg g (by simp [hm])) [group]

end GraphQL.IncrementalDelivery.Semantics
