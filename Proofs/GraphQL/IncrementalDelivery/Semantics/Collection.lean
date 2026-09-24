import Proofs.GraphQL.IncrementalDelivery.Semantics.FieldExecution

/-! Collection invariants for execution without incremental directives. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

variable {ObjectRef : Type}

/-- Id's pure operation is the identity; witness: definitional equality. -/
theorem id_pure_eq {α : Type} (value : α) : (pure value : Id α) = value := rfl

/-- Id binding applies its continuation directly; witness: definitional equality. -/
@[simp]
theorem id_bind_eq {α β : Type} (value : α) (next : α → Id β)
    : (value >>= next : Id β) = next value :=
  rfl

/-- Mapping an Id value applies the function directly; witness: definitional equality. -/
@[simp]
theorem id_map_eq {α β : Type} (f : α → β) (value : α) : (f <$> value : Id β) = f value :=
  rfl

/-- State binding threads the intermediate state; witness: definitional equality. -/
@[simp]
theorem run_bind {α β : Type} (action : StateM Nat α) (next : α → StateM Nat β)
    (state : Nat)
    : (action >>= next).run state
      = (next (action.run state).1).run (action.run state).2 :=
  rfl

/-- State mapping changes only the returned value; witness: definitional equality. -/
@[simp]
theorem run_map {α β : Type} (f : α → β) (action : StateM Nat α) (state : Nat)
    : (f <$> action).run state = (f (action.run state).1, (action.run state).2) :=
  rfl

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

abbrev DirectivesPlain (directives : List DirectiveApplication) : Prop :=
  directives.any DirectiveApplication.isIncremental = false

abbrev SelectionsPlain (selections : List Selection) : Prop :=
  SelectionSet.hasIncrementalDirectives selections = false

abbrev FieldPlain (field : ExecutableField) : Prop :=
  field.deferUsage = none
  ∧ DirectivesPlain field.directives
  ∧ SelectionsPlain field.selectionSet

abbrev FieldsPlain (fields : List ExecutableField) : Prop :=
  ∀ field ∈ fields, FieldPlain field

abbrev GroupsPlain (groups : CollectedFieldsMap) : Prop :=
  ∀ group ∈ groups, FieldsPlain group.snd

def eraseField (field : ExecutableField) : GraphQL.Execution.ExecutableField :=
  {
    fieldName := field.fieldName
    arguments := field.arguments
    selectionSet := SelectionSet.eraseIncrementalDirectives field.selectionSet
  }

def eraseGroup (group : Name × List ExecutableField)
    : Name × List GraphQL.Execution.ExecutableField :=
  (group.fst, group.snd.map eraseField)

def eraseGroups (groups : CollectedFieldsMap) := groups.map eraseGroup

/-- Plain directives preserve filtering and enable neither defer nor stream; induction on
directives.
-/
theorem directives_plain (variables : VariableValues)
    (directives : List DirectiveApplication) (h : DirectivesPlain directives)
    : selectionDirectivesAllowBool variables directives
        = GraphQL.Execution.selectionDirectivesAllowBool variables
            (directives.filterMap DirectiveApplication.eraseIncremental?)
      ∧ activeDefer? variables directives = none
      ∧ getStreamUsage variables directives = .ok none := by
  induction directives with
  | nil =>
      simp [selectionDirectivesAllowBool, GraphQL.Execution.selectionDirectivesAllowBool,
      activeDefer?, getStreamUsage]
  | cons directive rest ih =>
      simp only [DirectivesPlain, List.any_cons, Bool.or_eq_false_iff] at h
      obtain ⟨ha, hr⟩ := h
      obtain ⟨ih1, ih2, ih3⟩ := ih hr
      cases directive <;>
        simp_all [DirectiveApplication.isIncremental, selectionDirectivesAllowBool,
          GraphQL.Execution.selectionDirectivesAllowBool, DirectiveApplication.eraseIncremental?,
          directiveAllowsSelectionBool, GraphQL.Execution.directiveAllowsSelectionBool,
          activeDefer?, getStreamUsage] <;> rfl

/-- Field erasure commutes with ordered group insertion, by induction on existing groups.
-/
theorem eraseGroups_add (group : Name × List ExecutableField)
    (groups : CollectedFieldsMap)
    : eraseGroups (addExecutableGroup group groups)
      = GraphQL.Execution.addExecutableGroup (eraseGroup group) (eraseGroups groups) := by
  induction groups with
  | nil => rfl
  | cons head rest ih =>
      rcases group with ⟨key, fields⟩
      rcases head with ⟨name, existing⟩
      by_cases h : name == key
      · simp [addExecutableGroup, GraphQL.Execution.addExecutableGroup, h,
          eraseGroups, eraseGroup, List.map_append]
      · simpa [addExecutableGroup, GraphQL.Execution.addExecutableGroup, h,
          eraseGroups, eraseGroup] using congrArg (List.cons (name, existing.map eraseField)) ih

/-- Group erasure commutes with merging; witness: fold induction and eraseGroups_add. -/
theorem eraseGroups_merge (left right : CollectedFieldsMap)
    : eraseGroups (mergeExecutableGroups left right)
      = GraphQL.Execution.mergeExecutableGroups (eraseGroups left)
          (eraseGroups right) := by
  induction right generalizing left with
  | nil => rfl
  | cons group rest ih =>
      simp only [mergeExecutableGroups, List.foldl_cons, eraseGroups, List.map_cons,
        GraphQL.Execution.mergeExecutableGroups]
      exact (ih (addExecutableGroup group left)).trans
        (congrArg (fun gs => GraphQL.Execution.mergeExecutableGroups gs (eraseGroups rest))
          (eraseGroups_add group left))

/-- Insertion preserves plain field groups, by checking matching and fresh response names.
-/
theorem groupsPlain_add (group : Name × List ExecutableField)
    (groups : CollectedFieldsMap) (hg : FieldsPlain group.snd) (hs : GroupsPlain groups)
    : GroupsPlain (addExecutableGroup group groups) := by
  induction groups with
  | nil => simpa [addExecutableGroup, GroupsPlain] using hg
  | cons head rest ih =>
      have hh : FieldsPlain head.snd := hs head (by simp)
      have ht : GroupsPlain rest := fun g h => hs g (by simp [h])
      rcases group with ⟨key, fields⟩
      rcases head with ⟨name, existing⟩
      by_cases h : name == key
      · simp only [addExecutableGroup, h, ↓reduceIte]
        intro candidate hc field hf
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · rcases List.mem_append.mp hf with hf | hf
          · exact hh field hf
          · exact hg field hf
        · exact ht candidate hc field hf
      · simpa [addExecutableGroup, h, GroupsPlain] using And.intro hh (ih ht)

/-- Merging preserves plain groups, by fold induction using groupsPlain_add. -/
theorem groupsPlain_merge (left right : CollectedFieldsMap)
    (hl : GroupsPlain left) (hr : GroupsPlain right)
    : GroupsPlain (mergeExecutableGroups left right) := by
  induction right generalizing left with
  | nil => exact hl
  | cons group rest ih =>
      exact ih (addExecutableGroup group left)
        (groupsPlain_add group left (hr group (by simp)) hl)
        (fun g h => hr g (by simp [h]))

/-- The state supply is unchanged and collection creates no defer usages. -/
def CollectionMatches (basic : List (Name × List GraphQL.Execution.ExecutableField))
    (state : Nat) (output : FieldCollection × Nat)
    : Prop :=
  output.2 = state
  ∧ output.1.newDeferUsages = []
  ∧ GroupsPlain output.1.fields
  ∧ eraseGroups output.1.fields = basic

/-- Combining matching collections preserves state and erasure, using the group-merge
witnesses.
-/
theorem collectionMatches_append {left right : FieldCollection} {state : Nat}
    {basicLeft basicRight : List (Name × List GraphQL.Execution.ExecutableField)}
    (hl : CollectionMatches basicLeft state (left, state))
    (hr : CollectionMatches basicRight state (right, state))
    : CollectionMatches (GraphQL.Execution.mergeExecutableGroups basicLeft basicRight)
        state (left.append right, state) := by
  rcases hl with ⟨_, hln, hlp, hle⟩
  rcases hr with ⟨_, hrn, hrp, hre⟩
  dsimp only at hln hrn hlp hrp hle hre
  exact ⟨
    rfl,
    by simp [FieldCollection.append, hln, hrn],
    groupsPlain_merge _ _ hlp hrp,
    by
      simpa [FieldCollection.append, hle, hre]
        using eraseGroups_merge left.fields right.fields
  ⟩

mutual
  /-- A plain selection collects exactly its erasure without new work keys; mutual syntax
  induction.
  -/
  theorem collectSelection_plain (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selection : Selection)
      (hplain : selection.hasIncrementalDirectives = false) (state : Nat)
      : CollectionMatches
          (GraphQL.Execution.collectSelection schema variables parentType source
            selection.eraseIncrementalDirectives)
          state
          ((collectSelection schema variables parentType source none selection).run
            state) := by
    cases selection with
    | field responseName fieldName arguments directives children =>
        simp only [Selection.hasIncrementalDirectives, Bool.or_eq_false_iff] at hplain
        have hd := (directives_plain variables directives hplain.1).1
        cases ha : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, GraphQL.Execution.collectSelection,
            Selection.eraseIncrementalDirectives, ← hd, ha, CollectionMatches,
            GroupsPlain, FieldsPlain, FieldPlain,
            eraseGroups, eraseGroup, eraseField]
        simpa [List.any_eq_false, SelectionsPlain] using hplain
    | inlineFragment condition directives children =>
        simp only [Selection.hasIncrementalDirectives, Bool.or_eq_false_iff] at hplain
        obtain ⟨hd, hn, _⟩ := directives_plain variables directives hplain.1
        cases ha : selectionDirectivesAllowBool variables directives
        · cases condition <;>
            simp [collectSelection, GraphQL.Execution.collectSelection,
              Selection.eraseIncrementalDirectives, ← hd, ha, CollectionMatches,
              GroupsPlain, eraseGroups]
        · cases condition with
          | none =>
              simpa [collectSelection, GraphQL.Execution.collectSelection,
                Selection.eraseIncrementalDirectives, ← hd, ha, hn]
                using collectFields_plain schema variables parentType source children
                  hplain.2 state
          | some condition =>
              cases hc : doesFragmentTypeApplyBool schema parentType source condition
              · simp [collectSelection, GraphQL.Execution.collectSelection,
                  Selection.eraseIncrementalDirectives, ← hd, ha, hc, CollectionMatches,
                  GroupsPlain, eraseGroups]
              · simpa [collectSelection, GraphQL.Execution.collectSelection,
                  Selection.eraseIncrementalDirectives, ← hd, ha, hc, hn]
                  using collectFields_plain schema variables parentType source children
                    hplain.2 state
  termination_by sizeOf selection

  /-- Plain lists preserve collection state and erasure; compose head/tail induction
  witnesses.
  -/
  theorem collectFields_plain (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (hplain : SelectionsPlain selections) (state : Nat)
      : CollectionMatches
          (GraphQL.Execution.collectFields schema variables parentType source
            (SelectionSet.eraseIncrementalDirectives selections))
          state
          ((collectFields schema variables parentType source selections).run state) := by
    cases selections with
    | nil =>
        simp [collectFields, GraphQL.Execution.collectFields,
        SelectionSet.eraseIncrementalDirectives, CollectionMatches, GroupsPlain, eraseGroups]
    | cons selection rest =>
        simp only [SelectionsPlain, SelectionSet.hasIncrementalDirectives,
          Bool.or_eq_false_iff] at hplain
        have hh :=
          collectSelection_plain schema variables parentType source selection hplain.1 state
        have ht := collectFields_plain schema variables parentType source rest hplain.2 state
        generalize hhout :
          (collectSelection schema variables parentType source none selection).run state
          = headPair at hh
        generalize htout : (collectFields schema variables parentType source rest).run state
          = tailPair at ht
        rcases headPair with ⟨head, next⟩
        rcases tailPair with ⟨tail, final⟩
        rcases hh with ⟨hnext, hhn, hhp, hhe⟩
        rcases ht with ⟨hfinal, htn, htp, hte⟩
        dsimp only at hnext hfinal
        subst next final
        have hp := collectionMatches_append ⟨rfl, hhn, hhp, hhe⟩ ⟨rfl, htn, htp, hte⟩
        simpa [collectFields, SelectionSet.eraseIncrementalDirectives,
          GraphQL.Execution.collectFields, run_bind, run_map, hhout, htout] using hp
  termination_by sizeOf selections
end

/-- Plain subfield collection matches ordinary collection, by field-list induction and
erasure.
-/
theorem collectSubfields_plain (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    (hplain : FieldsPlain fields) (state : Nat)
    : CollectionMatches
        (GraphQL.Execution.collectSubfields schema variables parentType source
          (fields.map eraseField))
        state
        ((collectSubfields schema variables parentType source fields).run state) := by
  induction fields with
  | nil => simp [collectSubfields, GraphQL.Execution.collectSubfields,
      CollectionMatches, GroupsPlain, eraseGroups]
  | cons field rest ih =>
      have hf := hplain field (by simp)
      have hr : FieldsPlain rest := fun f h => hplain f (by simp [h])
      have hh :=
        collectFields_plain schema variables parentType source field.selectionSet hf.2.2 state
      have ht := ih hr
      generalize hhout :
        (collectFields schema variables parentType source field.selectionSet).run state
        = headPair at hh
      generalize htout : (collectSubfields schema variables parentType source rest).run state
        = tailPair at ht
      rcases headPair with ⟨head, next⟩
      rcases tailPair with ⟨tail, final⟩
      rcases hh with ⟨hnext, hhn, hhp, hhe⟩
      rcases ht with ⟨hfinal, htn, htp, hte⟩
      dsimp only at hnext hfinal
      subst next final
      have hp := collectionMatches_append ⟨rfl, hhn, hhp, hhe⟩ ⟨rfl, htn, htp, hte⟩
      simpa [collectSubfields, GraphQL.Execution.collectSubfields, eraseField, hf.1,
        run_bind, run_map, hhout, htout]
        using hp

/-- Plain fields have no filtered defer usages, witnessed by their absent defer owner. -/
theorem filteredUsages_plain (fields : List ExecutableField) (hplain : FieldsPlain fields)
    : getFilteredDeferUsageSet fields = [] := by
  cases fields with
  | nil => rfl
  | cons field rest =>
      have hf := (hplain field (by simp)).1
      simp [getFilteredDeferUsageSet, hf]

/-- A plain plan contains only immediate groups; fold induction uses filteredUsages_plain.
-/
theorem buildExecutionPlan_plain (groups : CollectedFieldsMap)
    (hplain : GroupsPlain groups)
    : buildExecutionPlan groups = { collectedFieldsMap := groups } := by
  have aux : ∀ (initial : ExecutionPlan),
      groups.foldl (fun plan group =>
        let usages := getFilteredDeferUsageSet group.2
        if deferUsageSetsEquivalent usages [] then
          { plan with collectedFieldsMap := plan.collectedFieldsMap ++ [group] }
        else { plan with newCollectedFieldsMaps :=
          addExecutionPartition usages group plan.newCollectedFieldsMaps }) initial
      = { initial with collectedFieldsMap := initial.collectedFieldsMap ++ groups } := by
    induction groups with
    | nil =>
        intro initial; simp
    | cons group rest ih =>
        intro initial
        have hg := filteredUsages_plain group.snd (hplain group (by simp))
        have hr : GroupsPlain rest := fun g h => hplain g (by simp [h])
        simp only [List.foldl_cons, hg, deferUsageSetsEquivalent, List.all_nil,
          Bool.and_self, ↓reduceIte]
        simpa [List.append_assoc, deferUsageSetsEquivalent]
          using ih hr
            { initial with collectedFieldsMap := initial.collectedFieldsMap ++ [group] }
  simpa [buildExecutionPlan] using aux {}

end GraphQL.IncrementalDelivery.Semantics
