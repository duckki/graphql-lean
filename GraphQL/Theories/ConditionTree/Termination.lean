import GraphQL.Theories.ConditionTree

/-! Shared termination support for condition-tree execution and reduction.

Both consumers recurse over a tree of selection-set trees. Structural traversal stays
inside one response boundary; constructing a tree from a merged field group strictly
decreases response depth.
-/

namespace GraphQL
namespace ConditionTree
namespace Termination

-----------------------------------------------------------------------------------------
-- Shared tree-of-trees recursion measure
-----------------------------------------------------------------------------------------

theorem triple_lt_of_depth_le_of_tail_lt
    {leftDepth rightDepth control leftTail rightTail : Nat}
    (hdepth : leftDepth ≤ rightDepth)
    (htail : leftTail < rightTail)
    : Prod.Lex (fun left right : Nat => left < right)
        (Prod.Lex (fun left right : Nat => left < right)
          (fun left right : Nat => left < right))
        (leftDepth, control, leftTail)
        (rightDepth, control, rightTail) := by
  rcases Nat.lt_or_eq_of_le hdepth with hstrict | hequal
  · exact Prod.Lex.left _ _ hstrict
  · subst rightDepth
    exact Prod.Lex.right leftDepth (Prod.Lex.right control htail)

-- Inline fragments stay within one condition-tree boundary. Only response fields add
-- a level at which value completion can recursively execute another extracted tree.
private theorem selection_size_le_cons_size (selection : Selection)
    (rest : List Selection)
    : selection.size ≤ SelectionSet.size (selection :: rest) := by
  simp [SelectionSet.size]

private theorem selectionSet_size_tail_lt_cons (selection : Selection)
    (rest : List Selection)
    : SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  cases selection <;> simp [SelectionSet.size, Selection.size] <;> omega

mutual
  def selectionResponseDepth : Selection -> Nat
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetResponseDepth selectionSet + 1
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetResponseDepth selectionSet
  termination_by selection => 2 * selection.size
  decreasing_by
    all_goals
      simp [Selection.size]
      omega

  def selectionSetResponseDepth : List Selection -> Nat
    | [] => 0
    | selection :: rest =>
        max (selectionResponseDepth selection) (selectionSetResponseDepth rest)
  termination_by selectionSet => 2 * SelectionSet.size selectionSet + 1
  decreasing_by
    all_goals
      have hsize := selection_size_le_cons_size selection rest
      have htail := selectionSet_size_tail_lt_cons selection rest
      first
      | exact
          Nat.add_lt_add_right
            (Nat.mul_lt_mul_of_pos_left htail (by omega)) 1
      | omega
end

theorem selectionSetResponseDepth_append (left right : List Selection)
    : selectionSetResponseDepth (left ++ right)
      = max (selectionSetResponseDepth left) (selectionSetResponseDepth right) := by
  induction left with
  | nil => simp [selectionSetResponseDepth]
  | cons selection rest ih =>
      simp [selectionSetResponseDepth, ih, Nat.max_assoc]

theorem selectionSetResponseDepth_singleton (selection : Selection)
    : selectionSetResponseDepth [selection] = selectionResponseDepth selection := by
  rw [selectionSetResponseDepth]
  simp [selectionSetResponseDepth]

theorem mergeSelectionSets_append (left right : List Selection)
    : SelectionSet.mergeSelectionSets (left ++ right)
      = SelectionSet.mergeSelectionSets left
        ++ SelectionSet.mergeSelectionSets right := by
  simp [SelectionSet.mergeSelectionSets]

def conditionFieldGroupResponseDepth (group : FieldGroup) : Nat :=
  selectionSetResponseDepth group.selections

def conditionFieldGroupsResponseDepth : List FieldGroup -> Nat
  | [] => 0
  | group :: rest =>
      max (conditionFieldGroupResponseDepth group)
        (conditionFieldGroupsResponseDepth rest)

mutual
  def conditionTreeResponseDepth (tree : Tree) : Nat :=
    max (conditionFieldGroupsResponseDepth tree.fields)
      (conditionBranchesResponseDepth tree.branches)
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def conditionBranchesResponseDepth : List (Branch Tree) -> Nat
    | [] => 0
    | branch :: rest =>
        max (conditionTreeResponseDepth branch.body) (conditionBranchesResponseDepth rest)
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

private theorem conditionBranchesResponseDepth_append (left right : List (Branch Tree))
    : conditionBranchesResponseDepth (left ++ right)
      = max (conditionBranchesResponseDepth left)
          (conditionBranchesResponseDepth right) := by
  induction left with
  | nil => simp [conditionBranchesResponseDepth]
  | cons branch rest ih =>
      simp [conditionBranchesResponseDepth, ih, Nat.max_assoc]

private theorem conditionFieldGroupResponseDepth_appendField
    (group : FieldGroup) (field : Field)
    : conditionFieldGroupResponseDepth { group with rest := group.rest ++ [field] }
      ≤ max (conditionFieldGroupResponseDepth group)
          (selectionResponseDepth (field.toSelection group.responseName)) := by
  have hselections :
      ({ group with rest := group.rest ++ [field] } : FieldGroup).selections
        = group.selections ++ [field.toSelection group.responseName] := by
    simp [FieldGroup.selections, FieldGroup.fields, List.map_append]
  rw [conditionFieldGroupResponseDepth, hselections,
    selectionSetResponseDepth_append, selectionSetResponseDepth_singleton,
    conditionFieldGroupResponseDepth]
  exact Nat.le_refl _

private theorem conditionFieldGroupsResponseDepth_addFieldWithResponseName
    (responseName : Name) (field : Field) (groups : List FieldGroup)
    : conditionFieldGroupsResponseDepth
        (addFieldWithResponseName responseName field groups)
      ≤ max (conditionFieldGroupsResponseDepth groups)
          (selectionResponseDepth (field.toSelection responseName)) := by
  induction groups with
  | nil =>
      simp [addFieldWithResponseName, conditionFieldGroupsResponseDepth,
        conditionFieldGroupResponseDepth, FieldGroup.selections, FieldGroup.fields,
        selectionSetResponseDepth, selectionResponseDepth, Field.toSelection]
  | cons group rest ih =>
      simp only [addFieldWithResponseName]
      split <;> rename_i hname
      · simp only [conditionFieldGroupsResponseDepth]
        apply Nat.max_le.mpr
        constructor
        · exact Nat.le_trans
            (conditionFieldGroupResponseDepth_appendField group field)
            (Nat.max_le.mpr
              ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _), by
                have heq : group.responseName = responseName := (beq_iff_eq.mp hname).symm
                subst responseName
                exact Nat.le_max_right _ _⟩)
        · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
      · simp only [conditionFieldGroupsResponseDepth]
        apply Nat.max_le.mpr
        constructor
        · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        · exact Nat.le_trans ih
            (Nat.max_le.mpr
              ⟨Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _),
                Nat.le_max_right _ _⟩)

private theorem conditionFieldGroupsResponseDepth_addFieldToGroups
    (field : NamedField) (groups : List FieldGroup)
    : conditionFieldGroupsResponseDepth (addFieldToGroups field groups)
      ≤ max (conditionFieldGroupsResponseDepth groups)
          (selectionResponseDepth field.toSelection) := by
  rcases field with ⟨responseName, field⟩
  exact conditionFieldGroupsResponseDepth_addFieldWithResponseName responseName field groups

private theorem conditionFieldGroupsResponseDepth_fold_addFieldToGroups
    (fields : List NamedField) (groups : List FieldGroup)
    : conditionFieldGroupsResponseDepth
        (fields.foldl (fun result field => addFieldToGroups field result) groups)
      ≤ max (conditionFieldGroupsResponseDepth groups)
          (selectionSetResponseDepth (fields.map NamedField.toSelection)) := by
  induction fields generalizing groups with
  | nil => simp [selectionSetResponseDepth]
  | cons field rest ih =>
      simp only [List.foldl_cons, List.map_cons, selectionSetResponseDepth]
      have hadded := conditionFieldGroupsResponseDepth_addFieldToGroups field groups
      have hrest := ih (addFieldToGroups field groups)
      exact Nat.le_trans hrest <| calc
        max (conditionFieldGroupsResponseDepth (addFieldToGroups field groups))
              (selectionSetResponseDepth (rest.map NamedField.toSelection))
            ≤ max
                (max (conditionFieldGroupsResponseDepth groups)
                  (selectionResponseDepth field.toSelection))
                (selectionSetResponseDepth (rest.map NamedField.toSelection)) :=
          Nat.max_le.mpr
            ⟨Nat.le_trans hadded (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
        _ = max (conditionFieldGroupsResponseDepth groups)
              (max (selectionResponseDepth field.toSelection)
                (selectionSetResponseDepth (rest.map NamedField.toSelection))) :=
          Nat.max_assoc _ _ _

theorem conditionFieldGroupsResponseDepth_collectFieldGroups (fields : List NamedField)
    : conditionFieldGroupsResponseDepth (collectFieldGroups fields)
      ≤ selectionSetResponseDepth (fields.map NamedField.toSelection) := by
  unfold collectFieldGroups
  simpa [conditionFieldGroupsResponseDepth] using
    conditionFieldGroupsResponseDepth_fold_addFieldToGroups fields []

mutual
  private theorem tree_modifyAtCondition?_responseDepth_le
      (target : Condition) (modify : Tree -> Tree) (addedDepth : Nat)
      (tree modifiedTree : Tree)
      (hmodify
        : ∀ node,
            conditionTreeResponseDepth (modify node)
            ≤ max (conditionTreeResponseDepth node) addedDepth)
      (hresult : tree.modifyAtCondition? target modify = some modifiedTree)
      : conditionTreeResponseDepth modifiedTree
        ≤ max (conditionTreeResponseDepth tree) addedDepth := by
    rw [Tree.modifyAtCondition?] at hresult
    split at hresult
    · cases hresult
      exact hmodify tree
    · split at hresult
      · contradiction
      · rename_i modifiedBranches hbranches
        cases hresult
        simp only [conditionTreeResponseDepth]
        apply Nat.max_le.mpr
        constructor
        · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        · exact Nat.le_trans
            (modifyBranchesAtCondition?_responseDepth_le target modify addedDepth
              tree.branches modifiedBranches hmodify hbranches)
            (Nat.max_le.mpr
              ⟨Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _),
                Nat.le_max_right _ _⟩)

  private theorem modifyBranchesAtCondition?_responseDepth_le
      (target : Condition) (modify : Tree -> Tree) (addedDepth : Nat)
      (branches modifiedBranches : List (Branch Tree))
      (hmodify
        : ∀ node,
            conditionTreeResponseDepth (modify node)
            ≤ max (conditionTreeResponseDepth node) addedDepth)
      (hresult
        : modifyBranchesAtCondition? target modify branches = some modifiedBranches)
      : conditionBranchesResponseDepth modifiedBranches
        ≤ max (conditionBranchesResponseDepth branches) addedDepth := by
    cases branches with
    | nil => simp [modifyBranchesAtCondition?] at hresult
    | cons branch rest =>
        rw [modifyBranchesAtCondition?] at hresult
        split at hresult
        · rename_i modifiedBody hbody
          cases hresult
          simp only [conditionBranchesResponseDepth]
          apply Nat.max_le.mpr
          constructor
          · exact Nat.le_trans
              (tree_modifyAtCondition?_responseDepth_le target modify addedDepth
                branch.body modifiedBody hmodify hbody)
              (Nat.max_le.mpr
                ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
                  Nat.le_max_right _ _⟩)
          · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
        · split at hresult
          · contradiction
          · rename_i modifiedRest hrest
            cases hresult
            simp only [conditionBranchesResponseDepth]
            apply Nat.max_le.mpr
            constructor
            · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
            · exact Nat.le_trans
                (modifyBranchesAtCondition?_responseDepth_le target modify
                  addedDepth rest modifiedRest hmodify hrest)
                (Nat.max_le.mpr
                  ⟨Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _),
                    Nat.le_max_right _ _⟩)
end

private theorem tree_appendAtCondition?_responseDepth_le
    (tree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    (modifiedTree : Tree)
    (hresult : tree.appendAtCondition? target fields branches = some modifiedTree)
    : conditionTreeResponseDepth modifiedTree
      ≤ max (conditionTreeResponseDepth tree)
          (max (selectionSetResponseDepth (fields.map NamedField.toSelection))
            (conditionBranchesResponseDepth branches)) := by
  unfold Tree.appendAtCondition? at hresult
  apply tree_modifyAtCondition?_responseDepth_le target _
    (max (selectionSetResponseDepth (fields.map NamedField.toSelection))
      (conditionBranchesResponseDepth branches))
    tree modifiedTree _ hresult
  intro node
  simp only [conditionTreeResponseDepth]
  rw [conditionBranchesResponseDepth_append]
  have hfields :=
    conditionFieldGroupsResponseDepth_fold_addFieldToGroups fields node.fields
  calc
    max
          (conditionFieldGroupsResponseDepth
            (fields.foldl
              (fun groups field => addFieldToGroups field groups) node.fields))
          (max (conditionBranchesResponseDepth node.branches)
            (conditionBranchesResponseDepth branches))
        ≤ max
            (max (conditionFieldGroupsResponseDepth node.fields)
              (selectionSetResponseDepth (fields.map NamedField.toSelection)))
            (max (conditionBranchesResponseDepth node.branches)
              (conditionBranchesResponseDepth branches)) :=
      Nat.max_le.mpr ⟨Nat.le_trans hfields (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    _ = max
          (max (conditionFieldGroupsResponseDepth node.fields)
            (conditionBranchesResponseDepth node.branches))
          (max (selectionSetResponseDepth (fields.map NamedField.toSelection))
            (conditionBranchesResponseDepth branches)) := by
      ac_rfl

private theorem conditionBranchesResponseDepth_branchesForPath
    (path : List (BranchCondition × Condition)) (fields : List NamedField)
    : conditionBranchesResponseDepth (branchesForPath path fields)
      ≤ selectionSetResponseDepth (fields.map NamedField.toSelection) := by
  induction path with
  | nil => simp [branchesForPath, conditionBranchesResponseDepth]
  | cons edge rest ih =>
      rcases edge with ⟨branchCondition, condition⟩
      cases rest with
      | nil =>
          simp only [branchesForPath, conditionBranchesResponseDepth,
            conditionTreeResponseDepth, Nat.max_zero]
          exact conditionFieldGroupsResponseDepth_collectFieldGroups fields
      | cons next tail =>
          simp only [branchesForPath, conditionBranchesResponseDepth,
            conditionTreeResponseDepth, conditionFieldGroupsResponseDepth,
            Nat.zero_max, Nat.max_zero]
          exact ih

private theorem tree_insertField_responseDepth_le
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (sourcePath : List BranchCondition)
    (target : Condition) (field : NamedField)
    : conditionTreeResponseDepth
        (tree.insertField schema inheritedBooleanCondition sourcePath target field)
      ≤ max (conditionTreeResponseDepth tree)
          (selectionResponseDepth field.toSelection) := by
  unfold Tree.insertField
  split
  · rename_i modifiedTree hmodifiedTree
    exact Nat.le_trans
      (tree_appendAtCondition?_responseDepth_le tree target [field] []
        modifiedTree hmodifiedTree)
      (by simp [selectionSetResponseDepth, conditionBranchesResponseDepth])
  · split
    · exact Nat.le_max_left _ _
    · rename_i sourcePath hsourcePath
      let sourcePrefix := deepestExistingPrefix tree tree.condition sourcePath
      let shrunk :=
        shrinkBranches schema inheritedBooleanCondition sourcePrefix.1 target
          (sourcePrefix.2.map Prod.fst)
      let retainedPath :=
        match pathForBranches? schema inheritedBooleanCondition sourcePrefix.1
            shrunk with
        | some path =>
            if pathEnd sourcePrefix.1 path = target then path else sourcePrefix.2
        | none => sourcePrefix.2
      let retainedPrefix :=
        deepestExistingPrefix tree sourcePrefix.1 retainedPath
      change
        conditionTreeResponseDepth
            (match retainedPrefix.2 with
            | [] =>
                match tree.appendAtCondition? retainedPrefix.1 [field] [] with
                | some modifiedTree => modifiedTree
                | none => tree
            | missingPath =>
                let simplePath := erasePathCycles missingPath
                match tree.appendAtCondition? retainedPrefix.1 []
                    (branchesForPath simplePath [field]) with
                | some modifiedTree => modifiedTree
                | none => tree)
          ≤ max (conditionTreeResponseDepth tree)
              (selectionResponseDepth field.toSelection)
      cases retainedPrefix.2 with
      | nil =>
          simp only
          split
          · rename_i modifiedTree hmodifiedTree
            exact Nat.le_trans
              (tree_appendAtCondition?_responseDepth_le tree retainedPrefix.1 [field]
                [] modifiedTree hmodifiedTree)
              (by simp [selectionSetResponseDepth, conditionBranchesResponseDepth])
          · exact Nat.le_max_left _ _
      | cons head rest =>
          simp only
          let simplePath := erasePathCycles (head :: rest)
          split
          · rename_i modifiedTree hmodifiedTree
            have hbranches :
                max (selectionSetResponseDepth ([] : List Selection))
                    (conditionBranchesResponseDepth
                      (branchesForPath simplePath [field]))
                  ≤ selectionResponseDepth field.toSelection := by
              simpa [selectionSetResponseDepth] using
                conditionBranchesResponseDepth_branchesForPath simplePath [field]
            exact Nat.le_trans
              (tree_appendAtCondition?_responseDepth_le tree retainedPrefix.1 []
                (branchesForPath simplePath [field]) modifiedTree hmodifiedTree)
              (Nat.max_le.mpr
                ⟨Nat.le_max_left _ _,
                  Nat.le_trans hbranches (Nat.le_max_right _ _)⟩)
          · exact Nat.le_max_left _ _

private theorem conditionTreeResponseDepth_insertSelections
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition) (branches : List BranchCondition)
    (tree : Tree) (selectionSet : List Selection)
    : conditionTreeResponseDepth
        (insertSelections schema inheritedBooleanCondition currentCondition branches tree
          selectionSet)
      ≤ max (conditionTreeResponseDepth tree)
          (selectionSetResponseDepth selectionSet) := by
  cases selectionSet with
  | nil => simp [insertSelections, selectionSetResponseDepth]
  | cons selection rest =>
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          rw [insertSelections]
          let sourceField : Selection :=
            .field responseName fieldName arguments directives childSelectionSet
          let storedField : NamedField :=
            {
              responseName
              field := { fieldName, arguments, selectionSet := childSelectionSet }
            }
          let treeAfterField :=
            match branchConditionsForDirectives? directives with
            | none => tree
            | some nextBranches =>
                match conditionForBranches? schema inheritedBooleanCondition
                        currentCondition nextBranches with
                | none => tree
                | some nextCondition =>
                    tree.insertField schema inheritedBooleanCondition
                      (branches ++ nextBranches) nextCondition storedField
          have hfield :
              conditionTreeResponseDepth treeAfterField
                ≤ max (conditionTreeResponseDepth tree)
                    (selectionResponseDepth sourceField) := by
            unfold treeAfterField
            split
            · exact Nat.le_max_left _ _
            · split
              · exact Nat.le_max_left _ _
              · simpa [storedField, sourceField, NamedField.toSelection,
                  Field.toSelection, selectionResponseDepth] using
                  tree_insertField_responseDepth_le schema
                    inheritedBooleanCondition tree (branches ++ ‹_›) ‹_› storedField
          have hrest :=
            conditionTreeResponseDepth_insertSelections schema inheritedBooleanCondition
              currentCondition branches treeAfterField rest
          exact Nat.le_trans hrest <| calc
            max (conditionTreeResponseDepth treeAfterField)
                  (selectionSetResponseDepth rest)
                ≤ max
                    (max (conditionTreeResponseDepth tree)
                      (selectionResponseDepth sourceField))
                    (selectionSetResponseDepth rest) :=
              Nat.max_le.mpr
                ⟨Nat.le_trans hfield (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
            _ = max (conditionTreeResponseDepth tree)
                  (selectionSetResponseDepth (sourceField :: rest)) := by
              simp only [selectionSetResponseDepth]
              ac_rfl
      | inlineFragment typeCondition directives childSelectionSet =>
          rw [insertSelections]
          let treeAfterFragment :=
            match branchConditionsForInlineFragment? typeCondition directives with
            | none => tree
            | some nextBranches =>
                match conditionForBranches? schema inheritedBooleanCondition
                    currentCondition nextBranches with
                | none => tree
                | some nextCondition =>
                    insertSelections schema inheritedBooleanCondition nextCondition
                      (branches ++ nextBranches) tree childSelectionSet
          have hfragment :
              conditionTreeResponseDepth treeAfterFragment
                ≤ max (conditionTreeResponseDepth tree)
                    (selectionSetResponseDepth childSelectionSet) := by
            unfold treeAfterFragment
            split
            · exact Nat.le_max_left _ _
            · split
              · exact Nat.le_max_left _ _
              · exact conditionTreeResponseDepth_insertSelections schema
                  inheritedBooleanCondition ‹Condition›
                  (branches ++ ‹List BranchCondition›) tree childSelectionSet
          have hrest :=
            conditionTreeResponseDepth_insertSelections schema inheritedBooleanCondition
              currentCondition branches treeAfterFragment rest
          exact Nat.le_trans hrest <| calc
            max (conditionTreeResponseDepth treeAfterFragment)
                  (selectionSetResponseDepth rest)
                ≤ max
                    (max (conditionTreeResponseDepth tree)
                      (selectionSetResponseDepth childSelectionSet))
                    (selectionSetResponseDepth rest) :=
              Nat.max_le.mpr
                ⟨Nat.le_trans hfragment (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
            _ = max (conditionTreeResponseDepth tree)
                  (selectionSetResponseDepth
                    (.inlineFragment typeCondition directives childSelectionSet ::
                      rest)) := by
              simp only [selectionSetResponseDepth, selectionResponseDepth]
              ac_rfl
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem conditionTreeResponseDepth_ofSelectionSetInScope
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : conditionTreeResponseDepth
        (ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet)
      ≤ selectionSetResponseDepth selectionSet := by
  unfold ofSelectionSetInScope
  have hdepth :=
    conditionTreeResponseDepth_insertSelections schema inheritedBooleanCondition
      (rootCondition schema parentType) []
      (Tree.root (rootCondition schema parentType)) selectionSet
  simpa [conditionTreeResponseDepth, conditionFieldGroupsResponseDepth,
    conditionBranchesResponseDepth, Tree.root] using hdepth

private theorem selectionSetResponseDepth_pruneKnownFalseSelections
    (variableValues : Execution.VariableValues) (selectionSet : List Selection)
    : selectionSetResponseDepth (pruneKnownFalseSelections variableValues selectionSet)
      ≤ selectionSetResponseDepth selectionSet := by
  cases selectionSet with
  | nil => simp [pruneKnownFalseSelections, selectionSetResponseDepth]
  | cons selection rest =>
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          rw [pruneKnownFalseSelections]
          split
          · simp only [selectionSetResponseDepth, selectionResponseDepth]
            exact Nat.le_trans
              (selectionSetResponseDepth_pruneKnownFalseSelections variableValues rest)
              (Nat.le_max_right _ _)
          · simp only [selectionSetResponseDepth, selectionResponseDepth]
            apply Nat.max_le.mpr
            exact ⟨Nat.le_max_left _ _, Nat.le_trans
              (selectionSetResponseDepth_pruneKnownFalseSelections variableValues rest)
              (Nat.le_max_right _ _)⟩
      | inlineFragment typeCondition directives childSelectionSet =>
          rw [pruneKnownFalseSelections]
          split
          · simp only [selectionSetResponseDepth, selectionResponseDepth]
            exact Nat.le_trans
              (selectionSetResponseDepth_pruneKnownFalseSelections variableValues rest)
              (Nat.le_max_right _ _)
          · simp only [selectionSetResponseDepth, selectionResponseDepth]
            apply Nat.max_le.mpr
            exact ⟨Nat.le_trans
                (selectionSetResponseDepth_pruneKnownFalseSelections variableValues
                  childSelectionSet)
                (Nat.le_max_left _ _),
              Nat.le_trans
                (selectionSetResponseDepth_pruneKnownFalseSelections variableValues rest)
                (Nat.le_max_right _ _)⟩
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : Execution.VariableValues)
    (selectionSet : List Selection)
    : conditionTreeResponseDepth
        (ofSelectionSetInScopeWithKnownFalsePruning schema parentType
          inheritedBooleanCondition variableValues selectionSet)
      ≤ selectionSetResponseDepth selectionSet := by
  unfold ofSelectionSetInScopeWithKnownFalsePruning
  exact Nat.le_trans
    (conditionTreeResponseDepth_ofSelectionSetInScope schema parentType
      inheritedBooleanCondition (pruneKnownFalseSelections variableValues selectionSet))
    (selectionSetResponseDepth_pruneKnownFalseSelections variableValues selectionSet)

end Termination
end ConditionTree
end GraphQL
