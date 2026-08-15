import Proofs.GraphQL.Theories.ConditionTree.Soundness
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection.StateInvariant
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection
import Proofs.GraphQL.Execution.FieldGroups
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Variables
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ReorderingSoundness
import Proofs.GraphQL.Execution.Fuel
import Proofs.GraphQL.Execution.SemanticEquivalence

/-! Occurrence-preserving condition-tree extraction and runtime-group correspondence. -/

namespace GraphQL
namespace ConditionTree
namespace RuntimeExtraction

open Execution
open Algorithms.ExecutionUngroupedUncached
open Algorithms.ExecutionUngroupedUncached.Eager
open NormalForm.GroundTypeNormalization.ReorderingSoundness
open Execution.FieldGroups

-----------------------------------------------------------------------------------------
-- Occurrence-preserving extraction
-----------------------------------------------------------------------------------------

theorem groupedSelections_addFieldWithResponseName_perm
    (responseName : Name) (field : Field) (groups : List FieldGroup)
    : ((addFieldWithResponseName responseName field groups).flatMap
        FieldGroup.selections).Perm
        (groups.flatMap FieldGroup.selections ++ [field.toSelection responseName]) := by
  induction groups with
  | nil =>
      simp [addFieldWithResponseName, FieldGroup.selections, FieldGroup.fields]
  | cons group rest ih =>
      by_cases hname : (responseName == group.responseName) = true
      · simp only [addFieldWithResponseName, hname, if_true, List.flatMap_cons]
        have hequal : responseName = group.responseName := beq_iff_eq.mp hname
        have hselections :
            ({ group with rest := group.rest ++ [field] } : FieldGroup).selections
              = group.selections ++ [field.toSelection responseName] := by
          simp [FieldGroup.selections, FieldGroup.fields, List.map_append, hequal]
        rw [hselections]
        change ((group.selections ++ [field.toSelection responseName])
                ++ rest.flatMap FieldGroup.selections).Perm
                ((group.selections ++ rest.flatMap FieldGroup.selections)
                  ++ [field.toSelection responseName])
        simp only [List.append_assoc]
        exact List.Perm.append_left group.selections
          (List.perm_append_comm.trans (by simp))
      · have hfalse : (responseName == group.responseName) = false := by
          cases hvalue : responseName == group.responseName
          · rfl
          · contradiction
        simp only [addFieldWithResponseName, hfalse, List.flatMap_cons]
        simpa [List.append_assoc] using ih.append_left group.selections

theorem annotatedGroupedSelections_addFieldWithResponseName_perm
    (condition : Condition) (responseName : Name) (field : Field)
    (groups : List FieldGroup)
    : ((addFieldWithResponseName responseName field groups).flatMap
        (fun group => group.selections.map (condition, ·))).Perm
        (groups.flatMap (fun group => group.selections.map (condition, ·))
          ++ [(condition, field.toSelection responseName)]) := by
  induction groups with
  | nil =>
      simp [addFieldWithResponseName, FieldGroup.selections, FieldGroup.fields]
  | cons group rest ih =>
      by_cases hname : (responseName == group.responseName) = true
      · simp [addFieldWithResponseName, hname]
        have hequal : responseName = group.responseName := beq_iff_eq.mp hname
        have hselections :
            ({ group with rest := group.rest ++ [field] } : FieldGroup).selections
              = group.selections ++ [field.toSelection responseName] := by
          simp [FieldGroup.selections, FieldGroup.fields, List.map_append, hequal]
        rw [hselections, List.map_append]
        simpa [List.append_assoc] using
          List.Perm.append_left (group.selections.map (condition, ·))
            (List.perm_append_comm
              (l₁ := [(condition, field.toSelection responseName)])
              (l₂ := rest.flatMap
                (fun candidate => candidate.selections.map (condition, ·))))
      · have hfalse : (responseName == group.responseName) = false := by
          cases hvalue : responseName == group.responseName
          · rfl
          · contradiction
        simp [addFieldWithResponseName, hfalse]
        simpa [List.append_assoc] using
          ih.append_left (group.selections.map (condition, ·))

theorem Tree.localFieldEntries_addField_perm (tree : Tree) (field : NamedField)
    : ((addFieldToGroups field tree.fields).flatMap
          (fun group => group.selections.map (tree.condition, ·))
        ++ branchFieldEntries tree.branches).Perm
        (tree.fieldEntries ++ [(tree.condition, field.toSelection)]) := by
  rw [Tree.fieldEntries]
  have hgroups :=
    annotatedGroupedSelections_addFieldWithResponseName_perm tree.condition
      field.responseName field.field tree.fields
  exact (hgroups.append_right (branchFieldEntries tree.branches)).trans (by
    simpa [NamedField.toSelection, List.append_assoc] using
      List.Perm.append_left
        (tree.fields.flatMap
          (fun group => group.selections.map (tree.condition, ·)))
        (List.perm_append_comm
          (l₁ := [(tree.condition, field.toSelection)])
          (l₂ := branchFieldEntries tree.branches)))

set_option maxRecDepth 10000 in
mutual
  theorem Tree.fieldEntries_modifyAtCondition?_perm
      (target : Condition) (modify : Tree -> Tree)
      (added : List (Condition × Selection))
      (tree modifiedTree : Tree)
      (hmodify
        : ∀ node,
            node.condition = target
            -> (modify node).fieldEntries.Perm (node.fieldEntries ++ added))
      (hresult : tree.modifyAtCondition? target modify = some modifiedTree)
      : modifiedTree.fieldEntries.Perm (tree.fieldEntries ++ added) := by
    rw [Tree.modifyAtCondition?] at hresult
    split at hresult
    · rename_i hequal
      cases hresult
      exact hmodify tree hequal
    · split at hresult
      · contradiction
      · rename_i modifiedBranches hbranches
        cases hresult
        rw [Tree.fieldEntries, Tree.fieldEntries]
        have hrest :=
          branchFieldEntries_modifyBranchesAtCondition?_perm target modify added
            tree.branches modifiedBranches hmodify hbranches
        simpa [List.append_assoc] using
          hrest.append_left
            (tree.fields.flatMap
              (fun group => group.selections.map (tree.condition, ·)))
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem branchFieldEntries_modifyBranchesAtCondition?_perm
      (target : Condition) (modify : Tree -> Tree)
      (added : List (Condition × Selection))
      (branches modifiedBranches : List (Branch Tree))
      (hmodify
        : ∀ node,
            node.condition = target
            -> (modify node).fieldEntries.Perm (node.fieldEntries ++ added))
      (hresult
        : modifyBranchesAtCondition? target modify branches = some modifiedBranches)
      : (branchFieldEntries modifiedBranches).Perm
          (branchFieldEntries branches ++ added) := by
    cases branches with
    | nil =>
        simp [modifyBranchesAtCondition?] at hresult
    | cons branch rest =>
        rw [modifyBranchesAtCondition?] at hresult
        split at hresult
        · rename_i modifiedBody hbody
          cases hresult
          rw [branchFieldEntries, branchFieldEntries]
          have hhead :=
            Tree.fieldEntries_modifyAtCondition?_perm target modify added
              branch.body modifiedBody hmodify hbody
          exact (hhead.append_right (branchFieldEntries rest)).trans (by
            simpa [List.append_assoc] using
              List.Perm.append_left branch.body.fieldEntries
                (List.perm_append_comm
                  (l₁ := added) (l₂ := branchFieldEntries rest)))
        · split at hresult
          · contradiction
          · rename_i modifiedRest hrest
            cases hresult
            rw [branchFieldEntries, branchFieldEntries]
            simpa [List.append_assoc] using
              (branchFieldEntries_modifyBranchesAtCondition?_perm target modify
                added rest modifiedRest hmodify hrest).append_left
                  branch.body.fieldEntries
  termination_by sizeOf branches
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega
end

theorem Tree.fieldEntries_appendFieldAtCondition_perm
    (tree : Tree) (target : Condition)
    (field : NamedField)
    (hcontains : tree.containsCondition target = true)
    : (tree.appendAtConditionOrSelf target [field] []).fieldEntries.Perm
        (tree.fieldEntries ++ [(target, field.toSelection)]) := by
  let modify : Tree -> Tree := fun node =>
    { node with fields := addFieldToGroups field node.fields }
  have hsome : (tree.modifyAtCondition? target modify).isSome = true := by
    apply tree.modifyAtCondition?_isSome_iff_mem_nodeConditions target modify |>.2
    exact tree.containsCondition_iff_mem_nodeConditions target |>.1 hcontains
  cases hresult : tree.modifyAtCondition? target modify with
  | none => simp [hresult] at hsome
  | some modifiedTree =>
      unfold Tree.appendAtConditionOrSelf Tree.appendAtCondition?
      rw [show
        (fun node =>
          {
            node with
              fields :=
                [field].foldl
                  (fun groups candidate => addFieldToGroups candidate groups)
                  node.fields
              branches := node.branches ++ []
          }) = modify by
            funext node
            simp [modify]]
      simp only [hresult, Option.getD_some]
      apply Tree.fieldEntries_modifyAtCondition?_perm target modify
        [(target, field.toSelection)] tree modifiedTree
      · intro node hequal
        subst target
        simpa [modify, Tree.fieldEntries] using
          Tree.localFieldEntries_addField_perm node field
      · exact hresult

theorem Tree.fieldEntries_appendBranchesAtCondition_perm
    (tree : Tree) (target : Condition) (branches : List (Branch Tree))
    (hcontains : tree.containsCondition target = true)
    : (tree.appendAtConditionOrSelf target [] branches).fieldEntries.Perm
        (tree.fieldEntries ++ branchFieldEntries branches) := by
  let modify : Tree -> Tree := fun node =>
    { node with branches := node.branches ++ branches }
  have hsome : (tree.modifyAtCondition? target modify).isSome = true := by
    apply tree.modifyAtCondition?_isSome_iff_mem_nodeConditions target modify |>.2
    exact tree.containsCondition_iff_mem_nodeConditions target |>.1 hcontains
  cases hresult : tree.modifyAtCondition? target modify with
  | none => simp [hresult] at hsome
  | some modifiedTree =>
      unfold Tree.appendAtConditionOrSelf Tree.appendAtCondition?
      rw [show
        (fun node =>
          {
            node with
              fields :=
                [].foldl
                  (fun groups candidate => addFieldToGroups candidate groups)
                  node.fields
              branches := node.branches ++ branches
          }) = modify by
            funext node
            rfl]
      simp only [hresult, Option.getD_some]
      apply Tree.fieldEntries_modifyAtCondition?_perm target modify
        (branchFieldEntries branches) tree modifiedTree
      · intro node _hequal
        simp [modify, Tree.fieldEntries, branchFieldEntries_append,
          List.append_assoc]
      · exact hresult

theorem Tree.fieldEntries_appendFieldAtCondition?_perm
    (tree : Tree) (target : Condition)
    (field : NamedField)
    (modifiedTree : Tree)
    (hresult : tree.appendAtCondition? target [field] [] = some modifiedTree)
    : modifiedTree.fieldEntries.Perm
        (tree.fieldEntries ++ [(target, field.toSelection)]) := by
  have hcontains :=
    tree.containsCondition_of_appendAtCondition?_eq_some target
      [field] [] modifiedTree hresult
  have htotal :=
    fieldEntries_appendFieldAtCondition_perm tree target field hcontains
  simpa [Tree.appendAtConditionOrSelf, hresult] using htotal

theorem Tree.fieldEntries_appendBranchesAtCondition?_perm
    (tree : Tree) (target : Condition) (branches : List (Branch Tree))
    (modifiedTree : Tree)
    (hresult : tree.appendAtCondition? target [] branches = some modifiedTree)
    : modifiedTree.fieldEntries.Perm
        (tree.fieldEntries ++ branchFieldEntries branches) := by
  have hcontains :=
    tree.containsCondition_of_appendAtCondition?_eq_some target [] branches
      modifiedTree hresult
  have htotal :=
    fieldEntries_appendBranchesAtCondition_perm tree target branches hcontains
  simpa [Tree.appendAtConditionOrSelf, hresult] using htotal

theorem branchFieldEntries_branchesForPath_eq_singleton
    (start : Condition) (path : List (BranchCondition × Condition))
    (field : NamedField)
    (hpath : path ≠ [])
    : branchFieldEntries (branchesForPath path [field])
      = [(pathEnd start path, field.toSelection)] := by
  induction path generalizing start with
  | nil => contradiction
  | cons edge rest ih =>
      rcases edge with ⟨branch, condition⟩
      cases rest with
      | nil =>
          simp [branchesForPath, branchFieldEntries, Tree.fieldEntries,
            collectFieldGroups, addFieldToGroups, addFieldWithResponseName,
            FieldGroup.selections, FieldGroup.fields, NamedField.toSelection, pathEnd]
      | cons next tail =>
          simp only [branchesForPath, branchFieldEntries, Tree.fieldEntries,
            List.flatMap_nil, List.nil_append]
          simpa [pathEnd] using ih (start := condition) (by simp)

theorem Tree.fieldEntries_insertField_perm
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (source : List BranchCondition)
    (target : Condition) (field : NamedField)
    (sourcePath : List (BranchCondition × Condition))
    (hpath
      : pathForBranches? schema inheritedBooleanCondition tree.condition source
        = some sourcePath)
    (hpathEnd : pathEnd tree.condition sourcePath = target)
    : (tree.insertField schema inheritedBooleanCondition source target
        field).fieldEntries.Perm
        (tree.fieldEntries ++ [(target, field.toSelection)]) := by
  unfold Tree.insertField
  cases hinitial : tree.appendAtCondition? target [field] [] with
  | some modifiedTree =>
      exact fieldEntries_appendFieldAtCondition?_perm tree target field modifiedTree
        hinitial
  | none =>
      rw [hpath]
      simp only
      let sourcePrefix :=
        deepestExistingPrefix tree tree.condition sourcePath
      have hsourcePrefixEnd :
          pathEnd sourcePrefix.1 sourcePrefix.2 = target :=
        (deepestExistingPrefix_end tree tree.condition sourcePath).trans hpathEnd
      have hsourcePrefixContains :
          tree.containsCondition sourcePrefix.1 = true :=
        deepestExistingPrefix_contains tree tree.condition sourcePath
          tree.containsCondition_self
      let shrunk :=
        shrinkBranches schema inheritedBooleanCondition sourcePrefix.1 target
          (sourcePrefix.2.map Prod.fst)
      let retainedPath :=
        match pathForBranches? schema inheritedBooleanCondition sourcePrefix.1
            shrunk with
        | some path =>
            if pathEnd sourcePrefix.1 path = target then path else sourcePrefix.2
        | none => sourcePrefix.2
      have hretainedEnd :
          pathEnd sourcePrefix.1 retainedPath = target := by
        unfold retainedPath
        cases hshrunk
              : pathForBranches? schema inheritedBooleanCondition sourcePrefix.1
                  shrunk with
        | none => exact hsourcePrefixEnd
        | some path =>
            by_cases hend : pathEnd sourcePrefix.1 path = target
            · simp [hend]
            · simpa [hend] using hsourcePrefixEnd
      let retainedPrefix :=
        deepestExistingPrefix tree sourcePrefix.1 retainedPath
      have hretainedPrefixEnd :
          pathEnd retainedPrefix.1 retainedPrefix.2 = target :=
        (deepestExistingPrefix_end tree sourcePrefix.1 retainedPath).trans
          hretainedEnd
      have hretainedPrefixContains :
          tree.containsCondition retainedPrefix.1 = true :=
        deepestExistingPrefix_contains tree sourcePrefix.1 retainedPath
          hsourcePrefixContains
      change (match retainedPrefix.2 with
              | [] =>
                  match tree.appendAtCondition? retainedPrefix.1 [field] [] with
                  | some modifiedTree => modifiedTree
                  | none => tree
              | missingPath =>
                  let simplePath := erasePathCycles missingPath
                  match tree.appendAtCondition? retainedPrefix.1 []
                          (branchesForPath simplePath [field]) with
                  | some modifiedTree => modifiedTree
                  | none => tree).fieldEntries.Perm
              (tree.fieldEntries ++ [(target, field.toSelection)])
      cases hmissing : retainedPrefix.2 with
      | nil =>
          have hequal : retainedPrefix.1 = target := by
            simpa [hmissing, pathEnd] using hretainedPrefixEnd
          simp only
          cases happend : tree.appendAtCondition? retainedPrefix.1 [field] [] with
          | none =>
              have hsome :
                  (tree.appendAtCondition? retainedPrefix.1
                    [field] []).isSome = true := by
                rw [tree.appendAtCondition?_isSome]
                exact hretainedPrefixContains
              simp [happend] at hsome
          | some modifiedTree =>
              simpa [hequal] using
                fieldEntries_appendFieldAtCondition?_perm tree retainedPrefix.1
                  field modifiedTree happend
      | cons head rest =>
          let simplePath := erasePathCycles (head :: rest)
          have hsimple : simplePath ≠ [] :=
            erasePathCycles_ne_nil (head :: rest) (by simp)
          have hsimpleEnd :
              pathEnd retainedPrefix.1 simplePath = target := by
            rw [pathEnd_erasePathCycles]
            simpa [hmissing] using hretainedPrefixEnd
          simp only
          cases happend
                : tree.appendAtCondition? retainedPrefix.1 []
                    (branchesForPath (erasePathCycles (head :: rest)) [field]) with
          | none =>
              have hsome :
                  (tree.appendAtCondition? retainedPrefix.1 []
                    (branchesForPath (erasePathCycles (head :: rest))
                      [field])).isSome = true := by
                rw [tree.appendAtCondition?_isSome]
                exact hretainedPrefixContains
              simp [happend] at hsome
          | some modifiedTree =>
              have happendEntries :=
                fieldEntries_appendBranchesAtCondition?_perm tree retainedPrefix.1
                  (branchesForPath (erasePathCycles (head :: rest)) [field])
                  modifiedTree happend
              rw [branchFieldEntries_branchesForPath_eq_singleton retainedPrefix.1
                (erasePathCycles (head :: rest)) field
                (by simpa [simplePath] using hsimple)] at happendEntries
              simpa [hsimpleEnd, simplePath] using happendEntries

theorem insertSelections_fieldEntries_perm
    (schema : Schema) (currentParentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition) (branches : List BranchCondition)
    (tree : Tree) (selectionSet : List Selection)
    (hcondition
      : conditionForBranches? schema inheritedBooleanCondition tree.condition branches
        = some currentCondition)
    : (insertSelections schema inheritedBooleanCondition currentCondition branches tree
        selectionSet).fieldEntries.Perm
        (tree.fieldEntries
          ++ collectConditionEntries schema currentParentType inheritedBooleanCondition
              currentCondition selectionSet) := by
  cases hselectionSet : selectionSet with
  | nil =>
      subst selectionSet
      simp [insertSelections, collectConditionEntries]
  | cons selection rest =>
      subst selectionSet
      cases hselection : selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          subst selection
          rw [insertSelections, collectConditionEntries]
          cases hbranches : branchConditionsForDirectives? directives with
          | none =>
              simp only [List.nil_append]
              exact insertSelections_fieldEntries_perm schema currentParentType
                inheritedBooleanCondition currentCondition branches tree rest
                hcondition
          | some nextBranches =>
              simp only
              cases hnext
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition nextBranches with
              | none =>
                  simp only [List.nil_append]
                  exact insertSelections_fieldEntries_perm schema currentParentType
                    inheritedBooleanCondition currentCondition branches tree rest
                    hcondition
              | some nextCondition =>
                  simp only
                  let field : NamedField :=
                    {
                      responseName
                      field :=
                        { fieldName, arguments, selectionSet := childSelectionSet }
                    }
                  have hcombined :
                      conditionForBranches? schema inheritedBooleanCondition
                          tree.condition (branches ++ nextBranches)
                        = some nextCondition :=
                    conditionForBranches?_append schema inheritedBooleanCondition
                      tree.condition currentCondition nextCondition branches
                      nextBranches hcondition hnext
                  obtain ⟨sourcePath, hpath, hpathEnd⟩ :=
                    conditionForBranches?_pathForBranches? schema
                      inheritedBooleanCondition tree.condition
                      (branches ++ nextBranches) nextCondition hcombined
                  let treeAfter :=
                    tree.insertField schema inheritedBooleanCondition
                      (branches ++ nextBranches) nextCondition field
                  have hinsert :=
                    Tree.fieldEntries_insertField_perm schema
                      inheritedBooleanCondition tree (branches ++ nextBranches)
                      nextCondition field sourcePath hpath hpathEnd
                  have hrest :=
                    insertSelections_fieldEntries_perm schema currentParentType
                      inheritedBooleanCondition currentCondition branches treeAfter
                      rest (by
                        rw [tree.insertField_condition schema
                          inheritedBooleanCondition (branches ++ nextBranches)
                          nextCondition field]
                        exact hcondition)
                  exact hrest.trans (by
                    simpa [treeAfter, field, NamedField.toSelection, Field.toSelection,
                      List.append_assoc]
                      using hinsert.append_right
                        (collectConditionEntries schema currentParentType
                          inheritedBooleanCondition currentCondition rest))
      | inlineFragment typeCondition directives childSelectionSet =>
          subst selection
          rw [insertSelections, collectConditionEntries]
          cases hbranches
                : branchConditionsForInlineFragment? typeCondition directives with
          | none =>
              simp only [List.nil_append]
              exact insertSelections_fieldEntries_perm schema currentParentType
                inheritedBooleanCondition currentCondition branches tree rest
                hcondition
          | some nextBranches =>
              simp only
              cases hnext
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition nextBranches with
              | none =>
                  simp only [List.nil_append]
                  exact insertSelections_fieldEntries_perm schema currentParentType
                    inheritedBooleanCondition currentCondition branches tree rest
                    hcondition
              | some nextCondition =>
                  simp only
                  let nextParentType :=
                    parentTypeForBranches currentParentType nextBranches
                  let treeAfter :=
                    insertSelections schema inheritedBooleanCondition nextCondition
                      (branches ++ nextBranches) tree childSelectionSet
                  have hchildCondition :
                      conditionForBranches? schema inheritedBooleanCondition
                          tree.condition (branches ++ nextBranches)
                        = some nextCondition :=
                    conditionForBranches?_append schema inheritedBooleanCondition
                      tree.condition currentCondition nextCondition branches
                      nextBranches hcondition hnext
                  have hchild :=
                    insertSelections_fieldEntries_perm schema nextParentType
                      inheritedBooleanCondition nextCondition
                      (branches ++ nextBranches) tree childSelectionSet
                      hchildCondition
                  have hrestCondition :
                      conditionForBranches? schema inheritedBooleanCondition
                          treeAfter.condition branches
                        = some currentCondition := by
                    rw [tree.insertSelections_condition schema
                      inheritedBooleanCondition nextCondition
                      (branches ++ nextBranches) childSelectionSet]
                    exact hcondition
                  have hrest :=
                    insertSelections_fieldEntries_perm schema currentParentType
                      inheritedBooleanCondition currentCondition branches treeAfter
                      rest hrestCondition
                  exact hrest.trans (by
                    simpa [treeAfter, List.append_assoc] using
                      hchild.append_right
                        (collectConditionEntries schema currentParentType
                          inheritedBooleanCondition currentCondition rest))
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    try subst selectionSet
    try subst selection
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem ofSelectionSetInScope_fieldEntries_perm
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : (ofSelectionSetInScope schema parentType inheritedBooleanCondition
        selectionSet).fieldEntries.Perm
        (collectConditionEntries schema parentType inheritedBooleanCondition
          (rootCondition schema parentType) selectionSet) := by
  unfold ofSelectionSetInScope
  simpa [Tree.root, Tree.fieldEntries, branchFieldEntries] using
    insertSelections_fieldEntries_perm schema parentType
      inheritedBooleanCondition (rootCondition schema parentType) []
      (Tree.root (rootCondition schema parentType)) selectionSet
      (by simp [conditionForBranches?, Tree.root])

theorem runtimeFieldsForConditionEntries_perm
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (source : ResolverValue ObjectRef)
    {left right : List (Condition × Selection)}
    (hentries : left.Perm right)
    : (runtimeFieldsForConditionEntries schema variableValues executionParentType
        runtimeType source left).Perm
        (runtimeFieldsForConditionEntries schema variableValues executionParentType
          runtimeType source right) := by
  exact List.Perm.flatMap (β := ExecutableField) hentries fun entry =>
    if entry.1.allows variableValues runtimeType then
      match entry.2 with
      | .field responseName fieldName arguments _directives selectionSet =>
          [{
            parentType := executionParentType
            responseName
            fieldName
            arguments
            selectionSet
          }]
      | .inlineFragment .. => []
    else []

theorem collectFlatFields_perm_flatten_collectFields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : (collectFlatFields schema variableValues parentType source selectionSet).Perm
        (flattenCollectedFields
          (collectFields schema variableValues parentType source selectionSet)) := by
  simpa [ConditionTree.collectFlatFields_eq_fieldGroups,
    ConditionTree.flattenCollectedFields_eq_fieldGroups] using
    Execution.FieldGroups.collectFlatFields_perm_flatten_collectFields schema
      variableValues parentType source selectionSet

theorem extraction_runtimeFields_perm
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    {ObjectRef : Type} (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : ((ofSelectionSetInScope schema parentType inheritedBooleanCondition
          selectionSet).collectRuntimeFields
        variableValues executionParentType runtimeType).Perm
        (flattenCollectedFields
          (collectFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet)) := by
  have hroot :
      (rootCondition schema parentType).allows variableValues runtimeType = true := by
    change ((schema.getPossibleTypes parentType).contains runtimeType
              && booleanConditionAllows variableValues [])
            = true
    rw [hpossible]
    rfl
  have hsource :=
    collectConditionEntries_runtimeFields schema variableValues executionParentType
      runtimeType parentType ref inheritedBooleanCondition
      (rootCondition schema parentType) selectionSet hinherited
  rw [hroot] at hsource
  simp only [if_true] at hsource
  rw [Tree.collectRuntimeFields,
    runtimeFieldsForEntries_eq_projected schema variableValues executionParentType
      runtimeType (.object runtimeType ref),
    ← Tree.fieldEntries_eq_map_storedFieldEntries]
  exact (runtimeFieldsForConditionEntries_perm schema variableValues executionParentType
          runtimeType (.object runtimeType ref)
          (ofSelectionSetInScope_fieldEntries_perm schema parentType
            inheritedBooleanCondition selectionSet)).trans
          ((List.Perm.of_eq hsource).trans
            (collectFlatFields_perm_flatten_collectFields schema variableValues
              executionParentType (.object runtimeType ref) selectionSet))

theorem extraction_runtimeGroups_occurrence_equivalent
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    {ObjectRef : Type} (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : (flattenCollectedFields
        ((ofSelectionSetInScope schema parentType inheritedBooleanCondition
            selectionSet).collectRuntimeFieldGroups
          variableValues executionParentType runtimeType)).Perm
        (flattenCollectedFields
          (collectFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet)) := by
  exact (Tree.collectRuntimeFieldGroups_exact variableValues executionParentType
          runtimeType
          (ofSelectionSetInScope schema parentType inheritedBooleanCondition
            selectionSet)).2.trans
          (extraction_runtimeFields_perm schema parentType inheritedBooleanCondition
            selectionSet variableValues executionParentType runtimeType ref hinherited
            hpossible)

theorem extracted_runtimeGroups_permutationEquivalent
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    {ObjectRef : Type} (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : RuntimeGroupsPermutationEquivalent
        ((ofSelectionSetInScope schema parentType inheritedBooleanCondition
            selectionSet).collectRuntimeFieldGroups
          variableValues executionParentType runtimeType)
        (collectFields schema variableValues executionParentType
          (.object runtimeType ref) selectionSet) := by
  constructor
  · exact Tree.collectRuntimeFieldGroups_wellFormed variableValues
      executionParentType runtimeType _
  · exact NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
      variableValues executionParentType (.object runtimeType ref) selectionSet
  · exact (Tree.collectRuntimeFieldGroups_exact variableValues
      executionParentType runtimeType _).1
  · exact (Execution.FieldGroups.executableGroupNamesNodup_iff_map_fst_nodup _).mp
      (NormalForm.collectFields_namesNodup schema variableValues
        executionParentType (.object runtimeType ref) selectionSet)
  · simpa [ConditionTree.flattenCollectedFields_eq_fieldGroups,
      Execution.FieldGroups.flattenCollectedFields_eq_flatMap_snd] using
      extraction_runtimeGroups_occurrence_equivalent schema parentType
        inheritedBooleanCondition selectionSet variableValues executionParentType
        runtimeType ref hinherited hpossible

theorem selectionSetResultEquivalent_combine_singleField_append
    {responseName : Name}
    {leftHead rightHead : Result ResponseValue}
    {leftTail rightTail : Result (List (Name × ResponseValue))}
    (hhead : ResponseValueResultEquivalent leftHead rightHead)
    (htail : SelectionSetResultEquivalent leftTail rightTail)
    : SelectionSetResultEquivalent
        (Result.combine List.append (singleFieldResult responseName leftHead) leftTail)
        (Result.combine List.append
          (singleFieldResult responseName rightHead) rightTail) := by
  cases leftHead
  <;> cases rightHead
  <;>
    cases leftTail
  <;> cases rightTail
  <;>
      simp [ResponseValueResultEquivalent, SelectionSetResultEquivalent,
        singleFieldResult, Result.combine] at hhead htail ⊢
  all_goals try omega
  rename_i leftHeadResult rightHeadResult leftTailResult rightTailResult
  rcases leftHeadResult with ⟨leftValue, leftHeadErrors⟩
  rcases rightHeadResult with ⟨rightValue, rightHeadErrors⟩
  rcases leftTailResult with ⟨leftFields, leftTailErrors⟩
  rcases rightTailResult with ⟨rightFields, rightTailErrors⟩
  exact ⟨responseValue_semanticEquivalent_object_cons hhead.1 htail.1, by omega⟩

theorem collectFlatFields_perm_of_selectionSet_perm
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    {left right : List Selection} (hselectionSet : left.Perm right)
    : (collectFlatFields schema variableValues parentType source left).Perm
        (collectFlatFields schema variableValues parentType source right) := by
  simpa [ConditionTree.collectFlatFields_eq_fieldGroups] using
    Execution.FieldGroups.collectFlatFields_perm_of_selectionSet_perm schema
      variableValues parentType source hselectionSet

theorem extracted_runtimeGroups_permutationEquivalent_toPermutedSelectionSet
    (schema : Schema) (extractionParentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    {leftSelectionSet rightSelectionSet : List Selection}
    (hselectionSet : leftSelectionSet.Perm rightSelectionSet)
    {ObjectRef : Type} (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hpossible
      : (schema.getPossibleTypes extractionParentType).contains runtimeType = true)
    : RuntimeGroupsPermutationEquivalent
        ((ofSelectionSetInScope schema extractionParentType
            inheritedBooleanCondition leftSelectionSet).collectRuntimeFieldGroups
          variableValues executionParentType runtimeType)
        (collectFields schema variableValues executionParentType
          (.object runtimeType ref) rightSelectionSet) := by
  constructor
  · exact Tree.collectRuntimeFieldGroups_wellFormed variableValues
      executionParentType runtimeType _
  · exact NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
      variableValues executionParentType (.object runtimeType ref) rightSelectionSet
  · exact (Tree.collectRuntimeFieldGroups_exact variableValues
      executionParentType runtimeType _).1
  · exact (Execution.FieldGroups.executableGroupNamesNodup_iff_map_fst_nodup _).mp
      (NormalForm.collectFields_namesNodup schema variableValues
        executionParentType (.object runtimeType ref) rightSelectionSet)
  · have hperm :=
      (extraction_runtimeGroups_occurrence_equivalent schema
        extractionParentType inheritedBooleanCondition leftSelectionSet
        variableValues executionParentType runtimeType ref hinherited hpossible).trans
        ((collectFlatFields_perm_flatten_collectFields schema variableValues
          executionParentType (.object runtimeType ref) leftSelectionSet).symm.trans
          ((collectFlatFields_perm_of_selectionSet_perm schema variableValues
            executionParentType (.object runtimeType ref) hselectionSet).trans
            (collectFlatFields_perm_flatten_collectFields schema variableValues
              executionParentType (.object runtimeType ref) rightSelectionSet)))
    simpa [ConditionTree.flattenCollectedFields_eq_fieldGroups,
      Execution.FieldGroups.flattenCollectedFields_eq_flatMap_snd] using hperm

theorem flattenCollectedFields_eq_collectedExecutableFields
    (groups : List (Name × List ExecutableField))
    : flattenCollectedFields groups = collectedExecutableFields groups := by
  rw [ConditionTree.flattenCollectedFields_eq_fieldGroups]
  exact Execution.FieldGroups.flattenCollectedFields_eq_collectedExecutableFields groups

end RuntimeExtraction
end ConditionTree
end GraphQL
