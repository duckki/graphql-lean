import GraphQL.Theories.ConditionTree.Execution
import Proofs.GraphQL.Theories.ConditionTree.Execution
import Proofs.GraphQL.Theories.ConditionTree.Extraction
import Proofs.GraphQL.Theories.ConditionTree.FieldEntries
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldCollection
import Proofs.GraphQL.Theories.SelectionConditions.Runtime

/-! Exhaustive runtime coverage of extracted condition trees. -/

namespace GraphQL
namespace ConditionTree

open Execution
open GraphQL.SelectionConditions

export GraphQL.SelectionConditions (
  booleanConditionAllows_append canonicalBooleanCondition_none_not_allows
  canonicalBooleanCondition_some_allows conditionForBranch?_runtime
  conditionOptionAllows doesFragmentTypeApplyBool_object
)

-----------------------------------------------------------------------------------------
-- Field-entry preservation by tree insertion
-----------------------------------------------------------------------------------------

theorem branchFieldEntries_append (left right : List (Branch Tree))
    : branchFieldEntries (left ++ right)
      = branchFieldEntries left ++ branchFieldEntries right := by
  induction left with
  | nil => simp [branchFieldEntries]
  | cons branch rest ih =>
      simp [branchFieldEntries, ih, List.append_assoc]

theorem mem_groupedSelections_addField
    (field : NamedField) (groups : List FieldGroup) (selection : Selection)
    : selection ∈ (addFieldToGroups field groups).flatMap FieldGroup.selections
      ↔ selection = field.toSelection
        ∨ selection ∈ groups.flatMap FieldGroup.selections := by
  induction groups with
  | nil =>
      simp [addFieldToGroups, addFieldWithResponseName, FieldGroup.selections,
        FieldGroup.fields, NamedField.toSelection]
  | cons group rest ih =>
      simp only [addFieldToGroups, addFieldWithResponseName]
      by_cases hname : field.responseName = group.responseName
      · have hbeq : (field.responseName == group.responseName) = true := by
          simp [hname]
        simp only [hbeq, if_true, List.flatMap_cons, List.mem_append]
        have hselections :
            ({ group with rest := group.rest ++ [field.field] } : FieldGroup).selections
              = group.selections ++ [field.toSelection] := by
          simp [FieldGroup.selections, FieldGroup.fields, NamedField.toSelection,
            List.map_append, hname]
        rw [hselections, List.mem_append]
        simp [or_assoc, or_left_comm, or_comm]
      · have hbeq : (field.responseName == group.responseName) = false := by
          simp [hname]
        simp only [hbeq, Bool.false_eq_true, if_false, List.flatMap_cons,
          List.mem_append]
        unfold addFieldToGroups at ih
        rw [ih]
        simp [or_left_comm]

theorem mem_annotatedFieldGroups
    (nodeCondition condition : Condition) (selection : Selection)
    (groups : List FieldGroup)
    : (condition, selection)
        ∈ groups.flatMap (fun group => group.selections.map (nodeCondition, ·))
      ↔ condition = nodeCondition ∧ selection ∈ groups.flatMap FieldGroup.selections := by
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨group, hgroup, candidate, hcandidate, hequal⟩
    simp only [Prod.mk.injEq] at hequal
    exact ⟨hequal.1.symm, ⟨group, hgroup, by simpa [hequal.2] using hcandidate⟩⟩
  · rintro ⟨rfl, group, hgroup, hselection⟩
    exact ⟨group, hgroup, selection, hselection, rfl⟩

set_option maxRecDepth 10000 in
mutual
  theorem Tree.fieldEntries_modifyAtCondition?_mem
      (target : Condition) (modify : Tree -> Tree)
      (added : List (Condition × Selection))
      (tree modifiedTree : Tree)
      (hmodify
        : ∀ node,
            node.condition = target
            -> ∀ entry,
                entry ∈ (modify node).fieldEntries
                ↔ entry ∈ node.fieldEntries ∨ entry ∈ added)
      (hresult : tree.modifyAtCondition? target modify = some modifiedTree)
      : ∀ entry,
          entry ∈ modifiedTree.fieldEntries
          ↔ entry ∈ tree.fieldEntries ∨ entry ∈ added := by
    rw [Tree.modifyAtCondition?] at hresult
    split at hresult
    · rename_i hequal
      cases hresult
      exact hmodify tree hequal
    · split at hresult
      · contradiction
      · rename_i modifiedBranches hbranches
        cases hresult
        intro entry
        simp only [Tree.fieldEntries, List.mem_append]
        rw [branchFieldEntries_modifyBranchesAtCondition?_mem target modify added
          tree.branches modifiedBranches hmodify hbranches entry]
        simp [or_assoc, or_comm]
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem branchFieldEntries_modifyBranchesAtCondition?_mem
      (target : Condition) (modify : Tree -> Tree)
      (added : List (Condition × Selection))
      (branches modifiedBranches : List (Branch Tree))
      (hmodify
        : ∀ node,
            node.condition = target
            -> ∀ entry,
                entry ∈ (modify node).fieldEntries
                ↔ entry ∈ node.fieldEntries ∨ entry ∈ added)
      (hresult
        : modifyBranchesAtCondition? target modify branches = some modifiedBranches)
      : ∀ entry,
          entry ∈ branchFieldEntries modifiedBranches
          ↔ entry ∈ branchFieldEntries branches ∨ entry ∈ added := by
    cases branches with
    | nil =>
        simp [modifyBranchesAtCondition?] at hresult
    | cons branch rest =>
        rw [modifyBranchesAtCondition?] at hresult
        split at hresult
        · rename_i modifiedBody hbody
          cases hresult
          intro entry
          simp only [branchFieldEntries, List.mem_append]
          rw [branch.body.fieldEntries_modifyAtCondition?_mem target modify added
            modifiedBody hmodify hbody entry]
          simp [or_left_comm, or_comm]
        · split at hresult
          · contradiction
          · rename_i modifiedRest hrest
            cases hresult
            intro entry
            simp only [branchFieldEntries, List.mem_append]
            rw [branchFieldEntries_modifyBranchesAtCondition?_mem target modify added
              rest modifiedRest hmodify hrest entry]
            simp [or_assoc, or_comm]
  termination_by sizeOf branches
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega
end

theorem Tree.fieldEntries_appendFieldAtCondition_mem
    (tree : Tree) (target : Condition)
    (field : NamedField)
    (hcontains : tree.containsCondition target = true)
    : ∀ entry,
        entry ∈ (tree.appendAtConditionOrSelf target [field] []).fieldEntries
        ↔ entry ∈ tree.fieldEntries ∨ entry = (target, field.toSelection) := by
  let modify : Tree -> Tree := fun node =>
    {
      node with
        fields := addFieldToGroups field node.fields
    }
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
                  (fun groups field => addFieldToGroups field groups) node.fields
              branches := node.branches ++ []
          }) = modify by
            funext node
            simp [modify]]
      simp only [hresult, Option.getD_some]
      have hentries :=
        tree.fieldEntries_modifyAtCondition?_mem target modify
          [(target, field.toSelection)] modifiedTree
          (by
            intro node hequal entry
            subst target
            simp only [modify, Tree.fieldEntries, List.mem_append,
              List.mem_singleton]
            rcases entry with ⟨condition, selection⟩
            rw [mem_annotatedFieldGroups, mem_annotatedFieldGroups]
            rw [mem_groupedSelections_addField]
            simp [and_or_left, or_left_comm, or_comm])
          hresult
      simpa using hentries

theorem Tree.fieldEntries_appendBranchesAtCondition_mem
    (tree : Tree) (target : Condition) (branches : List (Branch Tree))
    (hcontains : tree.containsCondition target = true)
    : ∀ entry,
        entry ∈ (tree.appendAtConditionOrSelf target [] branches).fieldEntries
        ↔ entry ∈ tree.fieldEntries ∨ entry ∈ branchFieldEntries branches := by
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
                  (fun groups field => addFieldToGroups field groups) node.fields
              branches := node.branches ++ branches
          }) = modify by
            funext node
            simp [modify]]
      simp only [hresult, Option.getD_some]
      apply tree.fieldEntries_modifyAtCondition?_mem target modify
        (branchFieldEntries branches) modifiedTree
      · intro node _hequal entry
        simp [modify, Tree.fieldEntries, branchFieldEntries_append, or_assoc]
      · exact hresult

theorem Tree.fieldEntries_appendFieldAtCondition?_mem
    (tree : Tree) (target : Condition)
    (field : NamedField)
    (modifiedTree : Tree)
    (hresult : tree.appendAtCondition? target [field] [] = some modifiedTree)
    : ∀ entry,
        entry ∈ modifiedTree.fieldEntries
        ↔ entry ∈ tree.fieldEntries ∨ entry = (target, field.toSelection) := by
  have hcontains :=
    tree.containsCondition_of_appendAtCondition?_eq_some target
      [field] [] modifiedTree hresult
  have htotal :=
    tree.fieldEntries_appendFieldAtCondition_mem target field hcontains
  simpa [Tree.appendAtConditionOrSelf, hresult] using htotal

theorem Tree.fieldEntries_appendBranchesAtCondition?_mem
    (tree : Tree) (target : Condition) (branches : List (Branch Tree))
    (modifiedTree : Tree)
    (hresult : tree.appendAtCondition? target [] branches = some modifiedTree)
    : ∀ entry,
        entry ∈ modifiedTree.fieldEntries
        ↔ entry ∈ tree.fieldEntries ∨ entry ∈ branchFieldEntries branches := by
  have hcontains :=
    tree.containsCondition_of_appendAtCondition?_eq_some target [] branches
      modifiedTree hresult
  have htotal :=
    tree.fieldEntries_appendBranchesAtCondition_mem target branches hcontains
  simpa [Tree.appendAtConditionOrSelf, hresult] using htotal

theorem pathEnd_cons (start condition : Condition)
    (branch : BranchCondition)
    (rest : List (BranchCondition × Condition))
    : pathEnd start ((branch, condition) :: rest) = pathEnd condition rest := by
  cases rest <;> simp [pathEnd]

theorem pathEnd_append_single (start condition : Condition)
    (path : List (BranchCondition × Condition)) (branch : BranchCondition)
    : pathEnd start (path ++ [(branch, condition)]) = condition := by
  induction path generalizing start with
  | nil => rfl
  | cons edge rest ih =>
      rcases edge with ⟨headBranch, headCondition⟩
      simpa [pathEnd] using ih headCondition

theorem pathEnd_prefixThrough (start target : Condition)
    (path : List (BranchCondition × Condition))
    (hcontains : target ∈ path.map Prod.snd)
    : pathEnd start (pathPrefixThrough target path) = target := by
  induction path generalizing start with
  | nil => simp at hcontains
  | cons edge rest ih =>
      rcases edge with ⟨branch, condition⟩
      simp only [List.map_cons, List.mem_cons] at hcontains
      simp only [pathPrefixThrough]
      by_cases hequal : condition = target
      · simp [hequal, pathEnd]
      · simp only [if_neg hequal]
        have hrest : target ∈ rest.map Prod.snd :=
          hcontains.resolve_left (fun h => hequal h.symm)
        simpa [pathEnd] using ih condition hrest

theorem pathEnd_append_right
    (left right : List (BranchCondition × Condition))
    (start rightStart : Condition) (hright : right ≠ [])
    : pathEnd start (left ++ right) = pathEnd rightStart right := by
  induction left generalizing start with
  | nil =>
      cases right with
      | nil => contradiction
      | cons edge rest =>
          rcases edge with ⟨branch, condition⟩
          simp [pathEnd]
  | cons edge rest ih =>
      rcases edge with ⟨branch, condition⟩
      simpa [pathEnd] using ih condition

theorem pathEnd_erasePathCyclesFrom
    (start : Condition)
    (kept remaining : List (BranchCondition × Condition))
    : pathEnd start (erasePathCyclesFrom kept remaining)
      = pathEnd start (kept ++ remaining) := by
  induction remaining generalizing kept start with
  | nil => simp [erasePathCyclesFrom]
  | cons edge rest ih =>
      rcases edge with ⟨branch, condition⟩
      simp only [erasePathCyclesFrom]
      let nextKept :=
        if (kept.map Prod.snd).contains condition then
          pathPrefixThrough condition kept
        else
          kept ++ [(branch, condition)]
      rw [ih start nextKept]
      cases rest with
      | nil =>
          simp only [List.append_nil]
          unfold nextKept
          by_cases hcontains : (kept.map Prod.snd).contains condition = true
          · simp only [if_pos hcontains]
            rw [pathEnd_prefixThrough start condition kept
              (List.contains_iff_mem.mp hcontains)]
            exact (pathEnd_append_single start condition kept branch).symm
          · simp only [if_neg hcontains]
      | cons next tail =>
          have hright : (next :: tail) ≠ [] := by simp
          rw [pathEnd_append_right nextKept (next :: tail) start start hright]
          symm
          simpa [List.append_assoc] using
            pathEnd_append_right
              (kept ++ [(branch, condition)]) (next :: tail) start start hright

theorem pathEnd_erasePathCycles (start : Condition)
    (path : List (BranchCondition × Condition))
    : pathEnd start (erasePathCycles path) = pathEnd start path := by
  unfold erasePathCycles
  simpa using pathEnd_erasePathCyclesFrom start [] path

theorem pathPrefixThrough_ne_nil (target : Condition)
    (path : List (BranchCondition × Condition))
    (hcontains : target ∈ path.map Prod.snd)
    : pathPrefixThrough target path ≠ [] := by
  cases path with
  | nil => simp at hcontains
  | cons edge rest =>
      simp only [pathPrefixThrough]
      split <;> simp

theorem erasePathCyclesFrom_ne_nil
    (kept remaining : List (BranchCondition × Condition))
    (hkept : kept ≠ [])
    : erasePathCyclesFrom kept remaining ≠ [] := by
  induction remaining generalizing kept with
  | nil => simpa [erasePathCyclesFrom] using hkept
  | cons edge rest ih =>
      rcases edge with ⟨branch, condition⟩
      simp only [erasePathCyclesFrom]
      by_cases hcontains : (kept.map Prod.snd).contains condition = true
      · simp only [if_pos hcontains]
        exact ih (pathPrefixThrough condition kept)
          (pathPrefixThrough_ne_nil condition kept
            (List.contains_iff_mem.mp hcontains))
      · simp only [if_neg hcontains]
        exact ih (kept ++ [(branch, condition)]) (by simp)

theorem erasePathCycles_ne_nil
    (path : List (BranchCondition × Condition)) (hpath : path ≠ [])
    : erasePathCycles path ≠ [] := by
  cases path with
  | nil => contradiction
  | cons edge rest =>
      rcases edge with ⟨branch, condition⟩
      unfold erasePathCycles
      simp only [erasePathCyclesFrom, List.map_nil, List.contains_nil,
        Bool.false_eq_true, if_false, List.nil_append]
      exact erasePathCyclesFrom_ne_nil [(branch, condition)] rest (by simp)

theorem deepestExistingPrefixFrom_end
    (tree : Tree) (target currentStart : Condition)
    (remaining : List (BranchCondition × Condition))
    (best : Condition × List (BranchCondition × Condition))
    (hremaining : pathEnd currentStart remaining = target)
    (hbest : pathEnd best.1 best.2 = target)
    : let result := deepestExistingPrefixFrom tree remaining best
      pathEnd result.1 result.2 = target := by
  induction remaining generalizing currentStart best with
  | nil =>
      simpa [deepestExistingPrefixFrom] using hbest
  | cons head rest ih =>
      rcases head with ⟨branch, condition⟩
      have htail : pathEnd condition rest = target := by
        rw [← pathEnd_cons currentStart condition branch rest]
        exact hremaining
      simp only [deepestExistingPrefixFrom]
      split
      · exact ih condition (condition, rest) htail htail
      · exact ih condition best htail hbest

theorem deepestExistingPrefix_end
    (tree : Tree) (start : Condition)
    (path : List (BranchCondition × Condition))
    : let result := deepestExistingPrefix tree start path
      pathEnd result.1 result.2 = pathEnd start path := by
  unfold deepestExistingPrefix
  exact deepestExistingPrefixFrom_end tree
    (pathEnd start path) start path (start, path) rfl rfl

theorem branchFieldEntries_branchesForPath
    (start : Condition) (path : List (BranchCondition × Condition))
    (field : NamedField)
    (hpath : path ≠ [])
    : ∀ entry,
        entry ∈ branchFieldEntries (branchesForPath path [field])
        ↔ entry = (pathEnd start path, field.toSelection) := by
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
          intro entry
          simp only [branchesForPath, branchFieldEntries, List.mem_append,
            Tree.fieldEntries, List.flatMap_nil, List.nil_append,
            List.not_mem_nil]
          simpa [pathEnd] using
            ih (start := condition) (by simp) entry

theorem Tree.appendAtCondition_condition
    (tree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    : (tree.appendAtConditionOrSelf target fields branches).condition
      = tree.condition := by
  unfold Tree.appendAtConditionOrSelf Tree.appendAtCondition?
  cases hresult
        : tree.modifyAtCondition? target
            (fun node =>
              {
                node with
                  fields :=
                    fields.foldl
                      (fun groups field => addFieldToGroups field groups) node.fields
                  branches := node.branches ++ branches
              }) with
  | none => rfl
  | some modifiedTree =>
      simp only [Option.getD_some]
      rw [Tree.modifyAtCondition?] at hresult
      split at hresult
      · cases hresult
        rfl
      · split at hresult
        · contradiction
        · cases hresult
          rfl

theorem Tree.appendAtCondition?_condition
    (tree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    (modifiedTree : Tree)
    (hresult : tree.appendAtCondition? target fields branches = some modifiedTree)
    : modifiedTree.condition = tree.condition := by
  have htotal := tree.appendAtCondition_condition target fields branches
  simpa [Tree.appendAtConditionOrSelf, hresult] using htotal

theorem Tree.insertField_condition
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (sourcePath : List BranchCondition)
    (target : Condition) (field : NamedField)
    : (tree.insertField schema inheritedBooleanCondition sourcePath target
        field).condition
      = tree.condition := by
  unfold Tree.insertField
  split
  · rename_i modifiedTree hmodifiedTree
    exact tree.appendAtCondition?_condition target [field] [] modifiedTree hmodifiedTree
  · split
    · rfl
    · rename_i sourcePath hsourcePath
      let sourcePrefix :=
        deepestExistingPrefix tree tree.condition sourcePath
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
                  | none => tree).condition
              = tree.condition
      cases retainedPrefix.2 <;> simp only
      all_goals
        split
        · rename_i modifiedTree hmodifiedTree
          exact tree.appendAtCondition?_condition _ _ _ modifiedTree hmodifiedTree
        · rfl

theorem conditionForBranches?_pathForBranches?
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start : Condition) (branches : List BranchCondition) (target : Condition)
    (hcondition
      : conditionForBranches? schema inheritedBooleanCondition start branches
        = some target)
    : ∃ path,
        pathForBranches? schema inheritedBooleanCondition start branches = some path
        ∧ pathEnd start path = target := by
  induction branches generalizing start target with
  | nil =>
      simp [conditionForBranches?] at hcondition
      subst target
      exact ⟨[], rfl, rfl⟩
  | cons branch rest ih =>
      simp only [conditionForBranches?] at hcondition
      cases hnext : conditionForBranch? schema inheritedBooleanCondition start branch with
      | none => simp [hnext] at hcondition
      | some next =>
          simp only [hnext] at hcondition
          obtain ⟨restPath, hrestPath, hend⟩ :=
            ih next target hcondition
          exact ⟨
            (branch, next) :: restPath,
            by simp [pathForBranches?, hnext, hrestPath],
            by
              cases restPath with
              | nil =>
                  simpa [pathEnd] using hend
              | cons edge tail =>
                  simpa [pathEnd] using hend
          ⟩

theorem Tree.fieldEntries_insertField_mem
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (source : List BranchCondition)
    (target : Condition) (field : NamedField)
    (sourcePath : List (BranchCondition × Condition))
    (hpath
      : pathForBranches? schema inheritedBooleanCondition tree.condition source
        = some sourcePath)
    (hpathEnd : pathEnd tree.condition sourcePath = target)
    : ∀ entry,
        entry
          ∈ (tree.insertField schema inheritedBooleanCondition source target
              field).fieldEntries
        ↔ entry ∈ tree.fieldEntries ∨ entry = (target, field.toSelection) := by
  unfold Tree.insertField
  cases hinitial : tree.appendAtCondition? target [field] [] with
  | some modifiedTree =>
      exact tree.fieldEntries_appendFieldAtCondition?_mem target field modifiedTree
        hinitial
  | none =>
      rw [hpath]
      simp only
      let sourcePrefix :=
        deepestExistingPrefix tree tree.condition sourcePath
      have hsourcePrefixEnd :
          pathEnd sourcePrefix.1 sourcePrefix.2 = target := by
        exact (deepestExistingPrefix_end tree tree.condition sourcePath).trans hpathEnd
      have hsourcePrefixContains :
          tree.containsCondition sourcePrefix.1 = true := by
        exact deepestExistingPrefix_contains tree tree.condition sourcePath
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
          pathEnd retainedPrefix.1 retainedPrefix.2 = target := by
        exact (deepestExistingPrefix_end tree sourcePrefix.1 retainedPath).trans
                hretainedEnd
      have hretainedPrefixContains :
          tree.containsCondition retainedPrefix.1 = true := by
        exact deepestExistingPrefix_contains tree sourcePrefix.1 retainedPath
          hsourcePrefixContains
      change
        ∀ entry,
          entry
              ∈ (match retainedPrefix.2 with
                | [] =>
                    match tree.appendAtCondition? retainedPrefix.1 [field] [] with
                    | some modifiedTree => modifiedTree
                    | none => tree
                | missingPath =>
                    let simplePath := erasePathCycles missingPath
                    match tree.appendAtCondition? retainedPrefix.1 []
                        (branchesForPath simplePath [field]) with
                    | some modifiedTree => modifiedTree
                    | none => tree).fieldEntries
            ↔ entry ∈ tree.fieldEntries
              ∨ entry = (target, field.toSelection)
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
              intro entry
              rw [tree.fieldEntries_appendFieldAtCondition?_mem retainedPrefix.1
                field modifiedTree happend entry]
              rw [hequal]
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
              intro entry
              rw [tree.fieldEntries_appendBranchesAtCondition?_mem retainedPrefix.1
                (branchesForPath (erasePathCycles (head :: rest)) [field])
                modifiedTree happend entry]
              rw [branchFieldEntries_branchesForPath retainedPrefix.1
                (erasePathCycles (head :: rest)) field
                (by simpa [simplePath] using hsimple) entry]
              rw [show
                pathEnd retainedPrefix.1 (erasePathCycles (head :: rest))
                  = target by
                    simpa [simplePath] using hsimpleEnd]

-----------------------------------------------------------------------------------------
-- Static source cases and extraction coverage
-----------------------------------------------------------------------------------------

-- Source fields annotated with the cumulative condition under which they occur.
def collectConditionEntries (schema : Schema) (currentParentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition)
    : List Selection -> List (Condition × Selection)
  | [] => []
  | .field responseName fieldName arguments directives selectionSet :: rest =>
      let head :=
        match branchConditionsForDirectives? directives with
        | none => []
        | some nextBranches =>
            match conditionForBranches? schema inheritedBooleanCondition
                    currentCondition nextBranches with
            | none => []
            | some nextCondition =>
                [(nextCondition, .field responseName fieldName arguments [] selectionSet)]
      head
      ++ collectConditionEntries schema currentParentType inheritedBooleanCondition
          currentCondition rest
  | .inlineFragment typeCondition directives selectionSet :: rest =>
      let child :=
        match branchConditionsForInlineFragment? typeCondition directives with
        | none => []
        | some nextBranches =>
            match conditionForBranches? schema inheritedBooleanCondition
                    currentCondition nextBranches with
            | none => []
            | some nextCondition =>
                collectConditionEntries schema
                  (parentTypeForBranches currentParentType nextBranches)
                  inheritedBooleanCondition nextCondition selectionSet
      child
      ++ collectConditionEntries schema currentParentType inheritedBooleanCondition
          currentCondition rest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    try subst selectionSet
    try subst selection
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem conditionForBranches?_append
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start middle target : Condition)
    (left right : List BranchCondition)
    (hleft
      : conditionForBranches? schema inheritedBooleanCondition start left = some middle)
    (hright
      : conditionForBranches? schema inheritedBooleanCondition middle right = some target)
    : conditionForBranches? schema inheritedBooleanCondition start (left ++ right)
      = some target := by
  induction left generalizing start middle with
  | nil =>
      simp [conditionForBranches?] at hleft
      subst middle
      exact hright
  | cons branch rest ih =>
      simp only [conditionForBranches?] at hleft ⊢
      cases hnext : conditionForBranch? schema inheritedBooleanCondition start branch with
      | none => simp [hnext] at hleft
      | some next =>
          simp only [hnext] at hleft ⊢
          simpa [conditionForBranches?, hnext] using
            ih next middle hleft hright

theorem Tree.insertSelections_condition
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition) (branches : List BranchCondition)
    (tree : Tree) (selectionSet : List Selection)
    : (insertSelections schema inheritedBooleanCondition currentCondition branches tree
        selectionSet).condition
      = tree.condition := by
  cases hselectionSet : selectionSet with
  | nil =>
      subst selectionSet
      simp [insertSelections]
  | cons selection rest =>
      subst selectionSet
      cases hselection : selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          subst selection
          rw [insertSelections]
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
          exact (treeAfterField.insertSelections_condition schema
                  inheritedBooleanCondition currentCondition branches rest).trans
                  (by
                    unfold treeAfterField
                    split
                    · rfl
                    · split
                      · rfl
                      · apply tree.insertField_condition)
      | inlineFragment typeCondition directives childSelectionSet =>
          subst selection
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
          exact (treeAfterFragment.insertSelections_condition schema
                  inheritedBooleanCondition currentCondition branches rest).trans
                  (by
                    unfold treeAfterFragment
                    split
                    · rfl
                    · split
                      · rfl
                      · exact
                          tree.insertSelections_condition schema
                            inheritedBooleanCondition ‹_› (branches ++ ‹_›)
                            childSelectionSet)
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem insertSelections_fieldEntries_mem
    (schema : Schema) (currentParentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition) (branches : List BranchCondition)
    (tree : Tree) (selectionSet : List Selection)
    (hcondition
      : conditionForBranches? schema inheritedBooleanCondition tree.condition branches
        = some currentCondition)
    : ∀ entry,
        entry
          ∈ (insertSelections schema inheritedBooleanCondition currentCondition branches
              tree selectionSet).fieldEntries
        ↔ entry ∈ tree.fieldEntries
          ∨ entry
            ∈ collectConditionEntries schema currentParentType
                inheritedBooleanCondition currentCondition selectionSet := by
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
              exact insertSelections_fieldEntries_mem schema currentParentType
                inheritedBooleanCondition currentCondition branches tree rest
                hcondition
          | some nextBranches =>
              simp only
              cases hnext
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition nextBranches with
              | none =>
                  simp only [List.nil_append]
                  exact insertSelections_fieldEntries_mem schema currentParentType
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
                  have hrest :=
                    insertSelections_fieldEntries_mem schema currentParentType
                      inheritedBooleanCondition currentCondition branches treeAfter
                      rest (by
                        rw [tree.insertField_condition schema
                          inheritedBooleanCondition (branches ++ nextBranches)
                          nextCondition field]
                        exact hcondition)
                  intro entry
                  rw [hrest]
                  rw [tree.fieldEntries_insertField_mem schema
                    inheritedBooleanCondition (branches ++ nextBranches)
                    nextCondition field sourcePath hpath hpathEnd entry]
                  simp [field, NamedField.toSelection, Field.toSelection,
                    or_assoc, or_comm]
      | inlineFragment typeCondition directives childSelectionSet =>
          subst selection
          rw [insertSelections, collectConditionEntries]
          cases hbranches
                : branchConditionsForInlineFragment? typeCondition directives with
          | none =>
              simp only [List.nil_append]
              exact insertSelections_fieldEntries_mem schema currentParentType
                inheritedBooleanCondition currentCondition branches tree rest
                hcondition
          | some nextBranches =>
              simp only
              cases hnext
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition nextBranches with
              | none =>
                  simp only [List.nil_append]
                  exact insertSelections_fieldEntries_mem schema currentParentType
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
                    insertSelections_fieldEntries_mem schema nextParentType
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
                    insertSelections_fieldEntries_mem schema currentParentType
                      inheritedBooleanCondition currentCondition branches treeAfter
                      rest hrestCondition
                  intro entry
                  rw [hrest, hchild]
                  simp [nextParentType, or_assoc, or_comm]
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    try subst selectionSet
    try subst selection
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem ofSelectionSetInScope_fieldEntries_mem
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : ∀ entry,
        entry
          ∈ (ofSelectionSetInScope schema parentType inheritedBooleanCondition
              selectionSet).fieldEntries
        ↔ entry
          ∈ collectConditionEntries schema parentType inheritedBooleanCondition
              (rootCondition schema parentType) selectionSet := by
  intro entry
  unfold ofSelectionSetInScope
  rw [insertSelections_fieldEntries_mem schema parentType
    inheritedBooleanCondition (rootCondition schema parentType) []
    (Tree.root (rootCondition schema parentType)) selectionSet
    (by simp [conditionForBranches?, Tree.root]) entry]
  simp [Tree.root, Tree.fieldEntries, branchFieldEntries]

-----------------------------------------------------------------------------------------
-- Condition-tree runtime projection
-----------------------------------------------------------------------------------------

def runtimeFieldsForConditionEntries
    {ObjectRef : Type}
    (_schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (_source : ResolverValue ObjectRef)
    (entries : List (Condition × Selection))
    : List ExecutableField :=
  entries.flatMap
    fun entry =>
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
      else
        []

theorem runtimeFieldsForConditionEntries_append
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (source : ResolverValue ObjectRef)
    (left right : List (Condition × Selection))
    : runtimeFieldsForConditionEntries schema variableValues executionParentType
        runtimeType source (left ++ right)
      = runtimeFieldsForConditionEntries schema variableValues executionParentType
          runtimeType source left
        ++ runtimeFieldsForConditionEntries schema variableValues
            executionParentType runtimeType source right := by
  simp [runtimeFieldsForConditionEntries]

theorem runtimeFieldsForConditionEntries_singleton
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (source : ResolverValue ObjectRef)
    (condition : Condition) (selection : Selection)
    : runtimeFieldsForConditionEntries schema variableValues executionParentType
        runtimeType source [(condition, selection)]
      = if condition.allows variableValues runtimeType then
          match selection with
          | .field responseName fieldName arguments _directives selectionSet =>
              [{
                parentType := executionParentType
                responseName
                fieldName
                arguments
                selectionSet
              }]
          | .inlineFragment .. => []
        else
          [] := by
  simp [runtimeFieldsForConditionEntries]

theorem runtimeFieldsForEntries_eq_projected
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (source : ResolverValue ObjectRef)
    (entries : List (Condition × NamedField))
    : runtimeFieldsForEntries variableValues executionParentType runtimeType entries
      = runtimeFieldsForConditionEntries schema variableValues executionParentType
          runtimeType source (entries.map projectStoredFieldEntry) := by
  induction entries with
  | nil => simp [runtimeFieldsForEntries, runtimeFieldsForConditionEntries]
  | cons entry rest ih =>
      rcases entry with ⟨condition, namedField⟩
      rcases namedField with ⟨responseName, field⟩
      cases field
      unfold runtimeFieldsForEntries runtimeFieldsForConditionEntries at ih
      rw [runtimeFieldsForEntries, runtimeFieldsForConditionEntries,
        List.map_cons, List.flatMap_cons, List.flatMap_cons]
      rw [ih]
      simp [projectStoredFieldEntry, NamedField.toSelection, Field.toSelection] <;> rfl

theorem collectFlatSelection_inlineFragment_object
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    : collectFlatSelection schema variableValues executionParentType
        (.object runtimeType ref)
        (.inlineFragment typeCondition directives selectionSet)
      = if selectionDirectivesAllowBool variableValues directives
            && inlineFragmentTypeAllows schema runtimeType typeCondition then
          collectFlatFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet
        else
          [] := by
  simpa [ConditionTree.collectFlatSelection_eq_fieldGroups,
    ConditionTree.collectFlatFields_eq_fieldGroups] using
    SelectionConditions.collectFlatSelection_inlineFragment_object schema
      variableValues executionParentType runtimeType ref typeCondition directives
      selectionSet

theorem collectConditionEntries_runtimeFields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType currentParentType : Name)
    (ref : ObjectRef)
    (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition)
    (selectionSet : List Selection)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    : runtimeFieldsForConditionEntries schema variableValues executionParentType
        runtimeType (.object runtimeType ref)
        (collectConditionEntries schema currentParentType
          inheritedBooleanCondition currentCondition selectionSet)
      = if currentCondition.allows variableValues runtimeType then
          collectFlatFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet
        else
          [] := by
  cases hselectionSet : selectionSet with
  | nil =>
      subst selectionSet
      simp [collectConditionEntries, runtimeFieldsForConditionEntries,
        collectFlatFields]
  | cons selection rest =>
      subst selectionSet
      cases hselection : selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          subst selection
          rw [collectConditionEntries, collectFlatFields]
          have ihRest :=
            collectConditionEntries_runtimeFields schema variableValues
              executionParentType runtimeType currentParentType ref
              inheritedBooleanCondition currentCondition rest hinherited
          cases hbranches : branchConditionsForDirectives? directives with
          | none =>
              have hliterals : literalsForDirectives directives = none := by
                cases hliterals : literalsForDirectives directives with
                | none => rfl
                | some literals =>
                    simp [branchConditionsForDirectives?, hliterals] at hbranches
              have hdirectives :=
                literalsForDirectives_none_not_allows variableValues directives
                  hliterals
              simp only [List.nil_append]
              rw [ihRest]
              cases hcurrent :
                  currentCondition.allows variableValues runtimeType
              <;>
                  simp [hdirectives, collectFlatSelection]
          | some nextBranches =>
              have hbranchesAllow :=
                branchConditionsForDirectives?_runtime schema variableValues
                  runtimeType directives nextBranches hbranches
              cases hnext
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition nextBranches with
              | none =>
                  have hnextAllows :=
                    conditionForBranches?_runtime schema variableValues runtimeType
                      inheritedBooleanCondition currentCondition nextBranches
                      hinherited
                  rw [hnext] at hnextAllows
                  simp only [conditionOptionAllows] at hnextAllows
                  rw [hbranchesAllow] at hnextAllows
                  simp only [hnext, List.nil_append]
                  rw [ihRest]
                  have hgateFalse :
                      (currentCondition.allows variableValues runtimeType
                        && selectionDirectivesAllowBool variableValues directives)
                        = false :=
                    hnextAllows.symm
                  cases hcurrent :
                      currentCondition.allows variableValues runtimeType <;>
                    cases hdirectives :
                      selectionDirectivesAllowBool variableValues directives
                  all_goals
                    simp [hcurrent, hdirectives, collectFlatSelection]
                      at hgateFalse ⊢
              | some nextCondition =>
                  have hnextAllows :=
                    conditionForBranches?_runtime schema variableValues runtimeType
                      inheritedBooleanCondition currentCondition nextBranches
                      hinherited
                  rw [hnext] at hnextAllows
                  simp only [conditionOptionAllows] at hnextAllows
                  rw [hbranchesAllow] at hnextAllows
                  simp only [hnext]
                  rw [runtimeFieldsForConditionEntries_append,
                    runtimeFieldsForConditionEntries_singleton, ihRest]
                  rw [hnextAllows]
                  cases hcurrent :
                      currentCondition.allows variableValues runtimeType <;>
                    cases hdirectives :
                      selectionDirectivesAllowBool variableValues directives
                  all_goals
                    simp [hdirectives, collectFlatSelection]
      | inlineFragment typeCondition directives childSelectionSet =>
          subst selection
          rw [collectConditionEntries, collectFlatFields]
          have ihRest :=
            collectConditionEntries_runtimeFields schema variableValues
              executionParentType runtimeType currentParentType ref
              inheritedBooleanCondition currentCondition rest hinherited
          cases hbranches
                : branchConditionsForInlineFragment? typeCondition directives with
          | none =>
              have hboolean :
                  branchConditionsForDirectives? directives = none := by
                cases hcandidate : branchConditionsForDirectives? directives with
                | none => rfl
                | some booleanBranches =>
                    simp [branchConditionsForInlineFragment?, hcandidate] at hbranches
              have hdirectives :=
                branchConditionsForDirectives?_none_not_allows variableValues
                  directives hboolean
              simp only [List.nil_append]
              rw [ihRest]
              rw [collectFlatSelection_inlineFragment_object]
              simp [hdirectives]
          | some nextBranches =>
              have hbranchesAllow :=
                branchConditionsForInlineFragment?_runtime schema variableValues
                  runtimeType typeCondition directives nextBranches hbranches
              cases hnext
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition nextBranches with
              | none =>
                  have hnextAllows :=
                    conditionForBranches?_runtime schema variableValues runtimeType
                      inheritedBooleanCondition currentCondition nextBranches
                      hinherited
                  rw [hnext] at hnextAllows
                  simp only [conditionOptionAllows] at hnextAllows
                  rw [hbranchesAllow] at hnextAllows
                  simp only [hnext, List.nil_append]
                  rw [ihRest]
                  rw [collectFlatSelection_inlineFragment_object]
                  have hgateFalse :
                      (currentCondition.allows variableValues runtimeType
                        && (selectionDirectivesAllowBool variableValues directives
                          && inlineFragmentTypeAllows schema runtimeType
                            typeCondition))
                        = false :=
                    hnextAllows.symm
                  cases hcurrent :
                      currentCondition.allows variableValues runtimeType <;>
                    cases hfragment :
                      (selectionDirectivesAllowBool variableValues directives
                        && inlineFragmentTypeAllows schema runtimeType
                          typeCondition)
                  all_goals
                    simp only [hcurrent, hfragment, Bool.false_eq_true,
                      Bool.true_eq_false, Bool.false_and, Bool.true_and,
                      if_false, if_true, List.nil_append] at hgateFalse ⊢
              | some nextCondition =>
                  have hnextAllows :=
                    conditionForBranches?_runtime schema variableValues runtimeType
                      inheritedBooleanCondition currentCondition nextBranches
                      hinherited
                  rw [hnext] at hnextAllows
                  simp only [conditionOptionAllows] at hnextAllows
                  rw [hbranchesAllow] at hnextAllows
                  have ihChild :=
                    collectConditionEntries_runtimeFields schema variableValues
                      executionParentType runtimeType
                      (parentTypeForBranches currentParentType nextBranches) ref
                      inheritedBooleanCondition nextCondition childSelectionSet
                      hinherited
                  simp only [hnext]
                  rw [runtimeFieldsForConditionEntries_append, ihChild, ihRest]
                  rw [collectFlatSelection_inlineFragment_object]
                  rw [hnextAllows]
                  cases hcurrent :
                      currentCondition.allows variableValues runtimeType <;>
                    cases hfragment :
                      (selectionDirectivesAllowBool variableValues directives
                        && inlineFragmentTypeAllows schema runtimeType
                          typeCondition)
                  all_goals
                    simp only [Bool.false_eq_true,
                      Bool.false_and, Bool.true_and, if_false, if_true,
                      List.nil_append]
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    try subst selectionSet
    try subst selection
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem runtimeFieldsForConditionEntries_mem_congr
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (source : ResolverValue ObjectRef)
    (left right : List (Condition × Selection))
    (hentries : ∀ entry, entry ∈ left ↔ entry ∈ right)
    (field : ExecutableField)
    : field
        ∈ runtimeFieldsForConditionEntries schema variableValues
            executionParentType runtimeType source left
      ↔ field
        ∈ runtimeFieldsForConditionEntries schema variableValues
            executionParentType runtimeType source right := by
  simp only [runtimeFieldsForConditionEntries, List.mem_flatMap]
  constructor
  · rintro ⟨entry, hentry, hfield⟩
    exact ⟨entry, (hentries entry).mp hentry, hfield⟩
  · rintro ⟨entry, hentry, hfield⟩
    exact ⟨entry, (hentries entry).mpr hentry, hfield⟩

theorem collectFlatFields_mem_collectFields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection) (field : ExecutableField)
    : field ∈ collectFlatFields schema variableValues parentType source selectionSet
      ↔ field
        ∈ flattenCollectedFields
            (Execution.collectFields schema variableValues parentType source
              selectionSet) := by
  rw [collectFlatFields_eq_fieldGroups,
    flattenCollectedFields_eq_fieldGroups]
  exact Execution.FieldGroups.collectFlatFields_mem_collectFields schema
    variableValues parentType source selectionSet field

theorem extraction_sound
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : ExtractionSound schema parentType inheritedBooleanCondition selectionSet := by
  intro ObjectRef variableValues executionParentType runtimeType ref
    hinherited hpossible field
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
  let tree :=
    ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet
  change field ∈ runtimeFieldsForEntries variableValues executionParentType runtimeType
      tree.storedFieldEntries ↔ _
  rw [runtimeFieldsForEntries_eq_projected schema variableValues executionParentType
    runtimeType (.object runtimeType ref) tree.storedFieldEntries]
  rw [← tree.fieldEntries_eq_map_storedFieldEntries]
  rw [runtimeFieldsForConditionEntries_mem_congr schema variableValues
    executionParentType runtimeType (.object runtimeType ref)
    tree.fieldEntries
    (collectConditionEntries schema parentType inheritedBooleanCondition
      (rootCondition schema parentType) selectionSet)
    (ofSelectionSetInScope_fieldEntries_mem schema parentType
      inheritedBooleanCondition selectionSet) field]
  rw [hsource]
  exact collectFlatFields_mem_collectFields schema variableValues
    executionParentType (.object runtimeType ref) selectionSet field

theorem mem_flattenCollectedFields_iff
    (groups : List (Name × List ExecutableField)) (field : ExecutableField)
    : field ∈ flattenCollectedFields groups
      ↔ ∃ responseName fields, (responseName, fields) ∈ groups ∧ field ∈ fields := by
  rw [flattenCollectedFields_eq_fieldGroups]
  exact Execution.FieldGroups.mem_flattenCollectedFields_iff groups field

theorem mem_group_key_iff_exists_field_of_wellFormed
    (groups : List (Name × List ExecutableField))
    (hgroups : NormalForm.executableGroupsWellFormed groups)
    (responseName : Name)
    : responseName ∈ groups.map Prod.fst
      ↔ ∃ field,
          field ∈ flattenCollectedFields groups ∧ responseName = field.responseName := by
  rw [flattenCollectedFields_eq_fieldGroups]
  exact Execution.FieldGroups.mem_group_key_iff_exists_field_of_wellFormed
    groups hgroups responseName

theorem collectFields_key_iff_exists_flat_field
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection) (responseName : Name)
    : responseName
        ∈ (Execution.collectFields schema variableValues parentType source
            selectionSet).map
            Prod.fst
      ↔ ∃ field,
          field
            ∈ flattenCollectedFields
                (Execution.collectFields schema variableValues parentType source
                  selectionSet)
          ∧ responseName = field.responseName := by
  exact mem_group_key_iff_exists_field_of_wellFormed _
    (NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
      variableValues parentType source selectionSet)
    responseName

-- Extracted tree groups and spec-collected groups have the same executable response
-- names and the same fields, modulo ordering and repeated source occurrences.
theorem extraction_groups_equivalent
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : ExtractionGroupsEquivalent schema parentType inheritedBooleanCondition
        selectionSet := by
  intro ObjectRef variableValues executionParentType runtimeType ref
    hinherited hpossible
  let tree :=
    ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet
  let source : ResolverValue ObjectRef := .object runtimeType ref
  have hfields :=
    extraction_sound schema parentType inheritedBooleanCondition selectionSet
      variableValues executionParentType runtimeType ref hinherited hpossible
  have hexact :=
    Tree.collectRuntimeFieldGroups_exact variableValues executionParentType
      runtimeType tree
  constructor
  · intro responseName
    rw [Tree.collectRuntimeFieldGroups,
      mem_groupExecutableFields_key_iff,
      collectFields_key_iff_exists_flat_field]
    constructor
    · rintro ⟨field, hfield, hname⟩
      exact ⟨field, (hfields field).mp hfield, hname⟩
    · rintro ⟨field, hfield, hname⟩
      exact ⟨field, (hfields field).mpr hfield, hname⟩
  · intro field
    exact hexact.2.mem_iff.trans (hfields field)

end ConditionTree
end GraphQL
