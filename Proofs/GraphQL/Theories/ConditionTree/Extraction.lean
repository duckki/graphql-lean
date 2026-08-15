import GraphQL.SchemaWellFormedness
import Proofs.GraphQL.Theories.ConditionTree.ExtractionCoherence

/-!
The condition-tree extractor produces globally unique, feasible condition nodes with
locally unique collected response names and condition-free retained fields.
-/

namespace GraphQL
namespace ConditionTree

-- Proof-only totalization for statements that describe both the present- and
-- absent-target cases. Production extraction matches on `appendAtCondition?` directly.
def Tree.appendAtConditionOrSelf (tree : Tree) (condition : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    : Tree :=
  (tree.appendAtCondition? condition fields branches).getD tree

-----------------------------------------------------------------------------------------
-- Flat condition membership
-----------------------------------------------------------------------------------------

theorem branchConditions_append (left right : List (Branch Tree))
    : branchNodeConditions (left ++ right)
      = branchNodeConditions left ++ branchNodeConditions right := by
  induction left with
  | nil => simp [branchNodeConditions]
  | cons branch rest ih =>
      simp [branchNodeConditions, ih, List.append_assoc]

mutual
  theorem Tree.containsCondition_iff_mem_nodeConditions (tree : Tree) (target : Condition)
      : tree.containsCondition target = true ↔ target ∈ tree.nodeConditions := by
    rw [Tree.containsCondition, Tree.nodeConditions]
    simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    rw [branchesContainCondition_iff_mem_branchNodeConditions]
    simp only [eq_comm]
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem branchesContainCondition_iff_mem_branchNodeConditions
      (branches : List (Branch Tree)) (target : Condition)
      : branchesContainCondition branches target = true
        ↔ target ∈ branchNodeConditions branches := by
    cases branches with
    | nil => simp [branchesContainCondition, branchNodeConditions]
    | cons branch rest =>
        rw [branchesContainCondition, branchNodeConditions]
        simp only [Bool.or_eq_true, List.mem_append]
        rw [branch.body.containsCondition_iff_mem_nodeConditions,
          branchesContainCondition_iff_mem_branchNodeConditions]
  termination_by sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

-- Cycle-free paths
-----------------------------------------------------------------------------------------

theorem pathPrefixThrough_map_subset (target : Condition)
    (path : List (BranchCondition × Condition))
    : ∀ condition,
        condition ∈ (pathPrefixThrough target path).map Prod.snd
        -> condition ∈ path.map Prod.snd := by
  induction path with
  | nil => simp [pathPrefixThrough]
  | cons edge rest ih =>
      intro condition hcondition
      simp only [pathPrefixThrough] at hcondition
      split at hcondition
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inl (by simpa using hcondition)
      · simp only [List.map_cons, List.mem_cons] at hcondition ⊢
        exact hcondition.elim Or.inl (fun hrest => Or.inr (ih condition hrest))

theorem pathPrefixThrough_map_nodup (target : Condition)
    (path : List (BranchCondition × Condition))
    (hnodup : (path.map Prod.snd).Nodup)
    : ((pathPrefixThrough target path).map Prod.snd).Nodup := by
  induction path with
  | nil => simp [pathPrefixThrough]
  | cons edge rest ih =>
      simp only [pathPrefixThrough]
      split
      · simp
      · simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
        exact ⟨
          fun hmember =>
            hnodup.1 (pathPrefixThrough_map_subset target rest edge.2 hmember),
          ih hnodup.2
        ⟩

theorem erasePathCyclesFrom_map_subset
    (kept remaining : List (BranchCondition × Condition))
    : ∀ condition,
        condition ∈ (erasePathCyclesFrom kept remaining).map Prod.snd
        -> condition ∈ (kept ++ remaining).map Prod.snd := by
  induction remaining generalizing kept with
  | nil =>
      simp [erasePathCyclesFrom]
  | cons edge rest ih =>
      rcases edge with ⟨branch, nextCondition⟩
      intro condition hcondition
      simp only [erasePathCyclesFrom] at hcondition
      by_cases hcontains : (kept.map Prod.snd).contains nextCondition = true
      · simp only [if_pos hcontains] at hcondition
        have hnext :=
          ih (pathPrefixThrough nextCondition kept) condition hcondition
        simp only [List.map_append, List.map_cons, List.mem_append,
          List.mem_cons] at hnext ⊢
        exact hnext.elim
          (fun hprefix =>
            Or.inl (pathPrefixThrough_map_subset nextCondition kept condition hprefix))
          (fun hrest => Or.inr (Or.inr hrest))
      · simp only [if_neg hcontains] at hcondition
        have hnext :=
          ih (kept ++ [(branch, nextCondition)]) condition hcondition
        simpa [List.map_append, List.append_assoc] using hnext

theorem erasePathCycles_map_subset (path : List (BranchCondition × Condition))
    : ∀ condition,
        condition ∈ (erasePathCycles path).map Prod.snd
        -> condition ∈ path.map Prod.snd := by
  unfold erasePathCycles
  simpa using erasePathCyclesFrom_map_subset [] path

theorem erasePathCyclesFrom_map_nodup
    (kept remaining : List (BranchCondition × Condition))
    (hnodup : (kept.map Prod.snd).Nodup)
    : ((erasePathCyclesFrom kept remaining).map Prod.snd).Nodup := by
  induction remaining generalizing kept with
  | nil =>
      simpa [erasePathCyclesFrom] using hnodup
  | cons edge rest ih =>
      rcases edge with ⟨branch, condition⟩
      simp only [erasePathCyclesFrom]
      by_cases hcontains : (kept.map Prod.snd).contains condition = true
      · simp only [if_pos hcontains]
        exact ih (pathPrefixThrough condition kept)
          (pathPrefixThrough_map_nodup condition kept hnodup)
      · simp only [if_neg hcontains]
        apply ih (kept ++ [(branch, condition)])
        simp only [List.map_append, List.map_cons]
        apply List.nodup_append.mpr
        refine ⟨hnodup, by simp, ?_⟩
        intro left hleft right hright hequal
        subst right
        have hleftEq : left = condition := by simpa using hright
        subst left
        exact hcontains (List.contains_iff_mem.mpr hleft)

theorem erasePathCycles_map_nodup (path : List (BranchCondition × Condition))
    : ((erasePathCycles path).map Prod.snd).Nodup := by
  unfold erasePathCycles
  exact erasePathCyclesFrom_map_nodup [] path (by simp)

theorem branchConditions_branchesForPath
    (path : List (BranchCondition × Condition)) (fields : List NamedField)
    : branchNodeConditions (branchesForPath path fields) = path.map Prod.snd := by
  induction path with
  | nil => simp [branchesForPath, branchNodeConditions]
  | cons edge rest ih =>
      rcases edge with ⟨branchCondition, condition⟩
      cases rest with
      | nil => simp [branchesForPath, branchNodeConditions, Tree.nodeConditions]
      | cons next tail =>
          simp [branchesForPath, branchNodeConditions, Tree.nodeConditions, ih]

-----------------------------------------------------------------------------------------
-- Updating one indexed node
-----------------------------------------------------------------------------------------

mutual
  theorem Tree.modifyAtCondition?_isSome_iff_mem_nodeConditions
      (target : Condition) (modify : Tree -> Tree) (tree : Tree)
      : (tree.modifyAtCondition? target modify).isSome = true
        ↔ target ∈ tree.nodeConditions := by
    rw [Tree.modifyAtCondition?]
    by_cases hequal : tree.condition = target
    · simp [hequal, Tree.nodeConditions]
    · simp only [if_neg hequal]
      have hbranches :=
        modifyBranchesAtCondition?_isSome_iff_mem_nodeConditions target modify tree.branches
      cases hresult : modifyBranchesAtCondition? target modify tree.branches <;>
        simp_all [Tree.nodeConditions, eq_comm]
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem modifyBranchesAtCondition?_isSome_iff_mem_nodeConditions
      (target : Condition) (modify : Tree -> Tree)
      (branches : List (Branch Tree))
      : (modifyBranchesAtCondition? target modify branches).isSome = true
        ↔ target ∈ branchNodeConditions branches := by
    cases branches with
    | nil => simp [modifyBranchesAtCondition?, branchNodeConditions]
    | cons branch rest =>
        rw [modifyBranchesAtCondition?, branchNodeConditions]
        have hbody :=
          branch.body.modifyAtCondition?_isSome_iff_mem_nodeConditions target modify
        have hrest :=
          modifyBranchesAtCondition?_isSome_iff_mem_nodeConditions target modify rest
        cases hbodyResult : branch.body.modifyAtCondition? target modify with
        | none =>
            cases hrestResult : modifyBranchesAtCondition? target modify rest <;>
              simp_all
        | some modifiedBody => simp_all
  termination_by sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

mutual
  theorem Tree.modifyAtCondition?_isSome_eq
      (target : Condition) (left right : Tree -> Tree) (tree : Tree)
      : (tree.modifyAtCondition? target left).isSome
        = (tree.modifyAtCondition? target right).isSome := by
    rw [Tree.modifyAtCondition?, Tree.modifyAtCondition?]
    split
    · rfl
    · have ih :=
        modifyBranchesAtCondition?_isSome_eq target left right tree.branches
      cases hleft : modifyBranchesAtCondition? target left tree.branches <;>
        cases hright : modifyBranchesAtCondition? target right tree.branches <;>
        simp_all
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem modifyBranchesAtCondition?_isSome_eq
      (target : Condition) (left right : Tree -> Tree)
      (branches : List (Branch Tree))
      : (modifyBranchesAtCondition? target left branches).isSome
        = (modifyBranchesAtCondition? target right branches).isSome := by
    cases branches with
    | nil => simp [modifyBranchesAtCondition?]
    | cons branch rest =>
        rw [modifyBranchesAtCondition?, modifyBranchesAtCondition?]
        have hhead :=
          branch.body.modifyAtCondition?_isSome_eq target left right
        have hrest :=
          modifyBranchesAtCondition?_isSome_eq target left right rest
        cases hleft : branch.body.modifyAtCondition? target left <;>
          cases hright : branch.body.modifyAtCondition? target right <;>
          simp_all
        case none.none =>
          cases hleftRest : modifyBranchesAtCondition? target left rest <;>
            cases hrightRest : modifyBranchesAtCondition? target right rest <;>
            simp_all
  termination_by sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      simp_all
      omega
end

theorem Tree.containsCondition_of_appendAtCondition?_eq_some
    (tree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    (modifiedTree : Tree)
    (hresult : tree.appendAtCondition? target fields branches = some modifiedTree)
    : tree.containsCondition target = true := by
  unfold Tree.appendAtCondition? at hresult
  apply tree.containsCondition_iff_mem_nodeConditions target |>.2
  apply tree.modifyAtCondition?_isSome_iff_mem_nodeConditions target _ |>.1
  have hisSome := congrArg Option.isSome hresult
  exact hisSome

theorem Tree.appendAtCondition?_isSome
    (tree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    : (tree.appendAtCondition? target fields branches).isSome
      = tree.containsCondition target := by
  unfold Tree.appendAtCondition?
  apply Bool.eq_iff_iff.mpr
  exact (tree.modifyAtCondition?_isSome_iff_mem_nodeConditions target _).trans
          (tree.containsCondition_iff_mem_nodeConditions target).symm

mutual
  theorem Tree.nodeConditions_modifyAtCondition?
      (target : Condition) (modify : Tree -> Tree) (added : List Condition)
      (tree modifiedTree : Tree)
      (hmodify
        : ∀ node,
            node.condition = target
            -> (modify node).nodeConditions.Perm (node.nodeConditions ++ added))
      (hresult : tree.modifyAtCondition? target modify = some modifiedTree)
      : modifiedTree.nodeConditions.Perm (tree.nodeConditions ++ added) := by
    rw [Tree.modifyAtCondition?] at hresult
    split at hresult
    · rename_i hequal
      cases hresult
      exact hmodify tree hequal
    · split at hresult
      · contradiction
      · rename_i modifiedBranches hbranches
        cases hresult
        simp only [Tree.nodeConditions]
        exact List.Perm.cons tree.condition
          (branchConditions_modifyBranchesAtCondition? target modify added
            tree.branches modifiedBranches hmodify hbranches)

  theorem branchConditions_modifyBranchesAtCondition?
      (target : Condition) (modify : Tree -> Tree) (added : List Condition)
      (branches modifiedBranches : List (Branch Tree))
      (hmodify
        : ∀ node,
            node.condition = target
            -> (modify node).nodeConditions.Perm (node.nodeConditions ++ added))
      (hresult
        : modifyBranchesAtCondition? target modify branches = some modifiedBranches)
      : (branchNodeConditions modifiedBranches).Perm
          (branchNodeConditions branches ++ added) := by
    cases branches with
    | nil =>
        simp [modifyBranchesAtCondition?] at hresult
    | cons branch rest =>
        rw [modifyBranchesAtCondition?] at hresult
        split at hresult
        · rename_i modifiedBody hbody
          cases hresult
          simp only [branchNodeConditions]
          have hhead :=
            branch.body.nodeConditions_modifyAtCondition? target modify added
              modifiedBody hmodify hbody
          exact (List.Perm.append_right (branchNodeConditions rest) hhead).trans
            (by
              simpa [List.append_assoc] using
                List.Perm.append_left branch.body.nodeConditions
                  (List.perm_append_comm :
                    (added ++ branchNodeConditions rest).Perm
                      (branchNodeConditions rest ++ added)))
        · split at hresult
          · contradiction
          · rename_i modifiedRest hrest
            cases hresult
            simp only [branchNodeConditions]
            simpa [List.append_assoc] using
              List.Perm.append_left branch.body.nodeConditions
                (branchConditions_modifyBranchesAtCondition? target modify added
                  rest modifiedRest hmodify hrest)
end

theorem Tree.nodeConditions_appendAtCondition
    (tree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    (hcontains : tree.containsCondition target = true)
    : (tree.appendAtConditionOrSelf target fields branches).nodeConditions.Perm
        (tree.nodeConditions ++ branchNodeConditions branches) := by
  let modify : Tree -> Tree := fun node =>
    {
      node with
        fields :=
          fields.foldl (fun groups field => addFieldToGroups field groups) node.fields
        branches := node.branches ++ branches
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
                fields.foldl
                  (fun groups field => addFieldToGroups field groups) node.fields
              branches := node.branches ++ branches
          }) = modify by rfl]
      simp only [hresult, Option.getD_some]
      apply tree.nodeConditions_modifyAtCondition? target modify
        (branchNodeConditions branches) modifiedTree
      · intro node _hequal
        simp only [modify, Tree.nodeConditions]
        rw [branchConditions_append]
        simp
      · exact hresult

theorem Tree.nodeConditions_appendAtCondition?_eq_some
    (tree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    (modifiedTree : Tree)
    (hresult : tree.appendAtCondition? target fields branches = some modifiedTree)
    : modifiedTree.nodeConditions.Perm
        (tree.nodeConditions ++ branchNodeConditions branches) := by
  let modify : Tree -> Tree := fun node =>
    {
      node with
        fields :=
          fields.foldl (fun groups field => addFieldToGroups field groups) node.fields
        branches := node.branches ++ branches
    }
  change tree.modifyAtCondition? target modify = some modifiedTree at hresult
  apply tree.nodeConditions_modifyAtCondition? target modify
    (branchNodeConditions branches) modifiedTree
  · intro node _hequal
    simp only [modify, Tree.nodeConditions]
    rw [branchConditions_append]
    simp
  · exact hresult

-----------------------------------------------------------------------------------------
-- Deepest existing prefixes
-----------------------------------------------------------------------------------------

theorem Tree.containsCondition_self (tree : Tree)
    : tree.containsCondition tree.condition = true := by
  apply tree.containsCondition_iff_mem_nodeConditions tree.condition |>.2
  simp [Tree.nodeConditions]

theorem deepestExistingPrefixFrom_contains
    (tree : Tree)
    (remaining : List (BranchCondition × Condition))
    (best : Condition × List (BranchCondition × Condition))
    (hbest : tree.containsCondition best.1 = true)
    : let result := deepestExistingPrefixFrom tree remaining best
      tree.containsCondition result.1 = true := by
  induction remaining generalizing best with
  | nil =>
      simpa [deepestExistingPrefixFrom] using hbest
  | cons head rest ih =>
      rcases head with ⟨branch, condition⟩
      simp only [deepestExistingPrefixFrom]
      split
      · rename_i hcondition
        exact ih (condition, rest) hcondition
      · exact ih best hbest

theorem deepestExistingPrefix_contains
    (tree : Tree) (start : Condition)
    (path : List (BranchCondition × Condition))
    (hstart : tree.containsCondition start = true)
    : let result := deepestExistingPrefix tree start path
      tree.containsCondition result.1 = true := by
  unfold deepestExistingPrefix
  exact deepestExistingPrefixFrom_contains tree path (start, path) hstart

theorem deepestExistingPrefixFrom_remaining_absent
    (tree : Tree) (currentStart : Condition)
    (remaining : List (BranchCondition × Condition))
    (best : Condition × List (BranchCondition × Condition))
    (hbest
      : ∀ condition,
          condition ∈ best.2.map Prod.snd
          -> tree.containsCondition condition = true
          -> condition ∈ remaining.map Prod.snd)
    : let result := deepestExistingPrefixFrom tree remaining best
      ∀ condition,
        condition ∈ result.2.map Prod.snd
        -> tree.containsCondition condition = false := by
  induction remaining generalizing currentStart best with
  | nil =>
      simp only [deepestExistingPrefixFrom]
      intro condition hcondition
      have hnotTrue : ¬tree.containsCondition condition = true := by
        intro htrue
        simpa using hbest condition hcondition htrue
      cases hvalue : tree.containsCondition condition with
      | false => rfl
      | true => exact False.elim (hnotTrue hvalue)
  | cons edge rest ih =>
      rcases edge with ⟨branch, condition⟩
      simp only [deepestExistingPrefixFrom]
      by_cases hcondition : tree.containsCondition condition = true
      · simp only [if_pos hcondition]
        apply ih condition (condition, rest)
        intro candidate hcandidate _hcontains
        exact hcandidate
      · simp only [if_neg hcondition]
        apply ih condition best
        intro candidate hcandidate hcontains
        have hremaining := hbest candidate hcandidate hcontains
        simp only [List.map_cons, List.mem_cons] at hremaining ⊢
        exact hremaining.elim
          (fun hequal =>
            False.elim (hcondition (by simpa [hequal] using hcontains)))
          id

theorem deepestExistingPrefix_remaining_absent
    (tree : Tree) (start : Condition)
    (path : List (BranchCondition × Condition))
    : let result := deepestExistingPrefix tree start path
      ∀ condition,
        condition ∈ result.2.map Prod.snd
        -> tree.containsCondition condition = false := by
  unfold deepestExistingPrefix
  apply deepestExistingPrefixFrom_remaining_absent tree start path (start, path)
  intro condition hcondition _hcontains
  exact hcondition

-----------------------------------------------------------------------------------------
-- Condition uniqueness under insertion
-----------------------------------------------------------------------------------------

theorem Tree.nodeConditions_insertField_nodup
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (sourcePath : List BranchCondition)
    (target : Condition) (field : NamedField)
    (hnodup : tree.nodeConditions.Nodup)
    : (tree.insertField schema inheritedBooleanCondition sourcePath target
        field).nodeConditions.Nodup := by
  unfold Tree.insertField
  split
  · rename_i modifiedTree hmodifiedTree
    have hperm :=
      tree.nodeConditions_appendAtCondition?_eq_some target [field] [] modifiedTree
        hmodifiedTree
    exact hperm.nodup_iff.mpr (by simpa [branchNodeConditions] using hnodup)
  · cases hsourcePath
          : pathForBranches? schema inheritedBooleanCondition tree.condition
              sourcePath with
    | none => exact hnodup
    | some sourcePath =>
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
        have hsourcePrefixContains :
            tree.containsCondition sourcePrefix.1 = true :=
          deepestExistingPrefix_contains tree tree.condition sourcePath
            tree.containsCondition_self
        have hremainingAbsent :
            ∀ condition,
              condition ∈ retainedPrefix.2.map Prod.snd
              -> tree.containsCondition condition = false :=
          deepestExistingPrefix_remaining_absent tree sourcePrefix.1 retainedPath
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
                    | none => tree).nodeConditions.Nodup
        cases hmissing : retainedPrefix.2 with
        | nil =>
            simp only
            split
            · rename_i modifiedTree hmodifiedTree
              have hperm :=
                tree.nodeConditions_appendAtCondition?_eq_some retainedPrefix.1 [field]
                  [] modifiedTree hmodifiedTree
              exact hperm.nodup_iff.mpr (by
                simpa [branchNodeConditions] using hnodup)
            · exact hnodup
        | cons head rest =>
            simp only
            let simplePath := erasePathCycles (head :: rest)
            let addedBranches := branchesForPath simplePath [field]
            split
            · rename_i modifiedTree hmodifiedTree
              have haddNodup : (branchNodeConditions addedBranches).Nodup := by
                rw [branchConditions_branchesForPath]
                exact erasePathCycles_map_nodup (head :: rest)
              have hdisjoint :
                  ∀ left,
                    left ∈ tree.nodeConditions
                    -> ∀ right,
                      right ∈ branchNodeConditions addedBranches
                      -> left = right
                      -> False := by
                intro left hleft right hright hequal
                subst right
                have hsimple : left ∈ simplePath.map Prod.snd := by
                  unfold addedBranches at hright
                  rw [branchConditions_branchesForPath] at hright
                  exact hright
                have horiginal : left ∈ (head :: rest).map Prod.snd :=
                  erasePathCycles_map_subset (head :: rest) left
                    (by simpa [simplePath] using hsimple)
                have habsent : tree.containsCondition left = false := by
                  apply hremainingAbsent left
                  rw [hmissing]
                  exact horiginal
                have hpresent : tree.containsCondition left = true :=
                  tree.containsCondition_iff_mem_nodeConditions left |>.2 hleft
                rw [hpresent] at habsent
                contradiction
              have happend :=
                tree.nodeConditions_appendAtCondition?_eq_some retainedPrefix.1 []
                  addedBranches modifiedTree hmodifiedTree
              apply happend.nodup_iff.mpr
              exact List.nodup_append.mpr ⟨hnodup, haddNodup, hdisjoint⟩
            · exact hnodup

-----------------------------------------------------------------------------------------
-- Collected response-name uniqueness
-----------------------------------------------------------------------------------------

theorem mem_responseNames_addFieldWithResponseName
    (responseName : Name) (field : Field) (groups : List FieldGroup)
    : ∀ name,
        name
          ∈ (addFieldWithResponseName responseName field groups).map
              FieldGroup.responseName
        -> name ∈ groups.map FieldGroup.responseName ∨ name = responseName := by
  induction groups with
  | nil =>
      intro name hname
      simp [addFieldWithResponseName] at hname
      exact Or.inr hname
  | cons group rest ih =>
      intro name hname
      by_cases hequal : responseName = group.responseName
      · subst responseName
        simp [addFieldWithResponseName] at hname ⊢
        exact Or.inl hname
      · have hbeq : (responseName == group.responseName) = false := by
          simp [hequal]
        simp only [addFieldWithResponseName, hbeq, Bool.false_eq_true,
          if_false, List.map_cons, List.mem_cons] at hname ⊢
        exact hname.elim
          (fun hhead => Or.inl (Or.inl hhead))
          (fun htail =>
            (ih name htail).elim
              (fun hold => Or.inl (Or.inr hold))
              Or.inr)

theorem addFieldWithResponseName_namesNodup
    (responseName : Name) (field : Field) (groups : List FieldGroup)
    (hnodup : (groups.map FieldGroup.responseName).Nodup)
    : ((addFieldWithResponseName responseName field groups).map
        FieldGroup.responseName).Nodup := by
  induction groups with
  | nil => simp [addFieldWithResponseName]
  | cons group rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      by_cases hequal : responseName = group.responseName
      · subst responseName
        simpa [addFieldWithResponseName] using hnodup
      · have hbeq : (responseName == group.responseName) = false := by
          simp [hequal]
        simp only [addFieldWithResponseName, hbeq, Bool.false_eq_true,
          if_false, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih hnodup.2⟩
        intro hmember
        rcases
            mem_responseNames_addFieldWithResponseName responseName field rest
              group.responseName hmember with
          hold | hnew
        · exact hnodup.1 hold
        · exact hequal hnew.symm

theorem addFieldToGroups_namesNodup
    (field : NamedField) (groups : List FieldGroup)
    (hnodup : (groups.map FieldGroup.responseName).Nodup)
    : ((addFieldToGroups field groups).map FieldGroup.responseName).Nodup := by
  exact addFieldWithResponseName_namesNodup field.responseName field.field groups hnodup

theorem foldl_addFieldToGroups_namesNodup
    (fields : List NamedField) (groups : List FieldGroup)
    (hnodup : (groups.map FieldGroup.responseName).Nodup)
    : ((fields.foldl (fun result field => addFieldToGroups field result) groups).map
        FieldGroup.responseName).Nodup := by
  induction fields generalizing groups with
  | nil => simpa using hnodup
  | cons field rest ih =>
      simp only [List.foldl_cons]
      exact ih (groups := addFieldToGroups field groups)
        (addFieldToGroups_namesNodup field groups hnodup)

theorem collectFieldGroups_namesNodup (fields : List NamedField)
    : ((collectFieldGroups fields).map FieldGroup.responseName).Nodup := by
  unfold collectFieldGroups
  exact foldl_addFieldToGroups_namesNodup fields [] (by simp)

theorem branchFieldGroupsUnique_append
    (left right : List (Branch Tree))
    (hleft : branchFieldGroupsUnique left)
    (hright : branchFieldGroupsUnique right)
    : branchFieldGroupsUnique (left ++ right) := by
  induction left with
  | nil => exact hright
  | cons branch rest ih =>
      rw [branchFieldGroupsUnique.eq_def] at hleft ⊢
      exact ⟨hleft.1, ih hleft.2⟩

theorem branchesForPath_fieldGroupsUnique
    (path : List (BranchCondition × Condition)) (fields : List NamedField)
    : branchFieldGroupsUnique (branchesForPath path fields) := by
  induction path with
  | nil => simp [branchesForPath, branchFieldGroupsUnique]
  | cons edge rest ih =>
      rcases edge with ⟨branchCondition, condition⟩
      cases rest with
      | nil =>
          simp [branchesForPath, branchFieldGroupsUnique, Tree.fieldGroupsUnique,
            collectFieldGroups_namesNodup]
      | cons next tail =>
          simp only [branchesForPath, branchFieldGroupsUnique,
            Tree.fieldGroupsUnique, List.map_nil, List.nodup_nil, true_and]
          exact ⟨ih, trivial⟩

mutual
  theorem Tree.modifyAtCondition?_fieldGroupsUnique
      (target : Condition) (modify : Tree -> Tree)
      (tree modifiedTree : Tree)
      (hmodify : ∀ node, node.fieldGroupsUnique -> (modify node).fieldGroupsUnique)
      (htree : tree.fieldGroupsUnique)
      (hresult : tree.modifyAtCondition? target modify = some modifiedTree)
      : modifiedTree.fieldGroupsUnique := by
    rw [Tree.modifyAtCondition?] at hresult
    split at hresult
    · cases hresult
      exact hmodify tree htree
    · split at hresult
      · contradiction
      · rename_i modifiedBranches hbranches
        cases hresult
        rw [Tree.fieldGroupsUnique] at htree ⊢
        exact ⟨htree.1,
          modifyBranchesAtCondition?_fieldGroupsUnique target modify
            tree.branches modifiedBranches hmodify htree.2 hbranches⟩

  theorem modifyBranchesAtCondition?_fieldGroupsUnique
      (target : Condition) (modify : Tree -> Tree)
      (branches modifiedBranches : List (Branch Tree))
      (hmodify : ∀ node, node.fieldGroupsUnique -> (modify node).fieldGroupsUnique)
      (hbranches : branchFieldGroupsUnique branches)
      (hresult
        : modifyBranchesAtCondition? target modify branches = some modifiedBranches)
      : branchFieldGroupsUnique modifiedBranches := by
    cases branches with
    | nil => simp [modifyBranchesAtCondition?] at hresult
    | cons branch rest =>
        rw [branchFieldGroupsUnique.eq_def] at hbranches
        rw [modifyBranchesAtCondition?] at hresult
        split at hresult
        · rename_i modifiedBody hbody
          cases hresult
          rw [branchFieldGroupsUnique.eq_def]
          exact ⟨branch.body.modifyAtCondition?_fieldGroupsUnique target modify
              modifiedBody hmodify hbranches.1 hbody,
            hbranches.2⟩
        · split at hresult
          · contradiction
          · rename_i modifiedRest hrest
            cases hresult
            rw [branchFieldGroupsUnique.eq_def]
            exact ⟨hbranches.1,
              modifyBranchesAtCondition?_fieldGroupsUnique target modify
                rest modifiedRest hmodify hbranches.2 hrest⟩
end

theorem Tree.appendAtCondition_fieldGroupsUnique
    (tree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    (htree : tree.fieldGroupsUnique)
    (hbranches : branchFieldGroupsUnique branches)
    : (tree.appendAtConditionOrSelf target fields branches).fieldGroupsUnique := by
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
  | none => simpa [hresult] using htree
  | some modifiedTree =>
      simp only [Option.getD_some]
      apply tree.modifyAtCondition?_fieldGroupsUnique target _ modifiedTree _ htree
        hresult
      intro node hnode
      rw [Tree.fieldGroupsUnique] at hnode ⊢
      exact ⟨
        foldl_addFieldToGroups_namesNodup fields node.fields hnode.1,
        branchFieldGroupsUnique_append node.branches branches hnode.2 hbranches
      ⟩

theorem Tree.appendAtCondition?_fieldGroupsUnique
    (tree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    (modifiedTree : Tree)
    (hresult : tree.appendAtCondition? target fields branches = some modifiedTree)
    (htree : tree.fieldGroupsUnique)
    (hbranches : branchFieldGroupsUnique branches)
    : modifiedTree.fieldGroupsUnique := by
  have htotal :=
    tree.appendAtCondition_fieldGroupsUnique target fields branches htree hbranches
  simpa [Tree.appendAtConditionOrSelf, hresult] using htotal

theorem Tree.insertField_fieldGroupsUnique
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (sourcePath : List BranchCondition)
    (target : Condition) (field : NamedField)
    (htree : tree.fieldGroupsUnique)
    : (tree.insertField schema inheritedBooleanCondition sourcePath target field)
      |>.fieldGroupsUnique := by
  unfold Tree.insertField
  split
  · rename_i modifiedTree hmodifiedTree
    exact tree.appendAtCondition?_fieldGroupsUnique _ [field] [] modifiedTree
      hmodifiedTree htree (by simp [branchFieldGroupsUnique])
  · split
    · exact htree
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
                  | none => tree)
              |>.fieldGroupsUnique
      cases hmissing : retainedPrefix.2 with
      | nil =>
          simp only
          split
          · rename_i modifiedTree hmodifiedTree
            exact tree.appendAtCondition?_fieldGroupsUnique _ [field] [] modifiedTree
              hmodifiedTree htree (by simp [branchFieldGroupsUnique])
          · exact htree
      | cons head rest =>
          simp only
          split
          · rename_i modifiedTree hmodifiedTree
            exact tree.appendAtCondition?_fieldGroupsUnique _ []
              (branchesForPath (erasePathCycles (head :: rest)) [field]) modifiedTree
              hmodifiedTree htree (branchesForPath_fieldGroupsUnique _ _)
          · exact htree

-----------------------------------------------------------------------------------------
-- Relative feasibility and inherited-literal disjointness
-----------------------------------------------------------------------------------------

end ConditionTree
namespace SelectionConditions

def Condition.GoodUnder (condition : Condition)
    (inheritedBooleanCondition : List BooleanLiteral)
    : Prop :=
  condition.FeasibleUnder inheritedBooleanCondition
  ∧ ConditionTree.booleanConditionsDisjoint inheritedBooleanCondition
      condition.booleanCondition

end SelectionConditions
namespace ConditionTree

theorem booleanConditionsDisjoint_filterInherited
    (inherited candidate : List BooleanLiteral)
    : booleanConditionsDisjoint inherited
        (candidate.filter fun literal => !inherited.contains literal) := by
  intro literal hinherited hfiltered
  have hnotContains :=
    (List.mem_filter.mp hfiltered).2
  have hnotMem : literal ∉ inherited := by
    simpa using hnotContains
  exact hnotMem hinherited

theorem conditionForBranch?_goodUnder
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start child : Condition) (branch : BranchCondition)
    (hstart : start.GoodUnder inheritedBooleanCondition)
    (hresult
      : conditionForBranch? schema inheritedBooleanCondition start branch = some child)
    : child.GoodUnder inheritedBooleanCondition := by
  cases branch with
  | typeCondition typeName =>
      unfold conditionForBranch? at hresult
      let possibleTypes :=
        intersectPossibleTypes start.possibleTypes (schema.getPossibleTypes typeName)
      by_cases hempty : possibleTypes.isEmpty = true
      · simp [possibleTypes, hempty] at hresult
      · simp only [possibleTypes, hempty, Bool.false_eq_true, if_false] at hresult
        cases hresult
        refine ⟨⟨?_, hstart.1.2⟩, hstart.2⟩
        simpa [List.isEmpty_iff] using hempty
  | booleanLiteral literal =>
      simp only [conditionForBranch?] at hresult
      cases hcandidate
            : canonicalBooleanCondition (start.booleanCondition ++ [literal]) with
      | none =>
          simp [hcandidate] at hresult
      | some candidate =>
          let booleanCondition :=
            candidate.filter
              fun item => !inheritedBooleanCondition.contains item
          rw [hcandidate] at hresult
          change
            (canonicalBooleanCondition
                (inheritedBooleanCondition ++ booleanCondition)).bind
                (fun _globalBooleanCondition =>
                  some { start with booleanCondition })
              = some child at hresult
          cases hglobal
                : canonicalBooleanCondition
                    (inheritedBooleanCondition ++ booleanCondition) with
          | none =>
              rw [hglobal] at hresult
              contradiction
          | some globalCondition =>
              rw [hglobal] at hresult
              simp only [Option.bind_some] at hresult
              cases hresult
              exact ⟨
                ⟨hstart.1.1, by simp [hglobal]⟩,
                booleanConditionsDisjoint_filterInherited
                  inheritedBooleanCondition candidate
              ⟩

theorem pathForBranches?_goodUnder
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start : Condition) (source : List BranchCondition)
    (path : List (BranchCondition × Condition))
    (hstart : start.GoodUnder inheritedBooleanCondition)
    (hpath : pathForBranches? schema inheritedBooleanCondition start source = some path)
    : ∀ condition,
        condition ∈ path.map Prod.snd
        -> condition.GoodUnder inheritedBooleanCondition := by
  induction source generalizing start path with
  | nil =>
      simp [pathForBranches?] at hpath
      subst path
      simp
  | cons branch rest ih =>
      cases hnext : conditionForBranch? schema inheritedBooleanCondition start branch with
      | none =>
          simp [pathForBranches?, hnext] at hpath
      | some next =>
          cases hrest : pathForBranches? schema inheritedBooleanCondition next rest with
          | none =>
              simp [pathForBranches?, hnext, hrest] at hpath
          | some restPath =>
              simp [pathForBranches?, hnext, hrest] at hpath
              subst path
              intro condition hcondition
              simp only [List.map_cons, List.mem_cons] at hcondition
              exact hcondition.elim
                (fun hequal =>
                  hequal ▸ conditionForBranch?_goodUnder schema
                    inheritedBooleanCondition start next branch hstart hnext)
                (fun htail =>
                  ih next restPath
                    (conditionForBranch?_goodUnder schema
                      inheritedBooleanCondition start next branch hstart hnext)
                    hrest condition htail)

theorem deepestExistingPrefixFrom_remaining_subset
    (tree : Tree)
    (remaining whole : List (BranchCondition × Condition))
    (best : Condition × List (BranchCondition × Condition))
    (hremaining
      : ∀ condition, condition ∈ remaining.map Prod.snd -> condition ∈ whole.map Prod.snd)
    (hbest
      : ∀ condition, condition ∈ best.2.map Prod.snd -> condition ∈ whole.map Prod.snd)
    : let result := deepestExistingPrefixFrom tree remaining best
      ∀ condition,
        condition ∈ result.2.map Prod.snd -> condition ∈ whole.map Prod.snd := by
  induction remaining generalizing best with
  | nil =>
      simpa [deepestExistingPrefixFrom] using hbest
  | cons edge rest ih =>
      rcases edge with ⟨branch, condition⟩
      simp only [deepestExistingPrefixFrom]
      split
      · apply ih (condition, rest)
        · intro candidate hcandidate
          exact hremaining candidate (by simp [hcandidate])
        · intro candidate hcandidate
          exact hremaining candidate (by simp [hcandidate])
      · apply ih best
        · intro candidate hcandidate
          exact hremaining candidate (by simp [hcandidate])
        · exact hbest

theorem deepestExistingPrefix_remaining_subset
    (tree : Tree) (start : Condition)
    (path : List (BranchCondition × Condition))
    : let result := deepestExistingPrefix tree start path
      ∀ condition,
        condition ∈ result.2.map Prod.snd -> condition ∈ path.map Prod.snd := by
  unfold deepestExistingPrefix
  apply deepestExistingPrefixFrom_remaining_subset tree path path (start, path)
  · intro condition hcondition
    exact hcondition
  · intro condition hcondition
    exact hcondition

theorem nodeConditions_goodUnder_of_perm
    (inheritedBooleanCondition : List BooleanLiteral)
    (left right : List Condition) (hperm : left.Perm right)
    (hright
      : ∀ condition, condition ∈ right -> condition.GoodUnder inheritedBooleanCondition)
    : ∀ condition, condition ∈ left -> condition.GoodUnder inheritedBooleanCondition := by
  intro condition hcondition
  exact hright condition (hperm.mem_iff.mp hcondition)

theorem Tree.nodeConditions_insertField_goodUnder
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (sourceBranches : List BranchCondition)
    (target : Condition) (field : NamedField)
    (htree
      : ∀ condition,
          condition ∈ tree.nodeConditions
          -> condition.GoodUnder inheritedBooleanCondition)
    : ∀ condition,
        condition
          ∈ Tree.nodeConditions
              (tree.insertField schema inheritedBooleanCondition sourceBranches target
                field)
        -> condition.GoodUnder inheritedBooleanCondition := by
  unfold Tree.insertField
  split
  · rename_i modifiedTree hmodifiedTree
    apply nodeConditions_goodUnder_of_perm inheritedBooleanCondition _ _
      (tree.nodeConditions_appendAtCondition?_eq_some target [field] [] modifiedTree
        hmodifiedTree)
    simpa [branchNodeConditions] using htree
  ·
    cases hsourcePath :
        pathForBranches? schema inheritedBooleanCondition tree.condition sourceBranches with
    | none => exact htree
    | some sourcePath =>
        have hrootGood : tree.condition.GoodUnder inheritedBooleanCondition :=
          htree tree.condition (by simp [Tree.nodeConditions])
        have hsourceGood :=
          pathForBranches?_goodUnder schema inheritedBooleanCondition
            tree.condition sourceBranches sourcePath hrootGood hsourcePath
        let sourcePrefix := deepestExistingPrefix tree tree.condition sourcePath
        have hsourcePrefixGood :
            sourcePrefix.1.GoodUnder inheritedBooleanCondition := by
          apply htree sourcePrefix.1
          exact tree.containsCondition_iff_mem_nodeConditions sourcePrefix.1 |>.1
            (deepestExistingPrefix_contains tree tree.condition sourcePath
              tree.containsCondition_self)
        have hsourceRemainingGood :
            ∀ condition,
              condition ∈ sourcePrefix.2.map Prod.snd
              -> condition.GoodUnder inheritedBooleanCondition := by
          intro condition hcondition
          exact hsourceGood condition
            (deepestExistingPrefix_remaining_subset tree tree.condition sourcePath
              condition hcondition)
        let shrunk :=
          shrinkBranches schema inheritedBooleanCondition sourcePrefix.1 target
            (sourcePrefix.2.map Prod.fst)
        let retainedPath :=
          match pathForBranches? schema inheritedBooleanCondition sourcePrefix.1
              shrunk with
          | some path =>
              if pathEnd sourcePrefix.1 path = target then path else sourcePrefix.2
          | none => sourcePrefix.2
        have hretainedGood :
            ∀ condition,
              condition ∈ retainedPath.map Prod.snd
              -> condition.GoodUnder inheritedBooleanCondition := by
          unfold retainedPath
          split
          · rename_i path hpath
            split
            · exact pathForBranches?_goodUnder schema inheritedBooleanCondition
                sourcePrefix.1 shrunk path hsourcePrefixGood hpath
            · exact hsourceRemainingGood
          · exact hsourceRemainingGood
        let retainedPrefix :=
          deepestExistingPrefix tree sourcePrefix.1 retainedPath
        have hmissingGood :
            ∀ condition,
              condition ∈ retainedPrefix.2.map Prod.snd
              -> condition.GoodUnder inheritedBooleanCondition := by
          intro condition hcondition
          exact hretainedGood condition
            (deepestExistingPrefix_remaining_subset tree sourcePrefix.1
              retainedPath condition hcondition)
        change
          ∀ condition,
            condition ∈
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
                  | none => tree).nodeConditions
            -> condition.GoodUnder inheritedBooleanCondition
        cases hmissing : retainedPrefix.2 with
        | nil =>
            simp only
            split
            · rename_i modifiedTree hmodifiedTree
              apply nodeConditions_goodUnder_of_perm inheritedBooleanCondition _ _
                (tree.nodeConditions_appendAtCondition?_eq_some retainedPrefix.1 [field]
                  [] modifiedTree hmodifiedTree)
              simpa [branchNodeConditions] using htree
            · exact htree
        | cons head rest =>
            simp only
            let simplePath := erasePathCycles (head :: rest)
            let addedBranches := branchesForPath simplePath [field]
            split
            · rename_i modifiedTree hmodifiedTree
              apply nodeConditions_goodUnder_of_perm inheritedBooleanCondition _ _
                (tree.nodeConditions_appendAtCondition?_eq_some retainedPrefix.1 []
                  addedBranches modifiedTree hmodifiedTree)
              intro condition hcondition
              simp only [List.mem_append] at hcondition
              exact hcondition.elim
                (htree condition)
                (fun hadd =>
                  hmissingGood condition (by
                    rw [hmissing]
                    exact erasePathCycles_map_subset (head :: rest) condition (by
                      simpa [addedBranches, simplePath,
                        branchConditions_branchesForPath] using hadd)))
            · exact htree

-----------------------------------------------------------------------------------------
-- Extraction
-----------------------------------------------------------------------------------------

theorem insertSelections_wellFormed
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition) (branches : List BranchCondition)
    (tree : Tree) (selectionSet : List Selection)
    (htree : tree.WellFormed schema inheritedBooleanCondition)
    : (insertSelections schema inheritedBooleanCondition currentCondition branches tree
        selectionSet).WellFormed
        schema inheritedBooleanCondition := by
  cases selectionSet with
  | nil =>
      simpa [insertSelections] using htree
  | cons selection rest =>
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
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
          apply insertSelections_wellFormed schema inheritedBooleanCondition
            currentCondition branches treeAfterField rest
          unfold treeAfterField
          split
          · exact htree
          · split
            · exact htree
            · have hgood := tree.nodeConditions_insertField_goodUnder schema
                  inheritedBooleanCondition (branches ++ ‹_›) ‹_› storedField
                  (fun condition hcondition =>
                    ⟨htree.conditionsFeasible condition hcondition,
                      htree.conditionsDisjointFromInherited condition hcondition⟩)
              exact {
                  nodeConditionsNodup := tree.nodeConditions_insertField_nodup schema
                    inheritedBooleanCondition (branches ++ ‹_›) ‹_› storedField
                    htree.nodeConditionsNodup
                  conditionsFeasible := fun condition hcondition =>
                    (hgood condition hcondition).1
                  conditionsDisjointFromInherited := fun condition hcondition =>
                    (hgood condition hcondition).2
                  branchesCoherent := tree.insertField_branchesCoherent schema
                    inheritedBooleanCondition (branches ++ ‹_›) ‹_› storedField
                    htree.branchesCoherent
                  fieldGroupsUnique := tree.insertField_fieldGroupsUnique schema
                    inheritedBooleanCondition (branches ++ ‹_›) ‹_› storedField
                    htree.fieldGroupsUnique
                }
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
          apply insertSelections_wellFormed schema inheritedBooleanCondition
            currentCondition branches treeAfterFragment rest
          unfold treeAfterFragment
          cases hbranches
                : branchConditionsForInlineFragment? typeCondition directives with
          | none =>
              simp
              exact htree
          | some nextBranches =>
              simp only
              cases hcondition
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition nextBranches with
              | none =>
                  simp
                  exact htree
              | some nextCondition =>
                  simp only
                  exact insertSelections_wellFormed schema
                    inheritedBooleanCondition nextCondition
                    (branches ++ nextBranches) tree childSelectionSet htree
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem Tree.root_wellFormed
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (hpossible : schema.getPossibleTypes parentType ≠ [])
    (hinherited : (canonicalBooleanCondition inheritedBooleanCondition).isSome = true)
    : (Tree.root (rootCondition schema parentType)).WellFormed schema
        inheritedBooleanCondition := by
  constructor
  · simp [Tree.root, Tree.nodeConditions, branchNodeConditions]
  · intro condition hcondition
    have hequal : condition = rootCondition schema parentType := by
      simpa [Tree.root, Tree.nodeConditions, branchNodeConditions] using hcondition
    subst condition
    exact ⟨
      hpossible,
      by
        simpa [Condition.FeasibleUnder, rootCondition] using hinherited
    ⟩
  · intro condition hcondition
    have hequal : condition = rootCondition schema parentType := by
      simpa [Tree.root, Tree.nodeConditions, branchNodeConditions] using hcondition
    subst condition
    simp [booleanConditionsDisjoint, rootCondition]
  · simp [Tree.BranchesCoherent, Tree.root, branchesCoherent]
  · simp [Tree.root, Tree.fieldGroupsUnique, branchFieldGroupsUnique]

theorem ofSelectionSetInScope_wellFormed
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    (hpossible : schema.getPossibleTypes parentType ≠ [])
    (hinherited : (canonicalBooleanCondition inheritedBooleanCondition).isSome = true)
    : Tree.WellFormed schema
        (ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet)
        inheritedBooleanCondition := by
  unfold ofSelectionSetInScope
  exact insertSelections_wellFormed schema inheritedBooleanCondition
      (rootCondition schema parentType) []
      (Tree.root (rootCondition schema parentType)) selectionSet
      (Tree.root_wellFormed schema parentType inheritedBooleanCondition
        hpossible hinherited)

theorem extraction_correct
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : ExtractionCorrect schema parentType inheritedBooleanCondition selectionSet := by
  intro hpossible hinherited
  exact ofSelectionSetInScope_wellFormed schema parentType inheritedBooleanCondition
    selectionSet hpossible hinherited

theorem ofSelectionSet_wellFormed
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    (hpossible : schema.getPossibleTypes parentType ≠ [])
    : (ofSelectionSet schema parentType selectionSet).WellFormed schema [] := by
  apply ofSelectionSetInScope_wellFormed schema parentType [] selectionSet hpossible
  simp [canonicalBooleanCondition]

theorem ofOperation_wellFormed
    (schema : Schema) (operation : Operation)
    (hpossible : schema.getPossibleTypes (operation.rootType schema) ≠ [])
    : (ofOperation schema operation).WellFormed schema [] := by
  exact ofSelectionSet_wellFormed schema (operation.rootType schema)
    operation.selectionSet hpossible

theorem ofOperation_wellFormed_of_schemaWellFormed
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : (ofOperation schema operation).WellFormed schema [] := by
  apply ofOperation_wellFormed schema operation
  rcases hschema.2.1 with ⟨objectType, hlookup⟩
  simp [Operation.rootType, OperationType.rootType, Schema.getPossibleTypes, hlookup]

end ConditionTree
end GraphQL
