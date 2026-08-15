import Proofs.GraphQL.Theories.ConditionTree.Soundness
import Proofs.GraphQL.Theories.SelectionConditions.BooleanVariables

/-! Boolean-variable provenance for extracted condition trees. -/

namespace GraphQL
namespace ConditionTree

open GraphQL.SelectionConditions

namespace BranchCondition

export GraphQL.SelectionConditions.BranchCondition (BooleanVariableWithin)

end BranchCondition

mutual
  def Tree.BooleanBranchesWithin (variables : List Name) (tree : Tree) : Prop :=
    branchesBooleanVariablesWithin variables tree.branches
  termination_by 2 * sizeOf tree
  decreasing_by
    cases tree
    simp_wf
    omega

  def branchesBooleanVariablesWithin (variables : List Name) : List (Branch Tree) -> Prop
    | [] => True
    | branch :: rest =>
        branch.condition.BooleanVariableWithin variables
        ∧ branch.body.BooleanBranchesWithin variables
        ∧ branchesBooleanVariablesWithin variables rest
  termination_by branches => 2 * sizeOf branches + 1
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

theorem branchesBooleanVariablesWithin_append
    (variables : List Name) (left right : List (Branch Tree))
    : branchesBooleanVariablesWithin variables (left ++ right)
      ↔ branchesBooleanVariablesWithin variables left
        ∧ branchesBooleanVariablesWithin variables right := by
  induction left with
  | nil => simp [branchesBooleanVariablesWithin]
  | cons branch rest ih =>
      simp only [List.cons_append, branchesBooleanVariablesWithin, ih]
      constructor
      · rintro ⟨hcondition, hbody, hrest, hright⟩
        exact ⟨⟨hcondition, hbody, hrest⟩, hright⟩
      · rintro ⟨⟨hcondition, hbody, hrest⟩, hright⟩
        exact ⟨hcondition, hbody, hrest, hright⟩

mutual
  private theorem Tree.modifyAtCondition?_booleanBranchesWithin
      (variables : List Name) (target : Condition) (modify : Tree -> Tree)
      (tree modifiedTree : Tree)
      (htree : tree.BooleanBranchesWithin variables)
      (hmodify
        : ∀ node,
            node.BooleanBranchesWithin variables
            -> (modify node).BooleanBranchesWithin variables)
      (hresult : tree.modifyAtCondition? target modify = some modifiedTree)
      : modifiedTree.BooleanBranchesWithin variables := by
    rw [Tree.modifyAtCondition?] at hresult
    split at hresult
    · cases hresult
      exact hmodify tree htree
    · split at hresult
      · contradiction
      · rename_i modifiedBranches hbranches
        cases hresult
        simp only [Tree.BooleanBranchesWithin]
        have htree' : branchesBooleanVariablesWithin variables tree.branches := by
          simpa [Tree.BooleanBranchesWithin] using htree
        exact modifyBranchesAtCondition?_booleanBranchesWithin variables target modify
          tree.branches modifiedBranches htree' hmodify hbranches
  termination_by 2 * sizeOf tree
  decreasing_by
    cases tree
    simp_wf
    omega

  private theorem modifyBranchesAtCondition?_booleanBranchesWithin
      (variables : List Name) (target : Condition) (modify : Tree -> Tree)
      (branches modifiedBranches : List (Branch Tree))
      (hbranches : branchesBooleanVariablesWithin variables branches)
      (hmodify
        : ∀ node,
            node.BooleanBranchesWithin variables
            -> (modify node).BooleanBranchesWithin variables)
      (hresult
        : modifyBranchesAtCondition? target modify branches = some modifiedBranches)
      : branchesBooleanVariablesWithin variables modifiedBranches := by
    cases branches with
    | nil => simp [modifyBranchesAtCondition?] at hresult
    | cons branch rest =>
        rw [modifyBranchesAtCondition?] at hresult
        simp only [branchesBooleanVariablesWithin] at hbranches
        cases hbody : branch.body.modifyAtCondition? target modify with
        | some modifiedBody =>
            simp only [hbody] at hresult
            cases hresult
            simp only [branchesBooleanVariablesWithin]
            exact ⟨hbranches.1,
              branch.body.modifyAtCondition?_booleanBranchesWithin variables target modify
                modifiedBody hbranches.2.1 hmodify hbody,
              hbranches.2.2⟩
        | none =>
            simp only [hbody] at hresult
            cases hrest : modifyBranchesAtCondition? target modify rest with
            | none => simp [hrest] at hresult
            | some modifiedRest =>
                simp only [hrest] at hresult
                cases hresult
                simp only [branchesBooleanVariablesWithin]
                exact ⟨hbranches.1, hbranches.2.1,
                  modifyBranchesAtCondition?_booleanBranchesWithin variables target modify
                    rest modifiedRest hbranches.2.2 hmodify hrest⟩
  termination_by 2 * sizeOf branches + 1
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega
end

theorem Tree.appendAtCondition?_booleanBranchesWithin
    (variables : List Name) (tree modifiedTree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    (htree : tree.BooleanBranchesWithin variables)
    (hadded : branchesBooleanVariablesWithin variables branches)
    (hresult : tree.appendAtCondition? target fields branches = some modifiedTree)
    : modifiedTree.BooleanBranchesWithin variables := by
  let modify : Tree -> Tree := fun node =>
    {
      node with
        fields := fields.foldl (fun groups field => addFieldToGroups field groups)
          node.fields
        branches := node.branches ++ branches
    }
  change tree.modifyAtCondition? target modify = some modifiedTree at hresult
  apply tree.modifyAtCondition?_booleanBranchesWithin variables target modify modifiedTree
    htree _ hresult
  intro node hnode
  simp only [modify, Tree.BooleanBranchesWithin]
  exact (branchesBooleanVariablesWithin_append variables node.branches branches).2
    ⟨by simpa [Tree.BooleanBranchesWithin] using hnode, hadded⟩

private theorem pathForBranches?_map_fst
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start : Condition) (source : List BranchCondition)
    {path : List (BranchCondition × Condition)}
    (hpath : pathForBranches? schema inheritedBooleanCondition start source = some path)
    : path.map Prod.fst = source := by
  induction source generalizing start path with
  | nil =>
      simp [pathForBranches?] at hpath
      simp [hpath]
  | cons branch rest ih =>
      rw [pathForBranches?] at hpath
      cases hnext : conditionForBranch? schema inheritedBooleanCondition start branch with
      | none => simp [hnext] at hpath
      | some next =>
          cases hrest : pathForBranches? schema inheritedBooleanCondition next rest with
          | none =>
              simp [hnext, hrest] at hpath
          | some restPath =>
              simp [hnext, hrest] at hpath
              subst path
              simp [ih next hrest]

private def Every {α : Type} (predicate : α -> Prop) (items : List α) : Prop :=
  ∀ item, item ∈ items -> predicate item

private theorem deepestExistingPrefixFrom_remaining_all
    (tree : Tree) (remaining : List (BranchCondition × Condition))
    (best : Condition × List (BranchCondition × Condition))
    (keep : BranchCondition × Condition -> Prop)
    (hremaining : Every keep remaining) (hbest : Every keep best.2)
    : Every keep (deepestExistingPrefixFrom tree remaining best).2 := by
  induction remaining generalizing best with
  | nil => simpa [deepestExistingPrefixFrom] using hbest
  | cons edge rest ih =>
      simp only [deepestExistingPrefixFrom]
      split
      · apply ih (edge.2, rest)
        · intro item hitem
          exact hremaining item (by simp [hitem])
        · intro item hitem
          exact hremaining item (by simp [hitem])
      · apply ih best
        · intro item hitem
          exact hremaining item (by simp [hitem])
        · exact hbest

private theorem deepestExistingPrefix_remaining_all
    (tree : Tree) (start : Condition)
    (path : List (BranchCondition × Condition))
    (keep : BranchCondition × Condition -> Prop)
    (hpath : Every keep path)
    : Every keep (deepestExistingPrefix tree start path).2 := by
  unfold deepestExistingPrefix
  exact deepestExistingPrefixFrom_remaining_all tree path (start, path) keep hpath hpath

private theorem booleanBranchConditions_every
    (variables : List Name) (branches : List BranchCondition)
    (hbranches : Every (BranchCondition.BooleanVariableWithin variables) branches)
    : Every (BranchCondition.BooleanVariableWithin variables)
        (booleanBranchConditions branches) := by
  intro candidate hcandidate
  unfold booleanBranchConditions at hcandidate
  rcases List.mem_filterMap.mp hcandidate with ⟨branch, hbranch, hmapped⟩
  cases branch with
  | typeCondition typeName => simp at hmapped
  | booleanLiteral literal =>
      simp only [Option.some.injEq] at hmapped
      subst candidate
      exact hbranches (.booleanLiteral literal) hbranch

private theorem singletonObjectBranchPath?_booleanVariablesWithin
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start target : Condition) (retained result : List BranchCondition)
    (variables : List Name)
    (hretained : Every (BranchCondition.BooleanVariableWithin variables) retained)
    (hresult
      : singletonObjectBranchPath? schema inheritedBooleanCondition start target retained
        = some result)
    : Every (BranchCondition.BooleanVariableWithin variables) result := by
  unfold singletonObjectBranchPath? at hresult
  cases htypes : retained.any BranchCondition.isTypeCondition with
  | false => simp [htypes] at hresult
  | true =>
      simp only [htypes, Bool.not_true, Bool.false_eq_true, if_false] at hresult
      cases hpossible : target.possibleTypes with
      | nil => simp [hpossible] at hresult
      | cons objectTypeName rest =>
          cases rest with
          | cons next tail => simp [hpossible] at hresult
          | nil =>
              simp only [hpossible] at hresult
              cases hobject : schema.lookupObject objectTypeName with
              | none => simp [hobject] at hresult
              | some objectType =>
                  let candidate :=
                    .typeCondition objectTypeName :: booleanBranchConditions retained
                  by_cases hcondition : conditionForBranches? schema
                      inheritedBooleanCondition start candidate = some target
                  · simp [hobject, candidate, hcondition] at hresult
                    subst result
                    intro branch hbranch
                    simp only [List.mem_cons] at hbranch
                    rcases hbranch with rfl | hbranch
                    · trivial
                    · exact booleanBranchConditions_every variables retained hretained
                        branch hbranch
                  · simp [hobject, candidate, hcondition] at hresult

private theorem shrinkBranches_booleanVariablesWithin
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start target : Condition) (source : List BranchCondition)
    (variables : List Name)
    (hsource : Every (BranchCondition.BooleanVariableWithin variables) source)
    : Every (BranchCondition.BooleanVariableWithin variables)
        (shrinkBranches schema inheritedBooleanCondition start target source) := by
  -- Boolean edges are only deleted by greedy shrinking. The optional singleton-object
  -- replacement changes type edges and retains the same Boolean edges.
  unfold shrinkBranches
  let retained := shrinkBranches.go schema inheritedBooleanCondition start target [] source
  have go_preserves : ∀ (kept remaining : List BranchCondition),
      Every (BranchCondition.BooleanVariableWithin variables) kept
      -> Every (BranchCondition.BooleanVariableWithin variables) remaining
      -> Every (BranchCondition.BooleanVariableWithin variables)
          (shrinkBranches.go schema inheritedBooleanCondition start target
            kept remaining) := by
    intro kept remaining hkept hremaining
    induction remaining generalizing kept with
    | nil => simpa [shrinkBranches.go] using hkept
    | cons branch rest ih =>
        rw [shrinkBranches.go]
        have hrest : Every (BranchCondition.BooleanVariableWithin variables) rest := by
          intro candidate hcandidate
          exact hremaining candidate (by simp [hcandidate])
        split
        · exact ih kept hkept hrest
        · apply ih (kept ++ [branch])
          · intro candidate hcandidate
            simp only [List.mem_append, List.mem_singleton] at hcandidate
            rcases hcandidate with hcandidate | rfl
            · exact hkept candidate hcandidate
            · exact hremaining candidate (by simp)
          · exact hrest
  have hretained : Every (BranchCondition.BooleanVariableWithin variables) retained := by
    exact go_preserves [] source (by simp [Every]) hsource
  change Every (BranchCondition.BooleanVariableWithin variables)
    ((singletonObjectBranchPath? schema inheritedBooleanCondition start target retained)
      |>.getD retained)
  cases hreplacement
        : singletonObjectBranchPath? schema inheritedBooleanCondition start target
            retained with
  | none =>
      simpa using hretained
  | some replacement =>
      simpa using singletonObjectBranchPath?_booleanVariablesWithin schema
          inheritedBooleanCondition start target retained replacement variables hretained
          hreplacement

private theorem branchesForPath_booleanBranchesWithin
    (variables : List Name) (path : List (BranchCondition × Condition))
    (fields : List NamedField)
    (hpath : Every (fun edge => edge.1.BooleanVariableWithin variables) path)
    : branchesBooleanVariablesWithin variables (branchesForPath path fields) := by
  induction path with
  | nil => simp [branchesForPath, branchesBooleanVariablesWithin]
  | cons edge rest ih =>
      rcases edge with ⟨condition, cumulative⟩
      cases rest with
      | nil =>
          simp only [branchesForPath, branchesBooleanVariablesWithin,
            Tree.BooleanBranchesWithin, true_and]
          exact ⟨hpath (condition, cumulative) (by simp), trivial⟩
      | cons next tail =>
          simp only [branchesForPath, branchesBooleanVariablesWithin,
            Tree.BooleanBranchesWithin]
          refine ⟨hpath (condition, cumulative) (by simp), ?_, trivial⟩
          apply ih
          intro candidate hcandidate
          exact hpath candidate (by simp [hcandidate])

private theorem pathPrefixThrough_every
    (target : Condition) (path : List (BranchCondition × Condition))
    (keep : BranchCondition × Condition -> Prop) (hpath : Every keep path)
    : Every keep (pathPrefixThrough target path) := by
  induction path with
  | nil => simp [pathPrefixThrough, Every]
  | cons edge rest ih =>
      rw [pathPrefixThrough]
      split
      · intro candidate hcandidate
        have heq : candidate = edge := List.mem_singleton.mp hcandidate
        subst candidate
        exact hpath edge (by simp)
      · intro candidate hcandidate
        simp only [List.mem_cons] at hcandidate
        rcases hcandidate with rfl | hcandidate
        · exact hpath _ (by simp)
        · exact ih (by
            intro item hitem
            exact hpath item (by simp [hitem])) candidate hcandidate

private theorem erasePathCyclesFrom_every
    (kept remaining : List (BranchCondition × Condition))
    (keep : BranchCondition × Condition -> Prop)
    (hkept : Every keep kept) (hremaining : Every keep remaining)
    : Every keep (erasePathCyclesFrom kept remaining) := by
  induction remaining generalizing kept with
  | nil => simpa [erasePathCyclesFrom] using hkept
  | cons edge rest ih =>
      rw [erasePathCyclesFrom]
      have hrest : Every keep rest := by
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])
      split
      · apply ih (pathPrefixThrough edge.2 kept)
        · exact pathPrefixThrough_every edge.2 kept keep hkept
        · exact hrest
      · apply ih (kept ++ [edge])
        · intro candidate hcandidate
          simp only [List.mem_append, List.mem_singleton] at hcandidate
          rcases hcandidate with hcandidate | rfl
          · exact hkept candidate hcandidate
          · exact hremaining _ (by simp)
        · exact hrest

private theorem erasePathCycles_every
    (path : List (BranchCondition × Condition))
    (keep : BranchCondition × Condition -> Prop) (hpath : Every keep path)
    : Every keep (erasePathCycles path) := by
  unfold erasePathCycles
  exact erasePathCyclesFrom_every [] path keep (by simp [Every]) hpath

private theorem Every.map_fst
    (variables : List Name) (path : List (BranchCondition × Condition))
    (hpath : Every (fun edge => edge.1.BooleanVariableWithin variables) path)
    : Every (BranchCondition.BooleanVariableWithin variables) (path.map Prod.fst) := by
  intro branch hbranch
  rcases List.mem_map.mp hbranch with ⟨edge, hedge, rfl⟩
  exact hpath edge hedge

theorem Tree.insertField_booleanBranchesWithin
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (variables : List Name) (tree : Tree) (sourcePath : List BranchCondition)
    (target : Condition) (field : NamedField)
    (htree : tree.BooleanBranchesWithin variables)
    (hsource : Every (BranchCondition.BooleanVariableWithin variables) sourcePath)
    : (tree.insertField schema inheritedBooleanCondition sourcePath target field)
      |>.BooleanBranchesWithin variables := by
  unfold Tree.insertField
  split
  · rename_i modifiedTree hmodified
    exact tree.appendAtCondition?_booleanBranchesWithin variables modifiedTree target
      [field] [] htree (by simp [branchesBooleanVariablesWithin]) hmodified
  · rename_i hnoAppend
    cases hsourcePath
          : pathForBranches? schema inheritedBooleanCondition tree.condition
              sourcePath with
    | none => exact htree
    | some sourcePathWithConditions =>
        have hsourcePathWithConditions : Every
            (fun edge => edge.1.BooleanVariableWithin variables)
            sourcePathWithConditions := by
          intro edge hedge
          apply hsource edge.1
          have hmap := congrArg (fun items => edge.1 ∈ items)
            (pathForBranches?_map_fst schema inheritedBooleanCondition tree.condition
              sourcePath hsourcePath)
          simpa using hmap.mp (List.mem_map.mpr ⟨edge, hedge, rfl⟩)
        let sourcePrefix := deepestExistingPrefix tree tree.condition
          sourcePathWithConditions
        have hsourcePrefix : Every
            (fun edge => edge.1.BooleanVariableWithin variables) sourcePrefix.2 := by
          exact deepestExistingPrefix_remaining_all tree tree.condition
            sourcePathWithConditions _ hsourcePathWithConditions
        let shrunk := shrinkBranches schema inheritedBooleanCondition sourcePrefix.1
          target (sourcePrefix.2.map Prod.fst)
        have hshrunk : Every (BranchCondition.BooleanVariableWithin variables) shrunk := by
          apply shrinkBranches_booleanVariablesWithin schema inheritedBooleanCondition
            sourcePrefix.1 target (sourcePrefix.2.map Prod.fst) variables
          exact Every.map_fst variables sourcePrefix.2 hsourcePrefix
        let retainedPath :=
          match pathForBranches? schema inheritedBooleanCondition sourcePrefix.1 shrunk with
          | some path => if pathEnd sourcePrefix.1 path = target then path else sourcePrefix.2
          | none => sourcePrefix.2
        have hretainedPath : Every
            (fun edge => edge.1.BooleanVariableWithin variables) retainedPath := by
          unfold retainedPath
          cases hpath
                : pathForBranches? schema inheritedBooleanCondition sourcePrefix.1
                    shrunk with
          | none => exact hsourcePrefix
          | some path =>
              by_cases hend : pathEnd sourcePrefix.1 path = target
              · simp only [hend, if_true]
                intro edge hedge
                apply hshrunk edge.1
                have hmap := congrArg (fun items => edge.1 ∈ items)
                  (pathForBranches?_map_fst schema inheritedBooleanCondition
                    sourcePrefix.1 shrunk hpath)
                simpa using hmap.mp (List.mem_map.mpr ⟨edge, hedge, rfl⟩)
              · simpa [hend] using hsourcePrefix
        let retainedPrefix := deepestExistingPrefix tree sourcePrefix.1 retainedPath
        have hretainedPrefix : Every
            (fun edge => edge.1.BooleanVariableWithin variables) retainedPrefix.2 := by
          exact deepestExistingPrefix_remaining_all tree sourcePrefix.1 retainedPath _
            hretainedPath
        have hfinal :
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
              | none => tree).BooleanBranchesWithin
            variables := by
          cases hmissing : retainedPrefix.2 with
          | nil =>
              cases happend : tree.appendAtCondition? retainedPrefix.1 [field] [] with
              | none => exact htree
              | some modifiedTree =>
                  exact tree.appendAtCondition?_booleanBranchesWithin variables
                    modifiedTree retainedPrefix.1 [field] [] htree
                    (by simp [branchesBooleanVariablesWithin]) happend
          | cons head rest =>
              simp only
              let simplePath := erasePathCycles (head :: rest)
              have hsimplePath : Every
                  (fun edge => edge.1.BooleanVariableWithin variables) simplePath := by
                exact erasePathCycles_every (head :: rest)
                  (fun edge => edge.1.BooleanVariableWithin variables)
                  (by simpa [hmissing] using hretainedPrefix)
              let addedBranches := branchesForPath simplePath [field]
              have hadded : branchesBooleanVariablesWithin variables addedBranches := by
                exact branchesForPath_booleanBranchesWithin variables simplePath [field]
                  hsimplePath
              cases happend
                    : tree.appendAtCondition? retainedPrefix.1 [] addedBranches with
              | none => exact htree
              | some modifiedTree =>
                  exact tree.appendAtCondition?_booleanBranchesWithin variables
                    modifiedTree retainedPrefix.1 [] addedBranches htree hadded happend
        have hresultEq :
            tree.insertField schema inheritedBooleanCondition sourcePath target field
              = match retainedPrefix.2 with
                | [] =>
                    match tree.appendAtCondition? retainedPrefix.1 [field] [] with
                    | some modifiedTree => modifiedTree
                    | none => tree
                | missingPath =>
                    let simplePath := erasePathCycles missingPath
                    match tree.appendAtCondition? retainedPrefix.1 []
                        (branchesForPath simplePath [field]) with
                    | some modifiedTree => modifiedTree
                    | none => tree := by
          unfold Tree.insertField
          rw [hnoAppend, hsourcePath]
          rfl
        rw [← hresultEq] at hfinal
        simpa only [Tree.insertField, hnoAppend, hsourcePath] using hfinal

theorem insertSelections_booleanBranchesWithin
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition) (branches : List BranchCondition)
    (tree : Tree) (selectionSet : List Selection) (variables : List Name)
    (htree : tree.BooleanBranchesWithin variables)
    (hbranches : Every (BranchCondition.BooleanVariableWithin variables) branches)
    (hselection
      : ∀ variableName,
          variableName ∈ selectionSetBooleanVariables selectionSet
          -> variableName ∈ variables)
    : (insertSelections schema inheritedBooleanCondition currentCondition branches tree
        selectionSet).BooleanBranchesWithin
        variables := by
  cases hselectionSet : selectionSet with
  | nil => simpa [hselectionSet, insertSelections] using htree
  | cons selection rest =>
      subst selectionSet
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          rw [insertSelections]
          cases hnextBranches : branchConditionsForDirectives? directives with
          | none =>
              exact insertSelections_booleanBranchesWithin schema
                inheritedBooleanCondition currentCondition branches tree rest variables
                htree hbranches (by
                  intro variableName hvariable
                  apply hselection variableName
                  simp [selectionSetBooleanVariables, selectionBooleanVariables,
                    hvariable])
          | some nextBranches =>
              cases hnextCondition
                    : conditionForBranches? schema
                        inheritedBooleanCondition currentCondition nextBranches with
              | none =>
                  simp only [hnextCondition]
                  exact insertSelections_booleanBranchesWithin schema
                    inheritedBooleanCondition currentCondition branches tree rest variables
                    htree hbranches (by
                      intro variableName hvariable
                      apply hselection variableName
                      simp [selectionSetBooleanVariables, selectionBooleanVariables,
                        hvariable])
              | some nextCondition =>
                  let field : NamedField :=
                    {
                      responseName := responseName
                      field := {
                        fieldName := fieldName
                        arguments := arguments
                        selectionSet := childSelectionSet
                      }
                    }
                  let treeAfter := tree.insertField schema inheritedBooleanCondition
                    (branches ++ nextBranches) nextCondition field
                  have hnextWithin : Every
                      (BranchCondition.BooleanVariableWithin variables) nextBranches := by
                    apply branchConditionsForDirectives?_within directives nextBranches
                      variables hnextBranches
                    intro variableName hvariable
                    apply hselection variableName
                    simp [selectionSetBooleanVariables, selectionBooleanVariables,
                      hvariable]
                  have htreeAfter : treeAfter.BooleanBranchesWithin variables := by
                    exact Tree.insertField_booleanBranchesWithin schema
                      inheritedBooleanCondition variables tree
                      (branches ++ nextBranches) nextCondition field htree (by
                      intro branch hbranch
                      simp only [List.mem_append] at hbranch
                      exact hbranch.elim (hbranches branch) (hnextWithin branch))
                  simp only [hnextCondition]
                  exact insertSelections_booleanBranchesWithin schema
                    inheritedBooleanCondition currentCondition branches treeAfter rest
                    variables htreeAfter hbranches (by
                      intro variableName hvariable
                      apply hselection variableName
                      simp [selectionSetBooleanVariables, selectionBooleanVariables,
                        hvariable])
      | inlineFragment typeCondition directives childSelectionSet =>
          rw [insertSelections]
          cases hnextBranches
                : branchConditionsForInlineFragment? typeCondition directives with
          | none =>
              exact insertSelections_booleanBranchesWithin schema
                inheritedBooleanCondition currentCondition branches tree rest variables
                htree hbranches (by
                  intro variableName hvariable
                  apply hselection variableName
                  simp [selectionSetBooleanVariables, selectionBooleanVariables,
                    hvariable])
          | some nextBranches =>
              cases hnextCondition
                    : conditionForBranches? schema
                        inheritedBooleanCondition currentCondition nextBranches with
              | none =>
                  simp only [hnextCondition]
                  exact insertSelections_booleanBranchesWithin schema
                    inheritedBooleanCondition currentCondition branches tree rest variables
                    htree hbranches (by
                      intro variableName hvariable
                      apply hselection variableName
                      simp [selectionSetBooleanVariables, selectionBooleanVariables,
                        hvariable])
              | some nextCondition =>
                  have hnextWithin : Every
                      (BranchCondition.BooleanVariableWithin variables) nextBranches := by
                    apply branchConditionsForInlineFragment?_within typeCondition directives
                      nextBranches variables hnextBranches
                    intro variableName hvariable
                    apply hselection variableName
                    simp [selectionSetBooleanVariables, selectionBooleanVariables,
                      hvariable]
                  let treeAfter := insertSelections schema inheritedBooleanCondition
                    nextCondition (branches ++ nextBranches) tree childSelectionSet
                  have htreeAfter : treeAfter.BooleanBranchesWithin variables := by
                    apply insertSelections_booleanBranchesWithin schema
                      inheritedBooleanCondition nextCondition (branches ++ nextBranches)
                      tree childSelectionSet variables htree
                    · intro branch hbranch
                      simp only [List.mem_append] at hbranch
                      exact hbranch.elim (hbranches branch) (hnextWithin branch)
                    · intro variableName hvariable
                      apply hselection variableName
                      simp [selectionSetBooleanVariables, selectionBooleanVariables,
                        hvariable]
                  simp only [hnextCondition]
                  exact insertSelections_booleanBranchesWithin schema
                    inheritedBooleanCondition currentCondition branches treeAfter rest
                    variables htreeAfter hbranches (by
                      intro variableName hvariable
                      apply hselection variableName
                      simp [selectionSetBooleanVariables, selectionBooleanVariables,
                        hvariable])
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem ofSelectionSetInScope_booleanBranchesWithin
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : (ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet)
      |>.BooleanBranchesWithin (selectionSetBooleanVariables selectionSet) := by
  unfold ofSelectionSetInScope
  apply insertSelections_booleanBranchesWithin schema inheritedBooleanCondition
    (rootCondition schema parentType) [] (Tree.root (rootCondition schema parentType))
    selectionSet (selectionSetBooleanVariables selectionSet)
  · simp [Tree.root, Tree.BooleanBranchesWithin, branchesBooleanVariablesWithin]
  · simp [Every]
  · exact fun _variableName hvariable => hvariable

-- Every nested selection retained by extraction uses only variables from `variables`.
-- `fieldEntries` ranges over the whole recursive condition-tree boundary, so this
-- single clause covers fields stored at both the root and branch bodies.
def Tree.StoredFieldBooleanVariablesWithin (variables : List Name) (tree : Tree) : Prop :=
  ∀ condition responseName fieldName arguments selectionSet,
    (condition, Selection.field responseName fieldName arguments [] selectionSet)
      ∈ tree.fieldEntries
    -> ∀ variableName,
        variableName ∈ selectionSetBooleanVariables selectionSet
        -> variableName ∈ variables

private theorem collectConditionEntries_childBooleanVariables_mem
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition condition : Condition)
    (source : List Selection) (responseName fieldName : Name)
    (arguments : List Argument) (selectionSet : List Selection)
    (hentry
      : (condition, Selection.field responseName fieldName arguments [] selectionSet)
        ∈ collectConditionEntries schema parentType inheritedBooleanCondition
            currentCondition source)
    (variableName : Name)
    (hvariable : variableName ∈ selectionSetBooleanVariables selectionSet)
    : variableName ∈ selectionSetBooleanVariables source := by
  cases hsource : source with
  | nil => simp [hsource, collectConditionEntries] at hentry
  | cons selection rest =>
      subst source
      cases selection with
      | field sourceResponseName sourceFieldName sourceArguments directives
          childSelectionSet =>
          rw [collectConditionEntries] at hentry
          cases hbranches : branchConditionsForDirectives? directives with
          | none =>
              simp only [hbranches, List.nil_append] at hentry
              apply List.mem_append.mpr
              exact Or.inr
                (collectConditionEntries_childBooleanVariables_mem schema parentType
                  inheritedBooleanCondition currentCondition condition rest responseName
                  fieldName arguments selectionSet hentry variableName hvariable)
          | some branches =>
              cases hcondition
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition branches with
              | none =>
                  simp only [hbranches, hcondition, List.nil_append] at hentry
                  apply List.mem_append.mpr
                  exact Or.inr
                    (collectConditionEntries_childBooleanVariables_mem schema parentType
                      inheritedBooleanCondition currentCondition condition rest
                      responseName fieldName arguments selectionSet hentry variableName
                      hvariable)
              | some nextCondition =>
                  simp only [hbranches, hcondition, List.singleton_append,
                    List.mem_cons] at hentry
                  rcases hentry with hentry | hentry
                  · simp only [Prod.mk.injEq, Selection.field.injEq] at hentry
                    rcases hentry with ⟨_rfl, _hresponse, _hfield, _harguments,
                      hselectionSet⟩
                    have hselectionSet' := hselectionSet.2
                    subst childSelectionSet
                    simp [selectionSetBooleanVariables, selectionBooleanVariables,
                      hvariable]
                  · apply List.mem_append.mpr
                    exact Or.inr
                      (collectConditionEntries_childBooleanVariables_mem schema parentType
                        inheritedBooleanCondition currentCondition condition rest
                        responseName fieldName arguments selectionSet hentry variableName
                        hvariable)
      | inlineFragment typeCondition directives childSelectionSet =>
          rw [collectConditionEntries] at hentry
          cases hbranches
                : branchConditionsForInlineFragment? typeCondition directives with
          | none =>
              simp only [hbranches, List.nil_append] at hentry
              apply List.mem_append.mpr
              exact Or.inr
                (collectConditionEntries_childBooleanVariables_mem schema parentType
                  inheritedBooleanCondition currentCondition condition rest responseName
                  fieldName arguments selectionSet hentry variableName hvariable)
          | some branches =>
              cases hcondition
                    : conditionForBranches? schema inheritedBooleanCondition
                        currentCondition branches with
              | none =>
                  simp only [hbranches, hcondition, List.nil_append] at hentry
                  apply List.mem_append.mpr
                  exact Or.inr
                    (collectConditionEntries_childBooleanVariables_mem schema parentType
                      inheritedBooleanCondition currentCondition condition rest
                      responseName fieldName arguments selectionSet hentry variableName
                      hvariable)
              | some nextCondition =>
                  simp only [hbranches, hcondition, List.mem_append] at hentry
                  rcases hentry with hentry | hentry
                  · apply List.mem_append.mpr
                    apply Or.inl
                    apply List.mem_append.mpr
                    exact Or.inr
                      (collectConditionEntries_childBooleanVariables_mem schema
                        (parentTypeForBranches parentType branches)
                        inheritedBooleanCondition nextCondition condition childSelectionSet
                        responseName fieldName arguments selectionSet hentry variableName
                        hvariable)
                  · apply List.mem_append.mpr
                    exact Or.inr
                      (collectConditionEntries_childBooleanVariables_mem schema parentType
                        inheritedBooleanCondition currentCondition condition rest
                        responseName fieldName arguments selectionSet hentry variableName
                        hvariable)
termination_by SelectionSet.size source
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem ofSelectionSetInScope_storedFieldBooleanVariablesWithin
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : (ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet)
      |>.StoredFieldBooleanVariablesWithin
          (selectionSetBooleanVariables selectionSet) := by
  unfold Tree.StoredFieldBooleanVariablesWithin
  intro condition responseName fieldName arguments childSelectionSet hentry variableName
    hvariable
  rw [ofSelectionSetInScope_fieldEntries_mem schema parentType
    inheritedBooleanCondition selectionSet] at hentry
  exact collectConditionEntries_childBooleanVariables_mem schema parentType
    inheritedBooleanCondition (rootCondition schema parentType) condition selectionSet
    responseName fieldName arguments childSelectionSet hentry variableName hvariable

mutual
  theorem Tree.conditionTreeBooleanVariables_mem_of_within
      (tree : Tree) (variables : List Name)
      (hbranches : tree.BooleanBranchesWithin variables)
      (hfields : tree.StoredFieldBooleanVariablesWithin variables)
      (variableName : Name)
      (hvariable : variableName ∈ conditionTreeBooleanVariables tree)
      : variableName ∈ variables := by
    cases tree with
    | mk condition fields branches =>
        simp only [conditionTreeBooleanVariables, List.mem_append,
          List.mem_flatMap] at hvariable
        rcases hvariable with hfield | hbranch
        · rcases hfield with ⟨group, hgroup, field, hfield, hvariable⟩
          apply hfields condition group.responseName field.fieldName field.arguments
            field.selectionSet
          · unfold Tree.fieldEntries
            apply List.mem_append.mpr
            apply Or.inl
            apply List.mem_flatMap.mpr
            refine ⟨group, hgroup, ?_⟩
            apply List.mem_map.mpr
            refine ⟨field.toSelection group.responseName, ?_, rfl⟩
            unfold FieldGroup.selections
            exact List.mem_map.mpr ⟨field, hfield, rfl⟩
          · exact hvariable
        · unfold Tree.BooleanBranchesWithin at hbranches
          exact conditionTreeBranchesBooleanVariables_mem_of_within branches variables
            hbranches (by
              intro entryCondition responseName fieldName arguments selectionSet hentry
                candidate hcandidate
              apply hfields entryCondition responseName fieldName arguments selectionSet
              · simp [Tree.fieldEntries, hentry]
              · exact hcandidate) variableName hbranch

  theorem conditionTreeBranchesBooleanVariables_mem_of_within
      (branches : List (Branch Tree)) (variables : List Name)
      (hbranches : branchesBooleanVariablesWithin variables branches)
      (hfields
        : ∀ condition responseName fieldName arguments selectionSet,
            (condition, Selection.field responseName fieldName arguments [] selectionSet)
              ∈ branchFieldEntries branches
            -> ∀ variableName,
                variableName ∈ selectionSetBooleanVariables selectionSet
                -> variableName ∈ variables)
      (variableName : Name)
      (hvariable : variableName ∈ conditionTreeBranchesBooleanVariables branches)
      : variableName ∈ variables := by
    cases branches with
    | nil => simp [conditionTreeBranchesBooleanVariables] at hvariable
    | cons branch rest =>
        rw [conditionTreeBranchesBooleanVariables.eq_def] at hvariable
        rw [branchesBooleanVariablesWithin.eq_def] at hbranches
        rcases hbranches with ⟨hcondition, hbody, hrest⟩
        cases hconditionEq : branch.condition with
        | typeCondition typeName =>
            simp only [hconditionEq, List.nil_append, List.mem_append] at hvariable
            rcases hvariable with hbodyVariable | hrestVariable
            · apply branch.body.conditionTreeBooleanVariables_mem_of_within variables
                hbody
              · intro condition responseName fieldName arguments selectionSet hentry
                  candidate hcandidate
                apply hfields condition responseName fieldName arguments selectionSet
                · simp [branchFieldEntries, hentry]
                · exact hcandidate
              · exact hbodyVariable
            · exact conditionTreeBranchesBooleanVariables_mem_of_within rest variables
                hrest (by
                  intro condition responseName fieldName arguments selectionSet hentry
                    candidate hcandidate
                  apply hfields condition responseName fieldName arguments selectionSet
                  · simp [branchFieldEntries, hentry]
                  · exact hcandidate) variableName hrestVariable
        | booleanLiteral literal =>
            simp only [hconditionEq, List.mem_append, List.mem_singleton] at hvariable
            rcases hvariable with hcurrent | hrestVariable
            · rcases hcurrent with hconditionVariable | hbodyVariable
              · rw [hconditionVariable]
                simpa [BranchCondition.BooleanVariableWithin, hconditionEq] using hcondition
              · apply branch.body.conditionTreeBooleanVariables_mem_of_within variables
                  hbody
                · intro condition responseName fieldName arguments selectionSet hentry
                    candidate hcandidate
                  apply hfields condition responseName fieldName arguments selectionSet
                  · simp [branchFieldEntries, hentry]
                  · exact hcandidate
                · exact hbodyVariable
            · exact conditionTreeBranchesBooleanVariables_mem_of_within rest variables
                hrest (by
                  intro condition responseName fieldName arguments selectionSet hentry
                    candidate hcandidate
                  apply hfields condition responseName fieldName arguments selectionSet
                  · simp [branchFieldEntries, hentry]
                  · exact hcandidate) variableName hrestVariable
end

theorem ofSelectionSetInScope_booleanVariablesWithin
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (variableName : Name)
    (hvariable
      : variableName
        ∈ conditionTreeBooleanVariables
            (ofSelectionSetInScope schema parentType inheritedBooleanCondition
              selectionSet))
    : variableName ∈ selectionSetBooleanVariables selectionSet := by
  exact Tree.conditionTreeBooleanVariables_mem_of_within _ _
    (ofSelectionSetInScope_booleanBranchesWithin schema parentType
      inheritedBooleanCondition selectionSet)
    (ofSelectionSetInScope_storedFieldBooleanVariablesWithin schema parentType
      inheritedBooleanCondition selectionSet)
    variableName hvariable

end ConditionTree
end GraphQL
