import GraphQL.Theories.ConditionTree

/-! Preservation of branch-edge coherence by condition-tree extraction. -/

namespace GraphQL
namespace ConditionTree

-----------------------------------------------------------------------------------------
-- Structural coherence of extracted branch paths
-----------------------------------------------------------------------------------------

def PathCoherent (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    : Condition -> List (BranchCondition × Condition) -> Prop
  | _start, [] => True
  | start, (branch, next) :: rest =>
      conditionForBranch? schema inheritedBooleanCondition start branch = some next
      ∧ PathCoherent schema inheritedBooleanCondition next rest

theorem pathForBranches?_coherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start : Condition) (source : List BranchCondition)
    (path : List (BranchCondition × Condition))
    (hpath : pathForBranches? schema inheritedBooleanCondition start source = some path)
    : PathCoherent schema inheritedBooleanCondition start path := by
  induction source generalizing start path with
  | nil =>
      simp [pathForBranches?] at hpath
      subst path
      simp [PathCoherent]
  | cons branch rest ih =>
      simp only [pathForBranches?] at hpath
      cases hnext : conditionForBranch? schema inheritedBooleanCondition start branch with
      | none => simp [hnext] at hpath
      | some next =>
          cases hrest : pathForBranches? schema inheritedBooleanCondition next rest with
          | none => simp [hnext, hrest] at hpath
          | some nextPath =>
              simp [hnext, hrest] at hpath
              subst path
              exact ⟨hnext, ih next nextPath hrest⟩

theorem PathCoherent.tail
    {schema : Schema} {inheritedBooleanCondition : List BooleanLiteral}
    {start next : Condition} {branch : BranchCondition}
    {rest : List (BranchCondition × Condition)}
    (hpath : PathCoherent schema inheritedBooleanCondition start ((branch, next) :: rest))
    : PathCoherent schema inheritedBooleanCondition next rest :=
  hpath.2

theorem PathCoherent.append
    {schema : Schema} {inheritedBooleanCondition : List BooleanLiteral}
    {start : Condition} {left right : List (BranchCondition × Condition)}
    (hleft : PathCoherent schema inheritedBooleanCondition start left)
    (hright : PathCoherent schema inheritedBooleanCondition (pathEnd start left) right)
    : PathCoherent schema inheritedBooleanCondition start (left ++ right) := by
  induction left generalizing start with
  | nil => simpa [pathEnd, PathCoherent] using hright
  | cons edge rest ih =>
      rcases edge with ⟨branch, next⟩
      exact ⟨hleft.1, ih hleft.2 hright⟩

theorem pathEnd_append (start : Condition)
    (left right : List (BranchCondition × Condition))
    : pathEnd start (left ++ right) = pathEnd (pathEnd start left) right := by
  induction left generalizing start with
  | nil => rfl
  | cons edge rest ih =>
      rcases edge with ⟨branch, next⟩
      exact ih next

theorem PathCoherent.prefixThrough
    {schema : Schema} {inheritedBooleanCondition : List BooleanLiteral}
    {start : Condition} (target : Condition)
    {path : List (BranchCondition × Condition)}
    (hpath : PathCoherent schema inheritedBooleanCondition start path)
    : PathCoherent schema inheritedBooleanCondition start
        (pathPrefixThrough target path) := by
  induction path generalizing start with
  | nil => trivial
  | cons edge rest ih =>
      rcases edge with ⟨branch, next⟩
      simp only [pathPrefixThrough]
      split
      · exact ⟨hpath.1, trivial⟩
      · exact ⟨hpath.1, ih hpath.2⟩

theorem pathEnd_prefixThrough_of_mem
    (start target : Condition) (path : List (BranchCondition × Condition))
    (hmem : target ∈ path.map Prod.snd)
    : pathEnd start (pathPrefixThrough target path) = target := by
  induction path generalizing start with
  | nil => simp at hmem
  | cons edge rest ih =>
      rcases edge with ⟨branch, next⟩
      simp only [List.map_cons, List.mem_cons] at hmem
      simp only [pathPrefixThrough]
      by_cases heq : next = target
      · simp [heq, pathEnd]
      · simp only [heq, if_false, pathEnd]
        exact ih next (hmem.resolve_left (Ne.symm heq))

theorem erasePathCyclesFrom_coherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start : Condition)
    (kept remaining : List (BranchCondition × Condition))
    (hkept : PathCoherent schema inheritedBooleanCondition start kept)
    (hremaining
      : PathCoherent schema inheritedBooleanCondition (pathEnd start kept) remaining)
    : PathCoherent schema inheritedBooleanCondition start
        (erasePathCyclesFrom kept remaining) := by
  induction remaining generalizing kept with
  | nil => simpa [erasePathCyclesFrom] using hkept
  | cons edge rest ih =>
      rcases edge with ⟨branch, next⟩
      simp only [erasePathCyclesFrom]
      by_cases hcontains : (kept.map Prod.snd).contains next = true
      · simp only [if_pos hcontains]
        have hmem : next ∈ kept.map Prod.snd := List.contains_iff_mem.mp hcontains
        apply ih (pathPrefixThrough next kept)
        · exact hkept.prefixThrough next
        · rw [pathEnd_prefixThrough_of_mem start next kept hmem]
          exact hremaining.2
      · simp only [if_neg hcontains]
        apply ih (kept ++ [(branch, next)])
        · apply hkept.append
          simpa [pathEnd, PathCoherent] using hremaining.1
        · rw [pathEnd_append]
          simpa [pathEnd] using hremaining.2

theorem erasePathCycles_coherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start : Condition) (path : List (BranchCondition × Condition))
    (hpath : PathCoherent schema inheritedBooleanCondition start path)
    : PathCoherent schema inheritedBooleanCondition start (erasePathCycles path) := by
  unfold erasePathCycles
  exact erasePathCyclesFrom_coherent schema inheritedBooleanCondition start [] path
    (by trivial) (by simpa [pathEnd] using hpath)

theorem deepestExistingPrefixFrom_coherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (currentStart : Condition)
    (remaining : List (BranchCondition × Condition))
    (best : Condition × List (BranchCondition × Condition))
    (hremaining : PathCoherent schema inheritedBooleanCondition currentStart remaining)
    (hbest : PathCoherent schema inheritedBooleanCondition best.1 best.2)
    : let result := deepestExistingPrefixFrom tree remaining best
      PathCoherent schema inheritedBooleanCondition result.1 result.2 := by
  induction remaining generalizing currentStart best with
  | nil => simpa [deepestExistingPrefixFrom] using hbest
  | cons edge rest ih =>
      rcases edge with ⟨branch, next⟩
      simp only [deepestExistingPrefixFrom]
      split
      · exact ih next (next, rest) hremaining.2 hremaining.2
      · exact ih next best hremaining.2 hbest

theorem deepestExistingPrefix_coherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (start : Condition)
    (path : List (BranchCondition × Condition))
    (hpath : PathCoherent schema inheritedBooleanCondition start path)
    : let result := deepestExistingPrefix tree start path
      PathCoherent schema inheritedBooleanCondition result.1 result.2 := by
  unfold deepestExistingPrefix
  exact deepestExistingPrefixFrom_coherent schema inheritedBooleanCondition tree
    start path (start, path) hpath hpath

theorem branchesForPath_coherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (start : Condition) (path : List (BranchCondition × Condition))
    (fields : List NamedField)
    (hpath : PathCoherent schema inheritedBooleanCondition start path)
    : branchesCoherent schema inheritedBooleanCondition start
        (branchesForPath path fields) := by
  induction path generalizing start with
  | nil => simp [branchesForPath, branchesCoherent]
  | cons edge rest ih =>
      rcases edge with ⟨branch, next⟩
      cases rest with
      | nil =>
          simpa [branchesForPath, branchesCoherent, Tree.BranchesCoherent]
            using hpath.1
      | cons nextEdge tail =>
          have hbody := ih next hpath.2
          simpa [branchesForPath, branchesCoherent, Tree.BranchesCoherent] using
            And.intro hpath.1 (And.intro hbody True.intro)

theorem branchesCoherent_append
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (parent : Condition) (left right : List (Branch Tree))
    (hleft : branchesCoherent schema inheritedBooleanCondition parent left)
    (hright : branchesCoherent schema inheritedBooleanCondition parent right)
    : branchesCoherent schema inheritedBooleanCondition parent (left ++ right) := by
  induction left with
  | nil => simpa [branchesCoherent] using hright
  | cons branch rest ih =>
      rw [List.cons_append, branchesCoherent]
      rw [branchesCoherent] at hleft
      exact ⟨hleft.1, hleft.2.1, ih hleft.2.2⟩

mutual
  theorem Tree.modifyAtCondition?_branchesCoherent
      (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
      (target : Condition) (modify : Tree -> Tree)
      (tree modifiedTree : Tree)
      (htree : tree.BranchesCoherent schema inheritedBooleanCondition)
      (hmodify
        : ∀ node,
            node.condition = target
            -> node.BranchesCoherent schema inheritedBooleanCondition
            -> (modify node).BranchesCoherent schema inheritedBooleanCondition)
      (hmodifyCondition : ∀ node, (modify node).condition = node.condition)
      (hresult : tree.modifyAtCondition? target modify = some modifiedTree)
      : modifiedTree.condition = tree.condition
        ∧ modifiedTree.BranchesCoherent schema inheritedBooleanCondition := by
    rw [Tree.modifyAtCondition?] at hresult
    split at hresult
    · rename_i hequal
      cases hresult
      exact ⟨hmodifyCondition tree, hmodify tree hequal htree⟩
    · split at hresult
      · contradiction
      · rename_i modifiedBranches hbranches
        cases hresult
        rw [Tree.BranchesCoherent]
        exact ⟨rfl, modifyBranchesAtCondition?_coherent schema inheritedBooleanCondition
          target modify tree.branches modifiedBranches
          (by simpa [Tree.BranchesCoherent] using htree) hmodify
          hmodifyCondition hbranches⟩
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem modifyBranchesAtCondition?_coherent
      (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
      (target : Condition) (modify : Tree -> Tree)
      (branches modifiedBranches : List (Branch Tree))
      (hbranches : branchesCoherent schema inheritedBooleanCondition parent branches)
      (hmodify
        : ∀ node,
            node.condition = target
            -> node.BranchesCoherent schema inheritedBooleanCondition
            -> (modify node).BranchesCoherent schema inheritedBooleanCondition)
      (hmodifyCondition : ∀ node, (modify node).condition = node.condition)
      (hresult
        : modifyBranchesAtCondition? target modify branches = some modifiedBranches)
      : branchesCoherent schema inheritedBooleanCondition parent modifiedBranches := by
    cases branches with
    | nil => simp [modifyBranchesAtCondition?] at hresult
    | cons branch rest =>
        rw [branchesCoherent] at hbranches
        rw [modifyBranchesAtCondition?] at hresult
        split at hresult
        · rename_i modifiedBody hbody
          cases hresult
          rw [branchesCoherent]
          have hmodified :=
            Tree.modifyAtCondition?_branchesCoherent schema
              inheritedBooleanCondition target modify branch.body modifiedBody
              hbranches.2.1
              hmodify hmodifyCondition hbody
          exact ⟨by simpa [hmodified.1] using hbranches.1,
            hmodified.2,
            hbranches.2.2⟩
        · split at hresult
          · contradiction
          · rename_i modifiedRest hrest
            cases hresult
            rw [branchesCoherent]
            exact ⟨hbranches.1, hbranches.2.1,
              modifyBranchesAtCondition?_coherent schema
                inheritedBooleanCondition target modify rest modifiedRest
                hbranches.2.2 hmodify hmodifyCondition hrest⟩
  termination_by sizeOf branches
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega
end

theorem Tree.appendAtCondition?_branchesCoherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (target : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    (modifiedTree : Tree)
    (htree : tree.BranchesCoherent schema inheritedBooleanCondition)
    (hadded : branchesCoherent schema inheritedBooleanCondition target branches)
    (hresult : tree.appendAtCondition? target fields branches = some modifiedTree)
    : modifiedTree.BranchesCoherent schema inheritedBooleanCondition := by
  let modify : Tree -> Tree := fun node =>
    {
      node with
        fields := fields.foldl
          (fun groups field => addFieldToGroups field groups) node.fields
        branches := node.branches ++ branches
    }
  change tree.modifyAtCondition? target modify = some modifiedTree at hresult
  have hpreserved :=
    Tree.modifyAtCondition?_branchesCoherent schema inheritedBooleanCondition
      target modify tree modifiedTree htree (by
        intro node hcondition hnode
        rw [Tree.BranchesCoherent]
        apply branchesCoherent_append schema inheritedBooleanCondition
        · simpa [Tree.BranchesCoherent] using hnode
        · simpa [modify, hcondition] using hadded)
      (by intro node; rfl) hresult
  exact hpreserved.2

theorem finishInsert_branchesCoherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (start : Condition)
    (retainedPath : List (BranchCondition × Condition)) (field : NamedField)
    (htree : tree.BranchesCoherent schema inheritedBooleanCondition)
    (hpath : PathCoherent schema inheritedBooleanCondition start retainedPath)
    : Tree.BranchesCoherent schema inheritedBooleanCondition
        (let retainedPrefix := deepestExistingPrefix tree start retainedPath
          match retainedPrefix.2 with
          | [] =>
              match tree.appendAtCondition? retainedPrefix.1 [field] [] with
              | some modifiedTree => modifiedTree
              | none => tree
          | missingPath =>
              let simplePath := erasePathCycles missingPath
              match tree.appendAtCondition? retainedPrefix.1 []
                      (branchesForPath simplePath [field]) with
              | some modifiedTree => modifiedTree
              | none => tree) := by
  let retainedPrefix := deepestExistingPrefix tree start retainedPath
  have hretainedPrefix :
      PathCoherent schema inheritedBooleanCondition retainedPrefix.1
        retainedPrefix.2 :=
    deepestExistingPrefix_coherent schema inheritedBooleanCondition tree start
      retainedPath hpath
  cases hmissing : retainedPrefix.2 with
  | nil =>
      cases hfinal : tree.appendAtCondition? retainedPrefix.1 [field] [] with
      | none => simp [retainedPrefix, hmissing, hfinal, htree]
      | some finalTree =>
          simpa [retainedPrefix, hmissing, hfinal] using
            tree.appendAtCondition?_branchesCoherent schema
              inheritedBooleanCondition retainedPrefix.1 [field] [] finalTree htree
              (by simp [branchesCoherent]) hfinal
  | cons edge rest =>
      let simplePath := erasePathCycles (edge :: rest)
      have hsimplePath :
          PathCoherent schema inheritedBooleanCondition retainedPrefix.1
            simplePath := by
        apply erasePathCycles_coherent
        simpa [hmissing] using hretainedPrefix
      let addedBranches := branchesForPath simplePath [field]
      have hadded :
          branchesCoherent schema inheritedBooleanCondition retainedPrefix.1
            addedBranches :=
        branchesForPath_coherent schema inheritedBooleanCondition retainedPrefix.1
          simplePath [field] hsimplePath
      cases hfinal : tree.appendAtCondition? retainedPrefix.1 [] addedBranches with
      | none =>
          simp [retainedPrefix, hmissing, simplePath, addedBranches, hfinal, htree]
      | some finalTree =>
          simpa [retainedPrefix, hmissing, simplePath, addedBranches, hfinal] using
            tree.appendAtCondition?_branchesCoherent schema
              inheritedBooleanCondition retainedPrefix.1 [] addedBranches finalTree
              htree hadded hfinal

theorem Tree.insertField_branchesCoherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (sourcePath : List BranchCondition)
    (target : Condition) (field : NamedField)
    (htree : tree.BranchesCoherent schema inheritedBooleanCondition)
    : Tree.BranchesCoherent schema inheritedBooleanCondition
        (tree.insertField schema inheritedBooleanCondition sourcePath target field) := by
  rw [Tree.insertField]
  cases happend : tree.appendAtCondition? target [field] [] with
  | some modifiedTree =>
      exact tree.appendAtCondition?_branchesCoherent schema
        inheritedBooleanCondition target [field] [] modifiedTree htree
        (by simp [branchesCoherent]) happend
  | none =>
      cases hsource
            : pathForBranches? schema inheritedBooleanCondition tree.condition
                sourcePath with
      | none => simp [htree]
      | some sourcePathWithConditions =>
          simp only
          let sourcePrefix :=
            deepestExistingPrefix tree tree.condition sourcePathWithConditions
          have hsourcePath :=
            pathForBranches?_coherent schema inheritedBooleanCondition tree.condition
              sourcePath sourcePathWithConditions hsource
          have hsourcePrefix :
              PathCoherent schema inheritedBooleanCondition sourcePrefix.1
                sourcePrefix.2 :=
            deepestExistingPrefix_coherent schema inheritedBooleanCondition tree
              tree.condition sourcePathWithConditions hsourcePath
          let shrunk :=
            shrinkBranches schema inheritedBooleanCondition sourcePrefix.1 target
              (sourcePrefix.2.map Prod.fst)
          let retainedPath :=
            match pathForBranches? schema inheritedBooleanCondition sourcePrefix.1
                shrunk with
            | some path =>
                if pathEnd sourcePrefix.1 path = target then path else sourcePrefix.2
            | none => sourcePrefix.2
          have hretained :
              PathCoherent schema inheritedBooleanCondition sourcePrefix.1
                retainedPath := by
            cases hshrunk
                  : pathForBranches? schema inheritedBooleanCondition
                      sourcePrefix.1 shrunk with
            | none => simpa [retainedPath, hshrunk] using hsourcePrefix
            | some path =>
                by_cases hend : pathEnd sourcePrefix.1 path = target
                · simpa [retainedPath, hshrunk, hend] using
                    pathForBranches?_coherent schema inheritedBooleanCondition
                      sourcePrefix.1 shrunk path hshrunk
                · simpa [retainedPath, hshrunk, hend] using hsourcePrefix
          exact finishInsert_branchesCoherent schema inheritedBooleanCondition tree
            sourcePrefix.1 retainedPath field htree hretained

theorem insertSelections_branchesCoherent
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition) (branches : List BranchCondition)
    (tree : Tree) (selectionSet : List Selection)
    (htree : tree.BranchesCoherent schema inheritedBooleanCondition)
    : (insertSelections schema inheritedBooleanCondition currentCondition branches tree
        selectionSet).BranchesCoherent
        schema inheritedBooleanCondition := by
  cases selectionSet with
  | nil => simpa [insertSelections] using htree
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
          apply insertSelections_branchesCoherent schema inheritedBooleanCondition
            currentCondition branches treeAfterField rest
          unfold treeAfterField
          split
          · exact htree
          · split
            · exact htree
            · exact tree.insertField_branchesCoherent schema
                inheritedBooleanCondition (branches ++ ‹_›) ‹_› storedField htree
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
          apply insertSelections_branchesCoherent schema inheritedBooleanCondition
            currentCondition branches treeAfterFragment rest
          unfold treeAfterFragment
          split
          · exact htree
          · split
            · exact htree
            · exact insertSelections_branchesCoherent schema
                inheritedBooleanCondition ‹_› (branches ++ ‹_›) tree
                childSelectionSet htree
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem ofSelectionSetInScope_branchesCoherent
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : Tree.BranchesCoherent schema inheritedBooleanCondition
        (ofSelectionSetInScope schema parentType inheritedBooleanCondition
          selectionSet) := by
  unfold ofSelectionSetInScope
  apply insertSelections_branchesCoherent
  simp [Tree.BranchesCoherent, Tree.root, branchesCoherent]

end ConditionTree
end GraphQL
