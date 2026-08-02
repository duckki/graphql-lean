import GraphQL.Theories.NormalForm
import Proofs.GraphQL.Argument

/-!
Equivalence-relation algebra for selection equality up to sibling reordering.
-/

namespace GraphQL

namespace NormalForm

/-- Selection-set equality up to reordering is symmetric. -/
theorem SelectionSetEqualUpToReordering.symm
    {left right : List Selection}
    (hequal : SelectionSetEqualUpToReordering left right)
    : SelectionSetEqualUpToReordering right left := by
  refine SelectionSetEqualUpToReordering.rec
    (motive_1 := fun left right _hequal =>
      SelectionEqualUpToReordering right left)
    (motive_2 := fun left right _hequal =>
      SelectionSetEqualUpToReordering right left)
    ?_ ?_ ?_ hequal
  · intro responseName fieldName leftArguments rightArguments directives
      leftSelectionSet rightSelectionSet harguments _hchildren ih
    exact .field responseName fieldName directives
      (Argument.argumentsEquivalent_symm harguments) ih
  · intro typeCondition directives leftSelectionSet rightSelectionSet
      _hchildren ih
    exact .inlineFragment typeCondition directives ih
  · intro left right pairs hleft hright _hrelations ih
    refine .paired (pairs.map fun pair => (pair.2, pair.1)) ?_ ?_ ?_
    · simpa [List.map_map, Function.comp_def] using hright
    · simpa [List.map_map, Function.comp_def] using hleft
    · intro pair hpair
      rcases List.mem_map.mp hpair with ⟨source, hsource, rfl⟩
      exact ih source hsource

private theorem perm_map_fst_align {α β : Type}
    : ∀ (middle : List α) (pairs : List (α × β)),
        middle.Perm (pairs.map Prod.fst)
        → ∃ aligned : List (α × β), aligned.Perm pairs ∧ aligned.map Prod.fst = middle
  | [], pairs, hperm => by
      have hlength := hperm.length_eq
      have hpairs : pairs = [] := by
        apply List.length_eq_zero_iff.mp
        simpa using hlength.symm
      subst pairs
      exact ⟨[], List.Perm.nil, rfl⟩
  | head :: tail, pairs, hperm => by
      have hheadMap : head ∈ pairs.map Prod.fst :=
        hperm.mem_iff.mp (by simp)
      rcases List.mem_map.mp hheadMap with ⟨pair, hpair, hpairHead⟩
      rcases List.mem_iff_append.mp hpair with ⟨before, after, hpairs⟩
      subst pairs
      have hmapReorder :
          ((before ++ pair :: after).map Prod.fst).Perm
            (head :: (before ++ after).map Prod.fst) := by
        have hleftEq :
            (before ++ pair :: after).map Prod.fst =
              (before.map Prod.fst ++ [head]) ++ after.map Prod.fst := by
          simp [List.map_append, hpairHead, List.append_assoc]
        have hrightEq :
            ([head] ++ before.map Prod.fst) ++ after.map Prod.fst =
              head :: (before ++ after).map Prod.fst := by
          simp [List.map_append]
        exact (List.Perm.of_eq hleftEq).trans
          (((List.perm_append_comm
            (l₁ := before.map Prod.fst) (l₂ := [head])).append_right
              (after.map Prod.fst)).trans (List.Perm.of_eq hrightEq))
      have htailPerm : tail.Perm ((before ++ after).map Prod.fst) :=
        List.Perm.cons_inv (hperm.trans hmapReorder)
      rcases perm_map_fst_align tail (before ++ after) htailPerm with
        ⟨alignedRest, halignedRest, hrestMap⟩
      let aligned := pair :: alignedRest
      have hmovePair :
          (pair :: before ++ after).Perm (before ++ pair :: after) := by
        simpa [List.append_assoc] using
          ((List.perm_append_comm (l₁ := before) (l₂ := [pair])).append_right
            after).symm
      refine ⟨aligned, ?_, ?_⟩
      · exact (halignedRest.cons pair).trans hmovePair
      · simp [aligned, hpairHead, hrestMap]

/-- Reorder selection pairs so their first projections equal a permutation target. -/
theorem selectionPairs_align_fst
    (middle : List Selection) (pairs : List (Selection × Selection))
    (hperm : middle.Perm (pairs.map Prod.fst))
    : ∃ aligned : List (Selection × Selection),
        aligned.Perm pairs ∧ aligned.map Prod.fst = middle :=
  perm_map_fst_align middle pairs hperm

private theorem compose_aligned_selection_pairs
    (middle : List Selection)
    (htrans
      : ∀ left middleSelection right,
          middleSelection ∈ middle
          → SelectionEqualUpToReordering left middleSelection
          → SelectionEqualUpToReordering middleSelection right
          → SelectionEqualUpToReordering left right)
    : ∀ (firstPairs secondPairs : List (Selection × Selection)),
        firstPairs.map Prod.snd = secondPairs.map Prod.fst
        → (∀ pair, pair ∈ firstPairs → SelectionEqualUpToReordering pair.1 pair.2)
        → (∀ pair, pair ∈ secondPairs → SelectionEqualUpToReordering pair.1 pair.2)
        → (∀ middleSelection,
            middleSelection ∈ firstPairs.map Prod.snd → middleSelection ∈ middle)
        → ∃ outputPairs : List (Selection × Selection),
            outputPairs.map Prod.fst = firstPairs.map Prod.fst
            ∧ outputPairs.map Prod.snd = secondPairs.map Prod.snd
            ∧ ∀ pair, pair ∈ outputPairs → SelectionEqualUpToReordering pair.1 pair.2
  | [], [], _hmaps, _hfirst, _hsecond, _hmiddle =>
      ⟨[], rfl, rfl, by intro pair hpair; simp at hpair⟩
  | first :: firstRest, second :: secondRest, hmaps,
      hfirst, hsecond, hmiddle => by
      have hheads : first.2 = second.1 :=
        List.cons.inj (by simpa using hmaps) |>.1
      have htails : firstRest.map Prod.snd = secondRest.map Prod.fst :=
        List.cons.inj (by simpa using hmaps) |>.2
      have hfirstHead := hfirst first List.mem_cons_self
      have hsecondHead := hsecond second List.mem_cons_self
      have hfirstRest : ∀ pair, pair ∈ firstRest →
          SelectionEqualUpToReordering pair.1 pair.2 := by
        intro pair hpair
        exact hfirst pair (List.mem_cons_of_mem first hpair)
      have hsecondRest : ∀ pair, pair ∈ secondRest →
          SelectionEqualUpToReordering pair.1 pair.2 := by
        intro pair hpair
        exact hsecond pair (List.mem_cons_of_mem second hpair)
      have hmiddleHead : first.2 ∈ middle := hmiddle first.2 (by simp)
      have hmiddleRest : ∀ middleSelection,
          middleSelection ∈ firstRest.map Prod.snd →
          middleSelection ∈ middle := by
        intro middleSelection hmem
        exact hmiddle middleSelection (by simp [hmem])
      rcases compose_aligned_selection_pairs middle htrans firstRest secondRest
          htails hfirstRest hsecondRest hmiddleRest with
        ⟨outputRest, houtLeft, houtRight, houtRelations⟩
      let outputHead : Selection × Selection := (first.1, second.2)
      refine ⟨outputHead :: outputRest, ?_, ?_, ?_⟩
      · simp [outputHead, houtLeft]
      · simp [outputHead, houtRight]
      · intro pair hpair
        rcases List.mem_cons.mp hpair with hhead | hrest
        · subst pair
          apply htrans first.1 first.2 second.2 hmiddleHead hfirstHead
          simpa [hheads] using hsecondHead
        · exact houtRelations pair hrest
  | [], _ :: _, hmaps, _hfirst, _hsecond, _hmiddle => by
      simp at hmaps
  | _ :: _, [], hmaps, _hfirst, _hsecond, _hmiddle => by
      simp at hmaps

private theorem selectionSetEqualUpToReordering_trans_of_element_trans
    {left middle right : List Selection}
    (htrans
      : ∀ leftSelection middleSelection rightSelection,
          middleSelection ∈ middle
          → SelectionEqualUpToReordering leftSelection middleSelection
          → SelectionEqualUpToReordering middleSelection rightSelection
          → SelectionEqualUpToReordering leftSelection rightSelection)
    (hfirst : SelectionSetEqualUpToReordering left middle)
    (hsecond : SelectionSetEqualUpToReordering middle right)
    : SelectionSetEqualUpToReordering left right := by
  rcases hfirst with
    ⟨firstPairs, hfirstLeft, hfirstRight, hfirstRelations⟩
  rcases hsecond with
    ⟨secondPairs, hsecondLeft, hsecondRight, hsecondRelations⟩
  have hmaps : (firstPairs.map Prod.snd).Perm
      (secondPairs.map Prod.fst) := hfirstRight.trans hsecondLeft.symm
  rcases perm_map_fst_align (firstPairs.map Prod.snd) secondPairs hmaps with
    ⟨alignedSecond, halignedSecond, halignedMap⟩
  have halignedRelations : ∀ pair, pair ∈ alignedSecond →
      SelectionEqualUpToReordering pair.1 pair.2 := by
    intro pair hpair
    exact hsecondRelations pair (halignedSecond.mem_iff.mp hpair)
  have hmiddleMem : ∀ middleSelection,
      middleSelection ∈ firstPairs.map Prod.snd →
      middleSelection ∈ middle := by
    intro middleSelection hmem
    exact hfirstRight.mem_iff.mp hmem
  rcases compose_aligned_selection_pairs middle htrans firstPairs alignedSecond
      halignedMap.symm hfirstRelations halignedRelations hmiddleMem with
    ⟨outputPairs, houtLeft, houtRight, houtRelations⟩
  exact .paired outputPairs
    (houtLeft ▸ hfirstLeft)
    (by
      rw [houtRight]
      exact (halignedSecond.map Prod.snd).trans hsecondRight)
    houtRelations

private theorem selection_size_le_selectionSet_size_of_mem {selection : Selection}
    : ∀ {selectionSet : List Selection},
        selection ∈ selectionSet → selection.size ≤ SelectionSet.size selectionSet
  | [], hmem => by simp at hmem
  | head :: rest, hmem => by
      rcases List.mem_cons.mp hmem with hhead | hrest
      · subst head
        simp [SelectionSet.size]
      · have ih := selection_size_le_selectionSet_size_of_mem hrest
        simp [SelectionSet.size]
        omega

private abbrev ReorderingNode := Sum Selection (List Selection)

private def reorderingNodeComplexity : ReorderingNode → Nat
  | .inl selection => 2 * selection.size
  | .inr selectionSet => 2 * SelectionSet.size selectionSet + 1

private def ReorderingTransAt : ReorderingNode → Prop
  | .inl middle =>
      ∀ {left right},
        SelectionEqualUpToReordering left middle
        → SelectionEqualUpToReordering middle right
        → SelectionEqualUpToReordering left right
  | .inr middle =>
      ∀ {left right},
        SelectionSetEqualUpToReordering left middle
        → SelectionSetEqualUpToReordering middle right
        → SelectionSetEqualUpToReordering left right

private theorem reorderingTransAt (node : ReorderingNode) : ReorderingTransAt node := by
  cases node with
  | inl middle =>
      intro left right hfirst hsecond
      cases hfirst with
      | field responseName fieldName directives hargumentsFirst hchildFirst =>
          cases hsecond with
          | field _ _ _ hargumentsSecond hchildSecond =>
              exact .field responseName fieldName directives
                (Argument.argumentsEquivalent_trans
                  hargumentsFirst hargumentsSecond)
                (reorderingTransAt (.inr _) hchildFirst hchildSecond)
      | inlineFragment typeCondition directives hchildFirst =>
          cases hsecond with
          | inlineFragment _ _ hchildSecond =>
              exact .inlineFragment typeCondition directives
                (reorderingTransAt (.inr _) hchildFirst hchildSecond)
  | inr middle =>
      intro left right hfirst hsecond
      exact selectionSetEqualUpToReordering_trans_of_element_trans
        (fun leftSelection middleSelection rightSelection hmiddle hleft hright =>
          reorderingTransAt (.inl middleSelection) hleft hright)
        hfirst hsecond
termination_by reorderingNodeComplexity node
decreasing_by
  all_goals
    simp [reorderingNodeComplexity, Selection.size]
    first
    | omega
    | (have hle := selection_size_le_selectionSet_size_of_mem hmiddle
       omega)

/-- Selection-set equality up to reordering is transitive. -/
theorem SelectionSetEqualUpToReordering.trans
    {left middle right : List Selection}
    (hfirst : SelectionSetEqualUpToReordering left middle)
    (hsecond : SelectionSetEqualUpToReordering middle right)
    : SelectionSetEqualUpToReordering left right :=
  reorderingTransAt (.inr middle) hfirst hsecond

end NormalForm

end GraphQL
