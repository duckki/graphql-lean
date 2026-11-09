import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.TypenameFree

namespace GraphQL.NormalForm.CompleteNormalization

theorem filterSelectionSetBoolCase_typenameFree (boolCase : BoolCase)
    : ∀ selections,
        selectionSetTypenameFree selections
        -> selectionSetTypenameFree (filterSelectionSetBoolCase boolCase selections)
  | [], _ => by simpa [filterSelectionSetBoolCase] using selectionSetTypenameFree_nil
  | selection :: rest, hfree => by
      have hrest := filterSelectionSetBoolCase_typenameFree boolCase rest
        (selectionSetTypenameFree_tail hfree)
      have hhead := selectionSetTypenameFree_head hfree
      cases selection with
      | field responseName fieldName arguments directives children =>
          rw [selectionTypenameFree] at hhead
          have hchildren := filterSelectionSetBoolCase_typenameFree boolCase children hhead.2
          by_cases hallow : directivesAllowIn boolCase directives = true
          · cases children with
            | nil =>
                simpa only [filterSelectionSetBoolCase, hallow, Bool.true_eq, ↓reduceIte] using
                  (selectionSetTypenameFree_cons
                    (by rw [selectionTypenameFree]; exact ⟨hhead.1, selectionSetTypenameFree_nil⟩) hrest)
            | cons child children =>
                cases hfiltered : filterSelectionSetBoolCase boolCase (child :: children) with
                | nil =>
                    simpa only [filterSelectionSetBoolCase, hallow, Bool.true_eq, ↓reduceIte, hfiltered] using
                      (selectionSetTypenameFree_cons
                        (by rw [selectionTypenameFree]; exact ⟨hhead.1, selectionSetTypenameFree_nil⟩) hrest)
                | cons filteredChild filteredChildren =>
                    simpa only [filterSelectionSetBoolCase, hallow, Bool.true_eq, ↓reduceIte, hfiltered] using
                      (selectionSetTypenameFree_cons
                        (by rw [selectionTypenameFree]; exact ⟨hhead.1, by simpa only [hfiltered] using hchildren⟩) hrest)
          · simpa [filterSelectionSetBoolCase, hallow] using hrest
      | inlineFragment condition directives children =>
          rw [selectionTypenameFree] at hhead
          have hchildren := filterSelectionSetBoolCase_typenameFree boolCase children hhead
          by_cases hallow : directivesAllowIn boolCase directives = true
          · cases hfiltered : filterSelectionSetBoolCase boolCase children with
            | nil => simpa [filterSelectionSetBoolCase, hallow, hfiltered] using hrest
            | cons child children =>
                simpa only [filterSelectionSetBoolCase, hallow, Bool.true_eq, ↓reduceIte, hfiltered] using
                  (selectionSetTypenameFree_cons
                    (by simpa only [selectionTypenameFree, hfiltered] using hchildren) hrest)
          · simpa [filterSelectionSetBoolCase, hallow] using hrest
termination_by selections => SelectionSet.size selections
decreasing_by
  all_goals
    first
    | cases selection <;> simp [SelectionSet.size, Selection.size] <;> omega
    | rename_i heq; cases heq; simp [SelectionSet.size, Selection.size]; omega
    | rename_i heq; cases heq; simp [SelectionSet.size, Selection.size]; omega

theorem completeNormalBooleanStem_body_typenameFree
    : ∀ {boolCase : BoolCase} {selection : Selection} {body : List Selection},
        completeNormalBooleanStem boolCase selection body
        -> selectionTypenameFree selection
        -> selectionSetTypenameFree body
  | [], _selection, _body, hstem, _hfree => by
      simp [completeNormalBooleanStem] at hstem
  | [(varName, value)],
      .inlineFragment none [directive] selectionSet, body, hstem, hfree => by
      rcases hstem with ⟨hdirective, hbody⟩
      subst directive
      subst selectionSet
      simpa only [selectionTypenameFree] using hfree
  | (varName, value) :: (nextVar, nextValue) :: rest,
      .inlineFragment none [directive] [child], body, hstem, hfree => by
      rcases hstem with ⟨hdirective, hchildStem⟩
      subst directive
      rw [selectionTypenameFree] at hfree
      exact completeNormalBooleanStem_body_typenameFree hchildStem
        (selectionSetTypenameFree_head hfree)
  | _ :: _ :: _, .field _ _ _ _ _, _body, hstem, _hfree => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none [] _, _body, hstem, _hfree => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none (_ :: _ :: _) _, _body, hstem,
      _hfree => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment (some _) _ _, _body, hstem, _hfree => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .field _ _ _ _ _, _body, hstem, _hfree => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none [] _, _body, hstem, _hfree => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none (_ :: _ :: _) _, _body, hstem, _hfree => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment (some _) _ _, _body, hstem, _hfree => by
      simp [completeNormalBooleanStem] at hstem

theorem wrapWithBoolCase_typenameFree (boolCase : BoolCase) {selections : List Selection}
    (hfree : selectionSetTypenameFree selections)
    : selectionSetTypenameFree (wrapWithBoolCase boolCase selections) := by
  induction boolCase with
  | nil => simpa [wrapWithBoolCase] using hfree
  | cons bit rest ih =>
      simpa only [wrapWithBoolCase] using selectionSetTypenameFree_fragment ih

theorem completeNormalizeRootSelectionSet_typenameFree (schema : Schema)
    (variables : List BoolVar) (parentType : Name) {selections : List Selection}
    (hfree : selectionSetTypenameFree selections)
    : selectionSetTypenameFree
        (completeNormalizeRootSelectionSet schema variables parentType selections) := by
  unfold selectionSetTypenameFree
  intro selection hmem
  simp only [completeNormalizeRootSelectionSet, List.mem_flatten, List.mem_map] at hmem
  rcases hmem with ⟨wrapped, ⟨boolCase, _, rfl⟩, hmem⟩
  have hnormalized := GroundTypeNormalization.normalizeSelectionSet_typenameFree schema parentType
    (filterSelectionSetBoolCase boolCase selections)
    (filterSelectionSetBoolCase_typenameFree boolCase selections hfree)
  cases hnormal
        : normalizeSelectionSet schema parentType
            (filterSelectionSetBoolCase boolCase selections) with
  | nil => simp [hnormal] at hmem
  | cons head tail =>
      have hwrapped := wrapWithBoolCase_typenameFree boolCase
        (by simpa only [hnormal] using hnormalized)
      unfold selectionSetTypenameFree at hwrapped
      exact hwrapped selection (by simpa only [hnormal] using hmem)

theorem completeNormalizeOperation_typenameFree (schema : Schema) (operation : Operation)
    (hfree : operationTypenameFree operation)
    : operationTypenameFree (completeNormalizeOperation schema operation) := by
  exact completeNormalizeRootSelectionSet_typenameFree schema _ _ hfree

end GraphQL.NormalForm.CompleteNormalization
