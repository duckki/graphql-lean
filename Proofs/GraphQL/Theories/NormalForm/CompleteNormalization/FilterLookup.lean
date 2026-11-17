import Proofs.GraphQL.Theories.NormalForm.Shared.DeclaredLookup
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterMerge

/-! Recursive declared lookup is preserved even when Boolean filtering empties a body. -/

namespace GraphQL.NormalForm.CompleteNormalization

theorem selectionSetDeclaredLookupReady_filter (schema : Schema) (boolCase : BoolCase)
    : ∀ parentType selectionSet,
        selectionSetDeclaredLookupReady schema parentType selectionSet
        -> selectionSetDeclaredLookupReady schema parentType
            (filterSelectionSetBoolCase boolCase selectionSet)
  | parentType, [], _ => by
      simp [filterSelectionSetBoolCase, selectionSetDeclaredLookupReady]
  | parentType, selection :: rest, hready => by
      unfold selectionSetDeclaredLookupReady at hready
      have hhead := hready selection (by simp)
      have htail : selectionSetDeclaredLookupReady schema parentType rest := by
        unfold selectionSetDeclaredLookupReady
        exact fun candidate hcandidate => hready candidate (by simp [hcandidate])
      have hrest := selectionSetDeclaredLookupReady_filter schema boolCase parentType rest htail
      rw [filterSelectionSetBoolCase_cons]
      apply selectionSetDeclaredLookupReady_append (hright := hrest)
      cases selection with
      | field responseName fieldName arguments directives children =>
          simp only [selectionDeclaredLookupReady] at hhead
          rcases hhead with ⟨definition, hlookup, hchildren⟩
          have hfiltered := selectionSetDeclaredLookupReady_filter schema boolCase
            definition.outputType.namedType children hchildren
          by_cases hallow : directivesAllowIn boolCase directives = true
          · cases children with
            | nil =>
                simp [filterSelectionSetBoolCase, hallow, selectionSetDeclaredLookupReady,
                  selectionDeclaredLookupReady, hlookup]
            | cons child children =>
                cases hfilter : filterSelectionSetBoolCase boolCase (child :: children) with
                | nil =>
                    simp [filterSelectionSetBoolCase, hallow, hfilter,
                      selectionSetDeclaredLookupReady, selectionDeclaredLookupReady, hlookup]
                | cons filtered filteredRest =>
                    simp only [hfilter] at hfiltered
                    simpa [filterSelectionSetBoolCase, hallow, hfilter,
                      selectionSetDeclaredLookupReady, selectionDeclaredLookupReady, hlookup]
                      using hfiltered
          · have hfalse : directivesAllowIn boolCase directives = false := by
              cases h : directivesAllowIn boolCase directives <;> simp_all
            simp [filterSelectionSetBoolCase, hfalse, selectionSetDeclaredLookupReady]
      | inlineFragment condition directives children =>
          cases condition <;> simp only [selectionDeclaredLookupReady] at hhead
          all_goals
            have hfiltered := selectionSetDeclaredLookupReady_filter schema boolCase _ children hhead
            by_cases hallow : directivesAllowIn boolCase directives = true
            · cases hfilter : filterSelectionSetBoolCase boolCase children with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hfilter,
                    selectionSetDeclaredLookupReady]
              | cons filtered filteredRest =>
                  simp only [hfilter] at hfiltered
                  simpa [filterSelectionSetBoolCase, hallow, hfilter,
                    selectionSetDeclaredLookupReady, selectionDeclaredLookupReady] using hfiltered
            · have hfalse : directivesAllowIn boolCase directives = false := by
                cases h : directivesAllowIn boolCase directives <;> simp_all
              simp [filterSelectionSetBoolCase, hfalse, selectionSetDeclaredLookupReady]

end GraphQL.NormalForm.CompleteNormalization
