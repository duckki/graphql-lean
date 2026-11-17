import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterMerge
import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness.Readiness

/-!
Semantic-readiness facts for Boolean case filtering.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

mutual
  theorem selectionLookupValid_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType sourceSelection filteredSelection,
          filteredSelection ∈ filterSelectionSetBoolCase boolCase [sourceSelection]
          -> selectionLookupValid schema parentType sourceSelection
          -> selectionLookupValid schema parentType filteredSelection
    | parentType,
      .field responseName fieldName arguments directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow] at hfiltered
              subst filteredSelection
              simpa [selectionLookupValid] using hlookupValid
          | cons child children =>
              cases hchild :
                  filterSelectionSetBoolCase boolCase (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchild]
                    at hfiltered
                  subst filteredSelection
                  simpa [selectionLookupValid] using hlookupValid
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hchild]
                    at hfiltered
                  subst filteredSelection
                  simpa [selectionLookupValid] using hlookupValid
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment none directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
              subst filteredSelection
              have hsourceChild :
                  selectionSetLookupValid schema parentType selectionSet := by
                simpa [selectionLookupValid] using hlookupValid
              have hfilteredChild :
                  selectionSetLookupValid schema parentType
                    (filteredChild :: filteredChildren) := by
                simpa [hchild] using
                  selectionSetLookupValid_filterSelectionSetBoolCase schema
                    boolCase parentType selectionSet hsourceChild
              simpa [selectionLookupValid] using hfilteredChild
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment (some typeCondition) directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
              subst filteredSelection
              have hsourceChild :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hlookupValid
              have hfilteredChild :
                  selectionSetLookupValid schema typeCondition
                    (filteredChild :: filteredChildren) := by
                simpa [hchild] using
                  selectionSetLookupValid_filterSelectionSetBoolCase schema
                    boolCase typeCondition selectionSet hsourceChild
              simpa [selectionLookupValid] using hfilteredChild
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered

  theorem selectionSetLookupValid_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType selectionSet,
          selectionSetLookupValid schema parentType selectionSet
          -> selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet)
    | parentType, [], _hlookupValid => by
        simp [filterSelectionSetBoolCase, selectionSetLookupValid]
    | parentType, selection :: rest, hlookupValid => by
        have hhead :
            selectionLookupValid schema parentType selection :=
          selectionSetLookupValid_head hlookupValid
        have htail :
            selectionSetLookupValid schema parentType rest :=
          selectionSetLookupValid_tail hlookupValid
        have hheadFiltered :
            selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase [selection]) := by
          unfold selectionSetLookupValid
          intro candidate hcandidate
          exact selectionLookupValid_filterSelectionSetBoolCase schema
            boolCase parentType selection candidate hcandidate hhead
        have hrestFiltered :
            selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase rest) :=
          selectionSetLookupValid_filterSelectionSetBoolCase schema
            boolCase parentType rest htail
        rw [filterSelectionSetBoolCase_cons]
        exact selectionSetLookupValid_append hheadFiltered hrestFiltered
end

mutual
  theorem selectionSemanticsReady_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType sourceSelection filteredSelection,
          filteredSelection ∈ filterSelectionSetBoolCase boolCase [sourceSelection]
          -> selectionSemanticsReady schema parentType sourceSelection
          -> selectionSemanticsReady schema parentType filteredSelection
    | parentType,
      .field responseName fieldName arguments directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow] at hfiltered
              subst filteredSelection
              simpa [selectionSemanticsReady] using hready
          | cons child children =>
              cases hchild :
                  filterSelectionSetBoolCase boolCase (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchild]
                    at hfiltered
                  subst filteredSelection
                  rcases (by
                    simpa [selectionSemanticsReady] using hready) with
                    ⟨fieldDefinition, hlookup, _hchildrenReady⟩
                  simp [selectionSemanticsReady]
                  exact ⟨fieldDefinition, hlookup, by
                    intro runtimeType _hincludes
                    exact selectionSetSemanticsReady_nil schema runtimeType⟩
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hchild]
                    at hfiltered
                  subst filteredSelection
                  rcases (by
                    simpa [selectionSemanticsReady] using hready) with
                    ⟨fieldDefinition, hlookup, hchildrenReady⟩
                  simp [selectionSemanticsReady]
                  refine ⟨fieldDefinition, hlookup, ?_⟩
                  intro runtimeType hincludes
                  have hsourceChildReady :
                      selectionSetSemanticsReady schema runtimeType
                        (child :: children) :=
                    hchildrenReady runtimeType hincludes
                  simpa [hchild] using
                    selectionSetSemanticsReady_filterSelectionSetBoolCase
                      schema boolCase runtimeType (child :: children)
                      hsourceChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment none directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
              subst filteredSelection
              have hsourceChildReady :
                  selectionSetSemanticsReady schema parentType selectionSet := by
                simpa [selectionSemanticsReady] using hready
              have hfilteredChildReady :
                  selectionSetSemanticsReady schema parentType
                    (filteredChild :: filteredChildren) := by
                simpa [hchild] using
                  selectionSetSemanticsReady_filterSelectionSetBoolCase
                    schema boolCase parentType selectionSet hsourceChildReady
              simpa [selectionSemanticsReady] using hfilteredChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment (some typeCondition) directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild] at hfiltered
              subst filteredSelection
              have hreadyParts :
                  selectionSetLookupValid schema typeCondition selectionSet
                    ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                      selectionSetSemanticsReady schema parentType
                        selectionSet) := by
                simpa [selectionSemanticsReady] using hready
              simp [selectionSemanticsReady]
              constructor
              · simpa [hchild] using
                  selectionSetLookupValid_filterSelectionSetBoolCase schema
                    boolCase typeCondition selectionSet hreadyParts.1
              · intro hoverlap
                have hsourceChildReady :
                    selectionSetSemanticsReady schema parentType selectionSet :=
                  hreadyParts.2 hoverlap
                simpa [hchild] using
                  selectionSetSemanticsReady_filterSelectionSetBoolCase
                    schema boolCase parentType selectionSet hsourceChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered

  theorem selectionSetSemanticsReady_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType selectionSet,
          selectionSetSemanticsReady schema parentType selectionSet
          -> selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet)
    | parentType, [], _hready => by
        simpa [filterSelectionSetBoolCase] using
          selectionSetSemanticsReady_nil schema parentType
    | parentType, selection :: rest, hready => by
        have hhead :
            selectionSemanticsReady schema parentType selection := by
          unfold selectionSetSemanticsReady at hready
          exact hready selection (by simp)
        have htailReady :
            selectionSetSemanticsReady schema parentType rest :=
          selectionSetSemanticsReady_tail hready
        have hheadFiltered :
            selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase [selection]) := by
          unfold selectionSetSemanticsReady
          intro candidate hcandidate
          exact selectionSemanticsReady_filterSelectionSetBoolCase schema
            boolCase parentType selection candidate hcandidate hhead
        have hrestFiltered :
            selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase rest) :=
          selectionSetSemanticsReady_filterSelectionSetBoolCase schema
            boolCase parentType rest htailReady
        rw [filterSelectionSetBoolCase_cons]
        exact selectionSetSemanticsReady_append hheadFiltered hrestFiltered
end

end CompleteNormalization

end NormalForm

end GraphQL
