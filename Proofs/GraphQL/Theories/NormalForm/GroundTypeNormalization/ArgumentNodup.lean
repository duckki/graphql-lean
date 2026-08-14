import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality

/-! Argument-name uniqueness preserved by ground-type normalization. -/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem selectionSetArgumentsNodup_append {left right : List Selection}
    : Execution.selectionSetArgumentsNodup left
      -> Execution.selectionSetArgumentsNodup right
      -> Execution.selectionSetArgumentsNodup (left ++ right) := by
  intro hleft hright
  induction left with
  | nil => exact hright
  | cons selection rest ih =>
      exact ⟨hleft.1, ih hleft.2⟩

theorem selectionSetArgumentsNodup_mergeSelectionSets
    : ∀ selections : List Selection,
        Execution.selectionSetArgumentsNodup selections
        -> Execution.selectionSetArgumentsNodup (mergeSelectionSets selections)
  | [], _hnodup => by simp [mergeSelectionSets, Execution.selectionSetArgumentsNodup]
  | selection :: rest, hnodup => by
      rcases hnodup with ⟨hselection, hrest⟩
      have hchildren :
          Execution.selectionSetArgumentsNodup selection.subselections := by
        cases selection with
        | field responseName fieldName arguments directives selectionSet =>
            exact hselection.2
        | inlineFragment typeCondition directives selectionSet =>
            exact hselection
      simpa [mergeSelectionSets] using
        selectionSetArgumentsNodup_append hchildren
          (selectionSetArgumentsNodup_mergeSelectionSets rest hrest)

theorem selectionSetArgumentsNodup_fieldSelectionsWithResponseNameInScope
    (schema : Schema) (parentType responseName : Name)
    : ∀ selectionSet,
        Execution.selectionSetArgumentsNodup selectionSet
        -> Execution.selectionSetArgumentsNodup
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet)
  | [], _hnodup => by
      simp [fieldSelectionsWithResponseNameInScope,
        Execution.selectionSetArgumentsNodup]
  | selection :: rest, hnodup => by
      rcases hnodup with ⟨hselection, hrest⟩
      cases selection with
      | field fieldResponseName fieldName arguments directives children =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, hname,
              Execution.selectionSetArgumentsNodup, hselection,
              selectionSetArgumentsNodup_fieldSelectionsWithResponseNameInScope
                schema parentType responseName rest hrest]
          · have hnameFalse : (fieldResponseName == responseName) = false := by
              cases h : fieldResponseName == responseName <;> simp_all
            simp [fieldSelectionsWithResponseNameInScope, hnameFalse,
              selectionSetArgumentsNodup_fieldSelectionsWithResponseNameInScope
                schema parentType responseName rest hrest]
      | inlineFragment typeCondition directives children =>
          have hchildren : Execution.selectionSetArgumentsNodup children := by
            simpa [Execution.selectionArgumentsNodup] using hselection
          cases typeCondition with
          | none =>
              simpa [fieldSelectionsWithResponseNameInScope] using
                selectionSetArgumentsNodup_append
                  (selectionSetArgumentsNodup_fieldSelectionsWithResponseNameInScope
                    schema parentType responseName children hchildren)
                  (selectionSetArgumentsNodup_fieldSelectionsWithResponseNameInScope
                    schema parentType responseName rest hrest)
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · simpa [fieldSelectionsWithResponseNameInScope, hoverlap] using
                  selectionSetArgumentsNodup_append
                    (selectionSetArgumentsNodup_fieldSelectionsWithResponseNameInScope
                      schema parentType responseName children hchildren)
                    (selectionSetArgumentsNodup_fieldSelectionsWithResponseNameInScope
                      schema parentType responseName rest hrest)
              · have hoverlapFalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases h : schema.typesOverlapBool parentType typeCondition <;>
                    simp_all
                simp [fieldSelectionsWithResponseNameInScope, hoverlapFalse,
                  selectionSetArgumentsNodup_fieldSelectionsWithResponseNameInScope
                    schema parentType responseName rest hrest]

theorem selectionSetArgumentsNodup_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName : Name)
    : ∀ selectionSet,
        Execution.selectionSetArgumentsNodup selectionSet
        -> Execution.selectionSetArgumentsNodup
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | [], _hnodup => by
      simp [withoutFieldSelectionsWithResponseName,
        Execution.selectionSetArgumentsNodup]
  | selection :: rest, hnodup => by
      rcases hnodup with ⟨hselection, hrest⟩
      cases selection with
      | field fieldResponseName fieldName arguments directives children =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname,
              selectionSetArgumentsNodup_withoutFieldSelectionsWithResponseName
                schema responseName rest hrest]
          · have hnameFalse : (fieldResponseName == responseName) = false := by
              cases h : fieldResponseName == responseName <;> simp_all
            simp [withoutFieldSelectionsWithResponseName, hnameFalse,
              Execution.selectionSetArgumentsNodup, hselection,
              selectionSetArgumentsNodup_withoutFieldSelectionsWithResponseName
                schema responseName rest hrest]
      | inlineFragment typeCondition directives children =>
          have hchildren : Execution.selectionSetArgumentsNodup children := by
            simpa [Execution.selectionArgumentsNodup] using hselection
          simp only [withoutFieldSelectionsWithResponseName,
            Execution.selectionSetArgumentsNodup]
          exact
            ⟨by
              simpa [Execution.selectionArgumentsNodup] using
                selectionSetArgumentsNodup_withoutFieldSelectionsWithResponseName
                  schema responseName children hchildren,
              selectionSetArgumentsNodup_withoutFieldSelectionsWithResponseName
                schema responseName rest hrest⟩

theorem selectionSetArgumentsNodup_possibleTypeNormalizations
    (schema : Schema)
    (possibleTypes : List Name) {selectionSet : List Selection}
    : (∀ objectType,
        objectType ∈ possibleTypes
        -> Execution.selectionSetArgumentsNodup
            (normalizeSelectionSet schema objectType selectionSet))
      -> Execution.selectionSetArgumentsNodup
          (possibleTypeNormalizations schema possibleTypes selectionSet) := by
  intro hnormalize
  induction possibleTypes with
  | nil =>
      simp [possibleTypeNormalizations,
        Execution.selectionSetArgumentsNodup]
  | cons objectType rest ih =>
      cases hnormalized : normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simp [possibleTypeNormalizations, hnormalized]
          exact ih (fun candidate hcandidate =>
            hnormalize candidate (List.mem_cons_of_mem objectType hcandidate))
      | cons selection restSelection =>
          have hhead :
              Execution.selectionSetArgumentsNodup
                (selection :: restSelection) := by
            simpa [hnormalized] using hnormalize objectType (by simp)
          simp [possibleTypeNormalizations, hnormalized,
            Execution.selectionSetArgumentsNodup,
            Execution.selectionArgumentsNodup]
          exact ⟨hhead, ih (fun candidate hcandidate =>
            hnormalize candidate
              (List.mem_cons_of_mem objectType hcandidate))⟩

theorem normalizeSelectionSet_argumentsNodup (schema : Schema)
    : ∀ parentType selectionSet,
        Execution.selectionSetArgumentsNodup selectionSet
        -> Execution.selectionSetArgumentsNodup
            (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro hnodup
      simp [normalizeSelectionSet,
        Execution.selectionSetArgumentsNodup]
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      intro hnodup
      have hfilteredRest :
          Execution.selectionSetArgumentsNodup
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetArgumentsNodup_withoutFieldSelectionsWithResponseName
          schema responseName rest hnodup.2
      simpa [normalizeSelectionSet, hlookup] using hrest hfilteredRest
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro hnodup
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have hselection := hnodup.1
      have hrestNodup := hnodup.2
      have hfilteredRest :
          Execution.selectionSetArgumentsNodup
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetArgumentsNodup_withoutFieldSelectionsWithResponseName
          schema responseName rest hrestNodup
      have hnormalizedRest :
          Execution.selectionSetArgumentsNodup
            (normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest)) :=
        hrest hfilteredRest
      have hmatching : Execution.selectionSetArgumentsNodup matching := by
        subst matching
        exact selectionSetArgumentsNodup_fieldSelectionsWithResponseNameInScope
          schema parentType responseName rest hrestNodup
      have hmergedSubselections :
          Execution.selectionSetArgumentsNodup mergedSubselections := by
        subst mergedSubselections
        exact selectionSetArgumentsNodup_append hselection.2
          (selectionSetArgumentsNodup_mergeSelectionSets matching hmatching)
      have hnormalizedSubselections :
          Execution.selectionSetArgumentsNodup normalizedSubselections := by
        dsimp [normalizedSubselections]
        by_cases hobject : objectTypeNameBool schema returnType = true
        · simp [hobject]
          exact hmerged hmergedSubselections
        · have hfalse : objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType <;> simp_all
          simp [hfalse]
          exact selectionSetArgumentsNodup_possibleTypeNormalizations
            schema (schema.getPossibleTypes returnType)
            (fun objectType _hobjectType =>
              hpossible objectType hmergedSubselections)
      rw [normalizeSelectionSet.eq_2, hlookup]
      change Execution.selectionSetArgumentsNodup
        (normalizedFieldWithRest schema returnType responseName fieldName
          arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)))
      exact ⟨⟨hselection.1, hnormalizedSubselections⟩, hnormalizedRest⟩
  | case4 parentType rest directives selectionSet happend =>
      intro hnodup
      have happendNodup :
          Execution.selectionSetArgumentsNodup (selectionSet ++ rest) :=
        selectionSetArgumentsNodup_append hnodup.1 hnodup.2
      simpa [normalizeSelectionSet] using happend happendNodup
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      _hrest happend =>
      intro hnodup
      have happendNodup :
          Execution.selectionSetArgumentsNodup (selectionSet ++ rest) :=
        selectionSetArgumentsNodup_append hnodup.1 hnodup.2
      simpa [normalizeSelectionSet, hoverlap] using happend happendNodup
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      intro hnodup
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition <;>
          simp_all
      simpa [normalizeSelectionSet, hfalse] using hrest hnodup.2

theorem normalizeOperation_selectionSetArgumentsNodup
    (schema : Schema) (operation : Operation)
    : Execution.selectionSetArgumentsNodup operation.selectionSet
      -> Execution.selectionSetArgumentsNodup
          (normalizeOperation schema operation).selectionSet := by
  intro hnodup
  simpa [normalizeOperation] using
    normalizeSelectionSet_argumentsNodup schema (operation.rootType schema)
      operation.selectionSet hnodup

end GroundTypeNormalization

end NormalForm

end GraphQL
