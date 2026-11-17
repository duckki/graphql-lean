import Proofs.GraphQL.Theories.NormalForm.Shared.TypenameFree
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality

namespace GraphQL.NormalForm.GroundTypeNormalization

theorem selectionSetTypenameFree_possibleTypeNormalizations
    (schema : Schema)
    (possibleTypes : List Name) {selectionSet : List Selection}
    : (∀ objectType,
        objectType ∈ possibleTypes
        -> selectionSetTypenameFree
            (normalizeSelectionSet schema objectType selectionSet))
      -> selectionSetTypenameFree
          (possibleTypeNormalizations schema possibleTypes selectionSet) := by
  intro hnormalize
  induction possibleTypes with
  | nil =>
      exact selectionSetTypenameFree_nil
  | cons objectType rest ih =>
      cases hnormalized : normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simp [possibleTypeNormalizations, hnormalized]
          exact ih (fun candidate hcandidate =>
            hnormalize candidate
              (List.mem_cons_of_mem objectType hcandidate))
      | cons selection restSelection =>
          have hheadFree :
              selectionSetTypenameFree (selection :: restSelection) := by
            simpa [hnormalized] using hnormalize objectType (by simp)
          simp [possibleTypeNormalizations, hnormalized]
          exact selectionSetTypenameFree_cons
            (by simpa only [selectionTypenameFree] using hheadFree)
            (ih
              (fun candidate hcandidate =>
                hnormalize candidate (List.mem_cons_of_mem objectType hcandidate)))

theorem normalizeSelectionSet_typenameFree (schema : Schema)
    : ∀ parentType selectionSet,
        selectionSetTypenameFree selectionSet
        -> selectionSetTypenameFree
            (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro hfree
      simpa [normalizeSelectionSet] using selectionSetTypenameFree_nil
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      intro hfree
      have hrestFree :=
        selectionSetTypenameFree_tail hfree
      have hfilteredRestFree :
          selectionSetTypenameFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_typenameFree schema responseName rest hrestFree
      simpa [normalizeSelectionSet, hlookup] using hrest hfilteredRestFree
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro hfree
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have hselectionFree :=
        selectionSetTypenameFree_head hfree
      have hrestFree :=
        selectionSetTypenameFree_tail hfree
      rw [selectionTypenameFree] at hselectionFree
      have hname : fieldName ≠ "__typename" := hselectionFree.1
      have hsubselectionsFree : selectionSetTypenameFree selectionSet :=
        hselectionFree.2
      have hfilteredRestFree :
          selectionSetTypenameFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_typenameFree schema responseName rest hrestFree
      have hnormalizedRest :
          selectionSetTypenameFree
            (normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest)) :=
        hrest hfilteredRestFree
      have hmatchingFree : selectionSetTypenameFree matching := by
        subst matching
        exact fieldSelectionsWithResponseNameInScope_typenameFree schema parentType
          responseName rest hrestFree
      have hmergedSubselectionsFree :
          selectionSetTypenameFree mergedSubselections := by
        subst mergedSubselections
        exact selectionSetTypenameFree_append hsubselectionsFree
          (selectionSetTypenameFree_mergeSelectionSets hmatchingFree)
      have hnormalizedSubselections :
          selectionSetTypenameFree
            (if objectTypeNameBool schema returnType then
              normalizeSelectionSet schema returnType mergedSubselections
            else
              possibleTypeNormalizations schema
                (schema.getPossibleTypes returnType)
                mergedSubselections) := by
        by_cases hobject : objectTypeNameBool schema returnType = true
        · simp [hobject]
          exact hmerged hmergedSubselectionsFree
        · have hfalse : objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hfalse]
          exact selectionSetTypenameFree_possibleTypeNormalizations
            schema (schema.getPossibleTypes returnType)
            (fun objectType _hobjectType =>
              hpossible objectType hmergedSubselectionsFree)
      have hnormalizedField :
          selectionTypenameFree
            (Selection.field responseName fieldName arguments directives
              normalizedSubselections) := by
        simpa only [selectionTypenameFree] using And.intro hname hnormalizedSubselections
      rw [normalizeSelectionSet.eq_2, hlookup]
      change selectionSetTypenameFree
        (normalizedFieldWithRest schema returnType responseName fieldName
          arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)))
      simpa only [normalizedFieldWithRest, normalizedField]
        using selectionSetTypenameFree_cons hnormalizedField hnormalizedRest
  | case4 parentType rest directives selectionSet happend =>
      intro hfree
      have hselectionFree :=
        selectionSetTypenameFree_head hfree
      have hrestFree :=
        selectionSetTypenameFree_tail hfree
      rw [selectionTypenameFree] at hselectionFree
      have happendFree :
          selectionSetTypenameFree (selectionSet ++ rest) :=
        selectionSetTypenameFree_append hselectionFree hrestFree
      simpa [normalizeSelectionSet] using happend happendFree
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      _hrest happend =>
      intro hfree
      have hselectionFree :=
        selectionSetTypenameFree_head hfree
      have hrestFree :=
        selectionSetTypenameFree_tail hfree
      rw [selectionTypenameFree] at hselectionFree
      have happendFree :
          selectionSetTypenameFree (selectionSet ++ rest) :=
        selectionSetTypenameFree_append hselectionFree hrestFree
      simpa [normalizeSelectionSet, hoverlap] using happend happendFree
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      intro hfree
      have hrestFree :=
        selectionSetTypenameFree_tail hfree
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest hrestFree

theorem normalizeOperation_typenameFree (schema : Schema) (operation : Operation)
    : operationTypenameFree operation
      -> operationTypenameFree (normalizeOperation schema operation) := by
  intro hfree
  simp [normalizeOperation, operationTypenameFree]
  exact normalizeSelectionSet_typenameFree schema (operation.rootType schema)
    operation.selectionSet hfree

end GraphQL.NormalForm.GroundTypeNormalization
