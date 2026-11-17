import Proofs.GraphQL.Theories.NormalForm.TypenameFree

namespace GraphQL.NormalForm

theorem selectionTypenameFree_subselections {selection : Selection}
    : selectionTypenameFree selection
      -> selectionSetTypenameFree selection.subselections := by
  intro hfree
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      rw [selectionTypenameFree] at hfree
      simpa [Selection.subselections, selectionTypenameFree] using hfree.2
  | inlineFragment typeCondition directives selectionSet =>
      simpa [Selection.subselections, selectionTypenameFree] using hfree

theorem fieldMerge_collectFields_mem_selectionSetTypenameFree (schema : Schema)
    : ∀ parentType selectionSet scopedField,
        selectionSetTypenameFree selectionSet
        -> scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
        -> selectionSetTypenameFree scopedField.selectionSet
  | _parentType, [], _scopedField, _hfree, hmem => by
      simp [FieldMerge.collectFields] at hmem
  | parentType, selection :: rest, scopedField, hfree, hmem => by
      have hselectionFree : selectionTypenameFree selection :=
        selectionSetTypenameFree_head hfree
      have hrestFree : selectionSetTypenameFree rest :=
        selectionSetTypenameFree_tail hfree
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          rw [selectionTypenameFree] at hselectionFree
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hmem
              exact fieldMerge_collectFields_mem_selectionSetTypenameFree
                schema parentType rest scopedField hrestFree hmem
          | some fieldDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hmem
              rcases hmem with hhead | htail
              · subst scopedField
                simpa [selectionTypenameFree] using hselectionFree.2
              · exact fieldMerge_collectFields_mem_selectionSetTypenameFree
                  schema parentType rest scopedField hrestFree htail
      | inlineFragment typeCondition directives selectionSet =>
          rw [selectionTypenameFree] at hselectionFree
          cases typeCondition with
          | none =>
              simp [FieldMerge.collectFields] at hmem
              rcases hmem with hbody | htail
              · exact fieldMerge_collectFields_mem_selectionSetTypenameFree
                  schema parentType selectionSet scopedField
                  (by simpa [selectionTypenameFree] using hselectionFree)
                  hbody
              · exact fieldMerge_collectFields_mem_selectionSetTypenameFree
                  schema parentType rest scopedField hrestFree htail
          | some typeCondition =>
              simp [FieldMerge.collectFields] at hmem
              rcases hmem with hbody | htail
              · exact fieldMerge_collectFields_mem_selectionSetTypenameFree
                  schema typeCondition selectionSet scopedField
                  (by simpa [selectionTypenameFree] using hselectionFree)
                  hbody
              · exact fieldMerge_collectFields_mem_selectionSetTypenameFree
                  schema parentType rest scopedField hrestFree htail

theorem selectionSetTypenameFree_mergeSelectionSets {selections : List Selection}
    : selectionSetTypenameFree selections
      -> selectionSetTypenameFree (mergeSelectionSets selections) := by
  intro hselections
  induction selections with
  | nil =>
      exact selectionSetTypenameFree_nil
  | cons selection rest ih =>
      simp [mergeSelectionSets]
      exact selectionSetTypenameFree_append
        (selectionTypenameFree_subselections
          (selectionSetTypenameFree_head hselections))
        (ih (selectionSetTypenameFree_tail hselections))

theorem withoutFieldSelectionsWithResponseName_typenameFree (schema : Schema)
    (responseName : Name)
    : ∀ selectionSet,
        selectionSetTypenameFree selectionSet
        -> selectionSetTypenameFree
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | [], _hfree => by
      simpa [withoutFieldSelectionsWithResponseName] using selectionSetTypenameFree_nil
  | selection :: rest, hfree => by
      have hselection := selectionSetTypenameFree_head hfree
      have hrest := selectionSetTypenameFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname]
            exact withoutFieldSelectionsWithResponseName_typenameFree schema responseName
              rest hrest
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse]
            exact selectionSetTypenameFree_cons hselection
              (withoutFieldSelectionsWithResponseName_typenameFree schema responseName
                rest hrest)
      | inlineFragment typeCondition directives selectionSet =>
          rw [selectionTypenameFree] at hselection
          simp [withoutFieldSelectionsWithResponseName]
          exact selectionSetTypenameFree_cons
            (by
              simpa only [selectionTypenameFree] using
                (withoutFieldSelectionsWithResponseName_typenameFree schema responseName
                  selectionSet hselection))
            (withoutFieldSelectionsWithResponseName_typenameFree schema responseName
              rest hrest)

theorem fieldSelectionsWithResponseNameInScope_typenameFree (schema : Schema)
    (parentType responseName : Name)
    : ∀ selectionSet,
        selectionSetTypenameFree selectionSet
        -> selectionSetTypenameFree
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet)
  | [], _hfree => by
      simpa [fieldSelectionsWithResponseNameInScope] using selectionSetTypenameFree_nil
  | selection :: rest, hfree => by
      have hselection := selectionSetTypenameFree_head hfree
      have hrest := selectionSetTypenameFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, hname]
            exact selectionSetTypenameFree_cons hselection
              (fieldSelectionsWithResponseNameInScope_typenameFree schema parentType
                responseName rest hrest)
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse]
            exact fieldSelectionsWithResponseNameInScope_typenameFree schema parentType
              responseName rest hrest
      | inlineFragment typeCondition directives selectionSet =>
          rw [selectionTypenameFree] at hselection
          cases typeCondition with
          | none =>
              simp [fieldSelectionsWithResponseNameInScope]
              exact selectionSetTypenameFree_append
                (fieldSelectionsWithResponseNameInScope_typenameFree schema parentType
                  responseName selectionSet hselection)
                (fieldSelectionsWithResponseNameInScope_typenameFree schema parentType
                  responseName rest hrest)
          | some typeCondition =>
              by_cases hoverlap :
                  (schema.typesOverlapBool parentType typeCondition) = true
              · simp [fieldSelectionsWithResponseNameInScope, hoverlap]
                exact selectionSetTypenameFree_append
                  (fieldSelectionsWithResponseNameInScope_typenameFree schema parentType
                    responseName selectionSet hselection)
                  (fieldSelectionsWithResponseNameInScope_typenameFree schema parentType
                    responseName rest hrest)
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse]
                exact fieldSelectionsWithResponseNameInScope_typenameFree schema parentType
                  responseName rest hrest

end GraphQL.NormalForm
