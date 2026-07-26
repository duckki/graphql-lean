import GraphQL.Theories.NormalForm

/-!
Directive-freeness facts for ground-type normalization proofs.
-/

namespace GraphQL

namespace NormalForm

theorem selectionSetDirectiveFree_nil
    : selectionSetDirectiveFree ([] : List Selection) := by
  simp [selectionSetDirectiveFree]

theorem selectionSetDirectiveFree_head
    {selection : Selection}
    {selectionSet : List Selection}
    : selectionSetDirectiveFree (selection :: selectionSet)
      -> selectionDirectiveFree selection := by
  intro hfree
  exact hfree.1

theorem selectionSetDirectiveFree_tail
    {selection : Selection}
    {selectionSet : List Selection}
    : selectionSetDirectiveFree (selection :: selectionSet)
      -> selectionSetDirectiveFree selectionSet := by
  intro hfree
  exact hfree.2

theorem selectionSetDirectiveFree_append {left right : List Selection}
    : selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetDirectiveFree (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa using hright
  | cons selection rest ih =>
      exact ⟨hleft.1, ih hleft.2⟩

theorem selectionSetDirectiveFree_append_left {left right : List Selection}
    : selectionSetDirectiveFree (left ++ right) -> selectionSetDirectiveFree left := by
  intro hfree
  induction left with
  | nil =>
      exact selectionSetDirectiveFree_nil
  | cons selection rest ih =>
      exact ⟨hfree.1, ih hfree.2⟩

theorem selectionSetDirectiveFree_append_right {left right : List Selection}
    : selectionSetDirectiveFree (left ++ right) -> selectionSetDirectiveFree right := by
  intro hfree
  induction left with
  | nil =>
      simpa using hfree
  | cons selection rest ih =>
      exact ih hfree.2

theorem selectionDirectiveFree_subselections {selection : Selection}
    : selectionDirectiveFree selection
      -> selectionSetDirectiveFree selection.subselections := by
  intro hfree
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      simpa [Selection.subselections, selectionDirectiveFree] using hfree.2
  | inlineFragment typeCondition directives selectionSet =>
      simpa [Selection.subselections, selectionDirectiveFree] using hfree.2

theorem fieldMerge_collectFields_mem_selectionSetDirectiveFree (schema : Schema)
    : ∀ parentType selectionSet scopedField,
        selectionSetDirectiveFree selectionSet
        -> scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
        -> selectionSetDirectiveFree scopedField.selectionSet
  | _parentType, [], _scopedField, _hfree, hmem => by
      simp [FieldMerge.collectFields] at hmem
  | parentType, selection :: rest, scopedField, hfree, hmem => by
      have hselectionFree : selectionDirectiveFree selection :=
        selectionSetDirectiveFree_head hfree
      have hrestFree : selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hmem
              exact fieldMerge_collectFields_mem_selectionSetDirectiveFree
                schema parentType rest scopedField hrestFree hmem
          | some fieldDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hmem
              rcases hmem with hhead | htail
              · subst scopedField
                simpa [selectionDirectiveFree] using hselectionFree.2
              · exact fieldMerge_collectFields_mem_selectionSetDirectiveFree
                  schema parentType rest scopedField hrestFree htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [FieldMerge.collectFields] at hmem
              rcases hmem with hbody | htail
              · exact fieldMerge_collectFields_mem_selectionSetDirectiveFree
                  schema parentType selectionSet scopedField
                  (by simpa [selectionDirectiveFree] using hselectionFree.2)
                  hbody
              · exact fieldMerge_collectFields_mem_selectionSetDirectiveFree
                  schema parentType rest scopedField hrestFree htail
          | some typeCondition =>
              simp [FieldMerge.collectFields] at hmem
              rcases hmem with hbody | htail
              · exact fieldMerge_collectFields_mem_selectionSetDirectiveFree
                  schema typeCondition selectionSet scopedField
                  (by simpa [selectionDirectiveFree] using hselectionFree.2)
                  hbody
              · exact fieldMerge_collectFields_mem_selectionSetDirectiveFree
                  schema parentType rest scopedField hrestFree htail

theorem selectionSetDirectiveFree_mergeSelectionSets {selections : List Selection}
    : selectionSetDirectiveFree selections
      -> selectionSetDirectiveFree (mergeSelectionSets selections) := by
  intro hselections
  induction selections with
  | nil =>
      exact selectionSetDirectiveFree_nil
  | cons selection rest ih =>
      simp [mergeSelectionSets]
      exact selectionSetDirectiveFree_append
        (selectionDirectiveFree_subselections
          (selectionSetDirectiveFree_head hselections))
        (ih (selectionSetDirectiveFree_tail hselections))

theorem withoutFieldSelectionsWithResponseName_directiveFree (schema : Schema)
    (responseName : Name)
    : ∀ selectionSet,
        selectionSetDirectiveFree selectionSet
        -> selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | [], _hfree => by
      simpa [withoutFieldSelectionsWithResponseName] using selectionSetDirectiveFree_nil
  | selection :: rest, hfree => by
      have hselection := selectionSetDirectiveFree_head hfree
      have hrest := selectionSetDirectiveFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname]
            exact withoutFieldSelectionsWithResponseName_directiveFree schema responseName
              rest hrest
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse]
            exact ⟨hselection,
              withoutFieldSelectionsWithResponseName_directiveFree schema responseName
                rest hrest⟩
      | inlineFragment typeCondition directives selectionSet =>
          have hdirectives : directives = [] := hselection.1
          subst directives
          simp [withoutFieldSelectionsWithResponseName]
          exact ⟨
            ⟨rfl,
              withoutFieldSelectionsWithResponseName_directiveFree schema responseName
                selectionSet hselection.2⟩,
            withoutFieldSelectionsWithResponseName_directiveFree schema responseName
              rest hrest⟩

theorem fieldSelectionsWithResponseNameInScope_directiveFree (schema : Schema)
    (parentType responseName : Name)
    : ∀ selectionSet,
        selectionSetDirectiveFree selectionSet
        -> selectionSetDirectiveFree
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet)
  | [], _hfree => by
      simpa [fieldSelectionsWithResponseNameInScope] using selectionSetDirectiveFree_nil
  | selection :: rest, hfree => by
      have hselection := selectionSetDirectiveFree_head hfree
      have hrest := selectionSetDirectiveFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, hname]
            exact ⟨hselection,
              fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
                responseName rest hrest⟩
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse]
            exact fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
              responseName rest hrest
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [fieldSelectionsWithResponseNameInScope]
              exact selectionSetDirectiveFree_append
                (fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
                  responseName selectionSet hselection.2)
                (fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
                  responseName rest hrest)
          | some typeCondition =>
              by_cases hoverlap :
                  (schema.typesOverlapBool parentType typeCondition) = true
              · simp [fieldSelectionsWithResponseNameInScope, hoverlap]
                exact selectionSetDirectiveFree_append
                  (fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
                    responseName selectionSet hselection.2)
                  (fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
                    responseName rest hrest)
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse]
                exact fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
                  responseName rest hrest

theorem selectionSetDirectiveFree_fieldHead_merged
    (schema : Schema) (parentType responseName : Name)
    (fieldName : Name) (arguments : List Argument)
    (subselections rest : List Selection)
    : selectionSetDirectiveFree
        (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetDirectiveFree
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hfree
  apply selectionSetDirectiveFree_append
  · exact (selectionSetDirectiveFree_head hfree).2
  · exact selectionSetDirectiveFree_mergeSelectionSets
      (fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
        responseName rest (selectionSetDirectiveFree_tail hfree))

end NormalForm

end GraphQL
