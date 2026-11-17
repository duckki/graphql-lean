import GraphQL.Theories.NormalForm

/-! Operation-local output-shape agreement through normalization's syntax helpers. -/

namespace GraphQL.NormalForm

theorem selectionSetFieldsSameOutputShape_append {schema : Schema}
    {left right : List Selection}
    (hleft : selectionSetFieldsSameOutputShape schema left)
    (hright : selectionSetFieldsSameOutputShape schema right)
    : selectionSetFieldsSameOutputShape schema (left ++ right) := by
  induction left with
  | nil => exact hright
  | cons head rest ih => exact ⟨hleft.1, ih hleft.2⟩

theorem selectionFieldsSameOutputShape_children {schema : Schema} {selection : Selection}
    (hshape : selectionFieldsSameOutputShape schema selection)
    : selectionSetFieldsSameOutputShape schema selection.subselections := by
  cases selection with
  | field => exact hshape.2
  | inlineFragment => exact hshape

theorem selectionSetFieldsSameOutputShape_mergeSelectionSets {schema : Schema}
    {selections : List Selection}
    (hshape : selectionSetFieldsSameOutputShape schema selections)
    : selectionSetFieldsSameOutputShape schema (mergeSelectionSets selections) := by
  induction selections with
  | nil => trivial
  | cons head rest ih =>
      exact selectionSetFieldsSameOutputShape_append
        (selectionFieldsSameOutputShape_children hshape.1) (ih hshape.2)

theorem selectionSetFieldsSameOutputShape_without (schema : Schema) (responseName : Name)
    : ∀ selections,
        selectionSetFieldsSameOutputShape schema selections
        -> selectionSetFieldsSameOutputShape schema
            (withoutFieldSelectionsWithResponseName schema responseName selections)
  | [], _ => by simp [withoutFieldSelectionsWithResponseName, selectionSetFieldsSameOutputShape]
  | .field name field arguments directives children :: rest, hshape => by
      simp only [withoutFieldSelectionsWithResponseName]
      split
      · exact selectionSetFieldsSameOutputShape_without schema responseName rest hshape.2
      · exact ⟨hshape.1,
          selectionSetFieldsSameOutputShape_without schema responseName rest hshape.2⟩
  | .inlineFragment condition directives children :: rest, hshape => by
      simp only [withoutFieldSelectionsWithResponseName, selectionSetFieldsSameOutputShape,
        selectionFieldsSameOutputShape]
      exact ⟨selectionSetFieldsSameOutputShape_without schema responseName children hshape.1,
        selectionSetFieldsSameOutputShape_without schema responseName rest hshape.2⟩

theorem selectionSetFieldsSameOutputShape_matching (schema : Schema)
    (parentType responseName : Name)
    : ∀ selections,
        selectionSetFieldsSameOutputShape schema selections
        -> selectionSetFieldsSameOutputShape schema
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selections)
  | [], _ => by simp [fieldSelectionsWithResponseNameInScope, selectionSetFieldsSameOutputShape]
  | .field name field arguments directives children :: rest, hshape => by
      simp only [fieldSelectionsWithResponseNameInScope]
      split
      · exact ⟨hshape.1,
          selectionSetFieldsSameOutputShape_matching schema parentType responseName rest hshape.2⟩
      · exact selectionSetFieldsSameOutputShape_matching schema parentType responseName rest hshape.2
  | .inlineFragment condition directives children :: rest, hshape => by
      have hrest := selectionSetFieldsSameOutputShape_matching schema parentType responseName
        rest hshape.2
      have hchildren := selectionSetFieldsSameOutputShape_matching schema parentType responseName
        children hshape.1
      cases condition with
      | none =>
          simpa only [fieldSelectionsWithResponseNameInScope]
            using selectionSetFieldsSameOutputShape_append hchildren hrest
      | some condition =>
          simp only [fieldSelectionsWithResponseNameInScope]
          split
          · exact selectionSetFieldsSameOutputShape_append hchildren hrest
          · exact hrest

theorem selectionSetFieldsSameOutputShape_merged (schema : Schema)
    {parentType responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {children rest : List Selection}
    (hshape
      : selectionSetFieldsSameOutputShape schema
          (.field responseName fieldName arguments directives children :: rest))
    : selectionSetFieldsSameOutputShape schema
        (children
          ++ mergeSelectionSets
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                rest)) := by
  exact selectionSetFieldsSameOutputShape_append hshape.1.2
    (selectionSetFieldsSameOutputShape_mergeSelectionSets
      (selectionSetFieldsSameOutputShape_matching schema parentType responseName rest hshape.2))

theorem selectionSetFieldsSameOutputShape_filter (schema : Schema) (boolCase : BoolCase)
    : ∀ selections,
        selectionSetFieldsSameOutputShape schema selections
        -> selectionSetFieldsSameOutputShape schema
            (filterSelectionSetBoolCase boolCase selections)
  | [], _ => by simp [filterSelectionSetBoolCase, selectionSetFieldsSameOutputShape]
  | .field name field arguments directives children :: rest, hshape => by
      have hrest := selectionSetFieldsSameOutputShape_filter schema boolCase rest hshape.2
      have hchildren := selectionSetFieldsSameOutputShape_filter schema boolCase children hshape.1.2
      simp only [filterSelectionSetBoolCase]
      split
      · split
        · exact ⟨⟨hshape.1.1, trivial⟩, hrest⟩
        · exact ⟨⟨hshape.1.1, trivial⟩, hrest⟩
        · refine ⟨⟨hshape.1.1, ?_⟩, hrest⟩
          simp_all only
      · exact hrest
  | .inlineFragment condition directives children :: rest, hshape => by
      have hrest := selectionSetFieldsSameOutputShape_filter schema boolCase rest hshape.2
      have hchildren := selectionSetFieldsSameOutputShape_filter schema boolCase children hshape.1
      simp only [filterSelectionSetBoolCase]
      split
      · split
        · exact hrest
        · refine ⟨?_, hrest⟩
          change selectionSetFieldsSameOutputShape schema _
          simp_all only
      · exact hrest

end GraphQL.NormalForm
