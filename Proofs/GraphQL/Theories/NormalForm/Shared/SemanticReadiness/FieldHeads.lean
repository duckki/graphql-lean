import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness.LookupTransport

/-! Field-head lookup and readiness facts. -/

namespace GraphQL

namespace NormalForm

theorem selectionSetLookupValid_field_head_lookup_none_false
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {selectionSet rest : List Selection}
    : selectionSetLookupValid schema parentType
        (Selection.field responseName fieldName arguments directives selectionSet :: rest)
      -> schema.lookupField parentType fieldName = none
      -> False := by
  intro hvalid hnone
  have hhead :
      selectionLookupValid schema parentType
        (Selection.field responseName fieldName arguments directives
          selectionSet) := by
    unfold selectionSetLookupValid at hvalid
    exact hvalid _ (by simp)
  simp [selectionLookupValid] at hhead
  rcases hhead with ⟨fieldDefinition, hlookup⟩
  rw [hnone] at hlookup
  contradiction

theorem selectionSetLookupValid_mergeSelectionSets_of_subselections
    {schema : Schema} {parentType : Name}
    : ∀ selections,
        (∀ selection,
          selection ∈ selections
          -> selectionSetLookupValid schema parentType selection.subselections)
        -> selectionSetLookupValid schema parentType (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets, selectionSetLookupValid]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply selectionSetLookupValid_append
      · exact hvalid selection (by simp)
      · exact selectionSetLookupValid_mergeSelectionSets_of_subselections rest
          (by
            intro candidate hcandidate
            exact hvalid candidate (by simp [hcandidate]))

theorem selectionSetLookupValid_mergeSelectionSets_of_field_subselections
    {schema : Schema} {parentType responseName : Name}
    (selections : List Selection)
    : (∀ selection,
        selection ∈ selections
        -> ∃ fieldName arguments directives subselections,
            selection
            = Selection.field responseName fieldName arguments directives subselections)
      -> (∀ fieldName arguments directives subselections,
            Selection.field responseName fieldName arguments directives subselections
              ∈ selections
            -> selectionSetLookupValid schema parentType subselections)
      -> selectionSetLookupValid schema parentType (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetLookupValid_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

theorem selectionSetLookupValid_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    {schema : Schema} {parentType responseName childType : Name}
    (selectionSet : List Selection)
    : (∀ fieldName arguments directives subselections,
        Selection.field responseName fieldName arguments directives subselections
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
        -> selectionSetLookupValid schema childType subselections)
      -> selectionSetLookupValid schema childType
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet)) := by
  intro hfields
  apply selectionSetLookupValid_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName
      selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem selectionSetLookupValid_fieldHead_merged_of_matching
    (schema : Schema)
    (parentType responseName fieldName childType : Name)
    (_arguments : List Argument) (subselections rest : List Selection)
    : selectionSetLookupValid schema childType subselections
      -> (∀ selection,
            selection
              ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
            -> ∃ matchedArguments matchedDirectives matchedSubselections,
                selection
                = Selection.field responseName fieldName matchedArguments
                    matchedDirectives matchedSubselections)
      -> (∀ matchedArguments matchedDirectives matchedSubselections,
            Selection.field responseName fieldName matchedArguments matchedDirectives
                matchedSubselections
              ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
            -> selectionSetLookupValid schema childType matchedSubselections)
      -> selectionSetLookupValid schema childType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hhead hshape hmatching
  apply selectionSetLookupValid_append hhead
  apply selectionSetLookupValid_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    rcases hshape selection hselection with
      ⟨matchedArguments, matchedDirectives, matchedSubselections,
        hselectionShape⟩
    exact ⟨fieldName, matchedArguments, matchedDirectives,
      matchedSubselections, hselectionShape⟩
  · intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    have hmatchedShape :=
      hshape
        (Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections)
        hmatched
    rcases hmatchedShape with
      ⟨shapeArguments, shapeDirectives, shapeSubselections, hshapeEq⟩
    injection hshapeEq with _hresponse hfield harguments hdirectives
      hsubselections
    subst matchedFieldName
    subst shapeArguments
    subst shapeDirectives
    subst shapeSubselections
    exact hmatching matchedArguments matchedDirectives matchedSubselections
      hmatched

theorem selectionSetLookupValid_fieldHead_merged_of_child_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.objectType parentType
      -> Validation.selectionSetValid schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> selectionSetLookupValid schema runtimeType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hschema hobject hvalid hmerge hlookup hinclude
  rcases Validation.selectionSetValid_field_head_lookup hvalid with
    ⟨headDefinition, hheadLookup, _harguments, hheadChild⟩
  have hdefinitionEq : headDefinition = fieldDefinition := by
    rw [hlookup] at hheadLookup
    cases hheadLookup
    rfl
  subst headDefinition
  have hheadSelectionValid :
      Validation.selectionSetValid schema variableDefinitions
        fieldDefinition.outputType.namedType subselections :=
    fieldSelectionSetValid_child_of_possibleType hheadChild
      (List.contains_iff_mem.mp hinclude)
  have hheadLookupValid :
      selectionSetLookupValid schema runtimeType subselections :=
    selectionSetLookupValid_of_selectionSetValid_possibleObject schema
      variableDefinitions fieldDefinition.outputType.namedType runtimeType
      hschema (List.contains_iff_mem.mp hinclude) subselections
      hheadSelectionValid
  have hlookupValid :
      selectionSetLookupValid schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) :=
    selectionSetLookupValid_of_selectionSetValid
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      hvalid
  apply selectionSetLookupValid_fieldHead_merged_of_matching schema parentType
    responseName fieldName runtimeType arguments subselections rest
  · exact hheadLookupValid
  · exact
      fieldSelectionsWithResponseNameInScope_matching_field_shape_of_canMerge_object_lookupValid
        schema parentType responseName fieldName arguments subselections rest
        hobject hlookupValid hmerge
  · intro matchedArguments matchedDirectives matchedSubselections hmatched
    exact
      fieldSelectionsWithResponseNameInScope_matching_subselections_lookupValid_of_child_object
        schema variableDefinitions parentType responseName fieldName
        runtimeType arguments subselections rest fieldDefinition hschema
        hobject hvalid hmerge hlookup hinclude fieldName matchedArguments
        matchedDirectives matchedSubselections hmatched

theorem selectionSetSemanticsReady_fieldHead_merged_of_child_object
    (schema : Schema)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetSemanticsReady schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> selectionSetSemanticsReady schema runtimeType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hobject hready hlookupValid hmerge hlookup hinclude
  have hheadReady :
      selectionSemanticsReady schema parentType
        (Selection.field responseName fieldName arguments [] subselections) := by
    unfold selectionSetSemanticsReady at hready
    exact hready _ (by simp)
  have hheadChildReady :
      selectionSetSemanticsReady schema runtimeType subselections := by
    simp [selectionSemanticsReady] at hheadReady
    rcases hheadReady with ⟨headDefinition, hheadLookup, hchildReady⟩
    rw [hlookup] at hheadLookup
    cases hheadLookup
    exact hchildReady runtimeType hinclude
  apply selectionSetSemanticsReady_append hheadChildReady
  apply selectionSetSemanticsReady_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    rcases
      fieldSelectionsWithResponseNameInScope_matching_field_shape_of_canMerge_object_lookupValid
        schema parentType responseName fieldName arguments subselections rest
        hobject hlookupValid hmerge selection hselection with
      ⟨matchedArguments, matchedDirectives, matchedSubselections, hselectionEq⟩
    exact
      ⟨fieldName, matchedArguments, matchedDirectives, matchedSubselections,
        hselectionEq⟩
  · intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    have hmatchedShape :=
      fieldSelectionsWithResponseNameInScope_matching_field_shape_of_canMerge_object_lookupValid
        schema parentType responseName fieldName arguments subselections rest
        hobject hlookupValid hmerge
        (Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections)
        hmatched
    rcases hmatchedShape with
      ⟨shapeArguments, shapeDirectives, shapeSubselections, hshapeEq⟩
    injection hshapeEq with _hresponse hfield harguments hdirectives
      hsubselections
    subst matchedFieldName
    subst shapeArguments
    subst shapeDirectives
    subst shapeSubselections
    exact
      fieldSelectionsWithResponseNameInScope_matching_subselections_semanticsReady_of_child_object
        schema parentType responseName fieldName runtimeType arguments
        subselections rest fieldDefinition hobject hready hlookupValid
        hmerge hlookup hinclude fieldName matchedArguments
        matchedDirectives matchedSubselections hmatched

end NormalForm

end GraphQL
