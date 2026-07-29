import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeTypes
import Proofs.GraphQL.Validation.FieldMerge

/-!
Validation facts transported through ground-type normalization helpers.
-/

namespace GraphQL

namespace NormalForm

theorem fieldSelectionsWithResponseNameInScope_mem_field (schema : Schema)
    (parentType responseName : Name)
    : ∀ selectionSet selection,
        selection
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
        -> ∃ fieldName arguments directives subselections,
            selection
            = Selection.field responseName fieldName arguments directives subselections
  | [], selection, hselection => by
      simp [fieldSelectionsWithResponseNameInScope] at hselection
  | source :: rest, selection, hselection => by
      cases source with
      | field fieldResponseName fieldName arguments directives subselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, hname] at hselection
            rcases hselection with hselection | hselection
            · subst selection
              have hresponseName : fieldResponseName = responseName :=
                beq_iff_eq.mp hname
              subst fieldResponseName
              exact ⟨fieldName, arguments, directives, subselections, rfl⟩
            · exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
                responseName rest selection hselection
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hselection
            exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
              responseName rest selection hselection
      | inlineFragment typeCondition directives subselections =>
          cases typeCondition with
          | none =>
              simp [fieldSelectionsWithResponseNameInScope] at hselection
              rcases hselection with hselection | hselection
              · exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
                  responseName subselections selection hselection
              · exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
                  responseName rest selection hselection
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hselection
                rcases hselection with hselection | hselection
                · exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
                    responseName subselections selection hselection
                · exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
                    responseName rest selection hselection
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hselection
                exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
                  responseName rest selection hselection

theorem fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (filterParent collectParent responseName : Name)
    : ∀ selectionSet fieldName arguments directives subselections,
        (schema.objectType collectParent
          -> schema.typesOverlapBool filterParent collectParent = true)
        -> Validation.selectionSetValid schema variableDefinitions collectParent
            selectionSet
        -> Selection.field responseName fieldName arguments directives subselections
            ∈ fieldSelectionsWithResponseNameInScope schema filterParent responseName
                selectionSet
        -> ∃ scopedField,
            scopedField ∈ FieldMerge.collectFields schema collectParent selectionSet
            ∧ scopedField.responseName = responseName
            ∧ scopedField.fieldName = fieldName
            ∧ scopedField.arguments = arguments
            ∧ scopedField.selectionSet = subselections
            ∧ (schema.objectType scopedField.parentType
                -> schema.typesOverlapBool filterParent scopedField.parentType = true)
  | [], fieldName, arguments, directives, subselections, _hoverlapScope,
      _hvalid, hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | selection :: rest, fieldName, arguments, directives, subselections,
      hoverlapScope, hvalid, hfield => by
      have hhead :
          Validation.selectionValid schema variableDefinitions collectParent
            selection := by
        simp [Validation.selectionSetValid] at hvalid
        exact hvalid.1
      have htail :
          Validation.selectionSetValid schema variableDefinitions collectParent
            rest :=
        Validation.selectionSetValid_tail hvalid
      cases selection with
      | field fieldResponseName sourceFieldName sourceArguments
          sourceDirectives sourceSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, hname] at hfield
            rcases hfield with hfield | hfield
            · rcases hfield with
                ⟨hresponseEq, hfieldEq, hargumentsEq, hdirectivesEq,
                  hsubselectionsEq⟩
              subst fieldResponseName
              subst sourceFieldName
              subst sourceArguments
              subst sourceDirectives
              subst sourceSubselections
              rcases Validation.selectionValid_field_lookup hhead with
                ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
              refine ⟨{
                parentType := collectParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                outputType := fieldDefinition.outputType,
                selectionSet := subselections
              }, ?_, rfl, rfl, rfl, rfl, ?_⟩
              simp [FieldMerge.collectFields, hlookup]
              exact hoverlapScope
            · rcases
                fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped
                  schema variableDefinitions filterParent collectParent
                  responseName rest fieldName arguments directives
                  subselections hoverlapScope htail hfield with
                ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
              refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                hselectionSet, hscopedOverlap⟩
              rcases Validation.selectionValid_field_lookup hhead with
                ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
              simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            rcases
              fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped
                schema variableDefinitions filterParent collectParent
                responseName rest fieldName arguments directives
                subselections hoverlapScope htail hfield with
              ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                hselectionSet, hscopedOverlap⟩
            refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
              hselectionSet, hscopedOverlap⟩
            rcases Validation.selectionValid_field_lookup hhead with
              ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
            simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
      | inlineFragment typeCondition _fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionSetValid :
                  Validation.selectionSetValid schema variableDefinitions
                    collectParent selectionSet :=
                Validation.selectionValid_inlineFragment_none_selectionSetValid
                  hhead
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hfield | hfield
              · rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped
                    schema variableDefinitions filterParent collectParent
                    responseName selectionSet fieldName arguments directives
                    subselections hoverlapScope hselectionSetValid hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]
              · rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped
                    schema variableDefinitions filterParent collectParent
                    responseName rest fieldName arguments directives
                    subselections hoverlapScope htail hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]
          | some typeCondition =>
              have hselectionSetValid :
                  Validation.selectionSetValid schema variableDefinitions
                    typeCondition selectionSet :=
                Validation.selectionValid_inlineFragment_some_selectionSetValid
                  hhead
              by_cases hoverlap :
                  schema.typesOverlapBool filterParent typeCondition = true
              · simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                rcases hfield with hfield | hfield
                · rcases
                    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped
                      schema variableDefinitions filterParent typeCondition
                      responseName selectionSet fieldName arguments directives
                      subselections (fun _hobject => hoverlap)
                      hselectionSetValid hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                      hselectionSet, hscopedOverlap⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases
                    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped
                      schema variableDefinitions filterParent collectParent
                      responseName rest fieldName arguments directives
                      subselections hoverlapScope htail hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                      hselectionSet, hscopedOverlap⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                  simp [FieldMerge.collectFields, hscoped]
              · have hfalse :
                    schema.typesOverlapBool filterParent typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool filterParent typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped
                    schema variableDefinitions filterParent collectParent
                    responseName rest fieldName arguments directives
                    subselections hoverlapScope htail hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]

theorem
    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_source_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (filterParent collectParent responseName : Name)
    : ∀ selectionSet fieldName arguments directives subselections,
        (schema.objectType filterParent
          -> schema.typeIncludesObjectBool collectParent filterParent = true)
        -> Validation.selectionSetValid schema variableDefinitions collectParent
            selectionSet
        -> Selection.field responseName fieldName arguments directives subselections
            ∈ fieldSelectionsWithResponseNameInScope schema filterParent responseName
                selectionSet
        -> ∃ scopedField,
            scopedField ∈ FieldMerge.collectFields schema collectParent selectionSet
            ∧ scopedField.responseName = responseName
            ∧ scopedField.fieldName = fieldName
            ∧ scopedField.arguments = arguments
            ∧ scopedField.selectionSet = subselections
            ∧ (schema.objectType filterParent
                -> schema.typeIncludesObjectBool scopedField.parentType filterParent
                    = true)
  | [], fieldName, arguments, directives, subselections, _hsourceScope,
      _hvalid, hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | selection :: rest, fieldName, arguments, directives, subselections,
      hsourceScope, hvalid, hfield => by
      have hhead :
          Validation.selectionValid schema variableDefinitions collectParent
            selection := by
        simp [Validation.selectionSetValid] at hvalid
        exact hvalid.1
      have htail :
          Validation.selectionSetValid schema variableDefinitions collectParent
            rest :=
        Validation.selectionSetValid_tail hvalid
      cases selection with
      | field fieldResponseName sourceFieldName sourceArguments
          sourceDirectives sourceSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, hname] at hfield
            rcases hfield with hfield | hfield
            · rcases hfield with
                ⟨hresponseEq, hfieldEq, hargumentsEq, hdirectivesEq,
                  hsubselectionsEq⟩
              subst fieldResponseName
              subst sourceFieldName
              subst sourceArguments
              subst sourceDirectives
              subst sourceSubselections
              rcases Validation.selectionValid_field_lookup hhead with
                ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
              refine ⟨{
                parentType := collectParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                outputType := fieldDefinition.outputType,
                selectionSet := subselections
              }, ?_, rfl, rfl, rfl, rfl, ?_⟩
              · simp [FieldMerge.collectFields, hlookup]
              · exact hsourceScope
            · rcases
                fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_source_object
                  schema variableDefinitions filterParent collectParent
                  responseName rest fieldName arguments directives
                  subselections hsourceScope htail hfield with
                ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedSource⟩
              rcases Validation.selectionValid_field_lookup hhead with
                ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
              refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                hselectionSet, hscopedSource⟩
              simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            rcases
              fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_source_object
                schema variableDefinitions filterParent collectParent
                responseName rest fieldName arguments directives subselections
                hsourceScope htail hfield with
              ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                hselectionSet, hscopedSource⟩
            rcases Validation.selectionValid_field_lookup hhead with
              ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
            refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
              hselectionSet, hscopedSource⟩
            simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
      | inlineFragment typeCondition _fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionSetValid :
                  Validation.selectionSetValid schema variableDefinitions
                    collectParent selectionSet :=
                Validation.selectionValid_inlineFragment_none_selectionSetValid
                  hhead
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hfield | hfield
              · rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_source_object
                    schema variableDefinitions filterParent collectParent
                    responseName selectionSet fieldName arguments directives
                    subselections hsourceScope hselectionSetValid hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedSource⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedSource⟩
                simp [FieldMerge.collectFields, hscoped]
              · rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_source_object
                    schema variableDefinitions filterParent collectParent
                    responseName rest fieldName arguments directives
                    subselections hsourceScope htail hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedSource⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedSource⟩
                simp [FieldMerge.collectFields, hscoped]
          | some typeCondition =>
              have hselectionSetValid :
                  Validation.selectionSetValid schema variableDefinitions
                    typeCondition selectionSet :=
                Validation.selectionValid_inlineFragment_some_selectionSetValid
                  hhead
              by_cases hoverlap :
                  schema.typesOverlapBool filterParent typeCondition = true
              · simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                have hfragmentSource :
                    schema.objectType filterParent ->
                      schema.typeIncludesObjectBool typeCondition
                        filterParent = true := by
                  intro hfilterObject
                  exact typeIncludesObjectBool_of_object_typesOverlapBool
                    schema hfilterObject hoverlap
                rcases hfield with hfield | hfield
                · rcases
                    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_source_object
                      schema variableDefinitions filterParent typeCondition
                      responseName selectionSet fieldName arguments directives
                      subselections hfragmentSource hselectionSetValid hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                      hselectionSet, hscopedSource⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedSource⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases
                    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_source_object
                      schema variableDefinitions filterParent collectParent
                      responseName rest fieldName arguments directives
                      subselections hsourceScope htail hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                      hselectionSet, hscopedSource⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedSource⟩
                  simp [FieldMerge.collectFields, hscoped]
              · have hfalse :
                    schema.typesOverlapBool filterParent typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool filterParent typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_source_object
                    schema variableDefinitions filterParent collectParent
                    responseName rest fieldName arguments directives
                    subselections hsourceScope htail hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedSource⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedSource⟩
                simp [FieldMerge.collectFields, hscoped]

theorem collectFields_scoped_mem_fieldSelectionSetValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    : ∀ selectionSet scopedField,
        Validation.selectionSetValid schema variableDefinitions parentType selectionSet
        -> scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
        -> ∃ fieldDefinition,
            schema.lookupField scopedField.parentType scopedField.fieldName
              = some fieldDefinition
            ∧ fieldDefinition.outputType = scopedField.outputType
            ∧ Validation.fieldSelectionSetValid schema variableDefinitions
                fieldDefinition scopedField.selectionSet
  | [], scopedField, _hvalid, hscoped => by
      simp [FieldMerge.collectFields] at hscoped
  | selection :: rest, scopedField, hvalid, hscoped => by
      have hhead :
          Validation.selectionValid schema variableDefinitions parentType
            selection := by
        simp [Validation.selectionSetValid] at hvalid
        exact hvalid.1
      have htail :
          Validation.selectionSetValid schema variableDefinitions parentType
            rest :=
        Validation.selectionSetValid_tail hvalid
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          rcases Validation.selectionValid_field_lookup hhead with
            ⟨fieldDefinition, hlookup, _harguments, hchild⟩
          simp [FieldMerge.collectFields, hlookup] at hscoped
          rcases hscoped with hcurrent | hrest
          · subst scopedField
            exact ⟨fieldDefinition, hlookup, rfl, hchild⟩
          · exact collectFields_scoped_mem_fieldSelectionSetValid schema
              variableDefinitions parentType rest scopedField htail hrest
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionSetValid :
                  Validation.selectionSetValid schema variableDefinitions
                    parentType selectionSet :=
                Validation.selectionValid_inlineFragment_none_selectionSetValid
                  hhead
              simp [FieldMerge.collectFields] at hscoped
              rcases hscoped with hselectionSet | hrest
              · exact collectFields_scoped_mem_fieldSelectionSetValid schema
                  variableDefinitions parentType selectionSet scopedField
                  hselectionSetValid hselectionSet
              · exact collectFields_scoped_mem_fieldSelectionSetValid schema
                  variableDefinitions parentType rest scopedField htail hrest
          | some typeCondition =>
              have hselectionSetValid :
                  Validation.selectionSetValid schema variableDefinitions
                    typeCondition selectionSet :=
                Validation.selectionValid_inlineFragment_some_selectionSetValid
                  hhead
              simp [FieldMerge.collectFields] at hscoped
              rcases hscoped with hselectionSet | hrest
              · exact collectFields_scoped_mem_fieldSelectionSetValid schema
                  variableDefinitions typeCondition selectionSet scopedField
                  hselectionSetValid hselectionSet
              · exact collectFields_scoped_mem_fieldSelectionSetValid schema
                  variableDefinitions parentType rest scopedField htail hrest

theorem selectionSetValid_mergeSelectionSets_of_subselections
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name}
    : ∀ selections,
        (∀ selection,
          selection ∈ selections
          -> Validation.selectionSetValid schema variableDefinitions parentType
              selection.subselections)
        -> Validation.selectionSetValid schema variableDefinitions parentType
            (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets, Validation.selectionSetValid]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply Validation.selectionSetValid_append
      · exact hvalid selection (by simp)
      · exact selectionSetValid_mergeSelectionSets_of_subselections rest
          (by
            intro candidate hcandidate
            exact hvalid candidate (by simp [hcandidate]))

theorem selectionSetValid_mergeSelectionSets_of_field_subselections
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName : Name}
    (selections : List Selection)
    : (∀ selection,
        selection ∈ selections
        -> ∃ fieldName arguments directives subselections,
            selection
            = Selection.field responseName fieldName arguments directives subselections)
      -> (∀ fieldName arguments directives subselections,
            Selection.field responseName fieldName arguments directives subselections
              ∈ selections
            -> Validation.selectionSetValid schema variableDefinitions parentType
                subselections)
      -> Validation.selectionSetValid schema variableDefinitions parentType
          (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetValid_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

theorem selectionSetValid_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName childType : Name}
    (selectionSet : List Selection)
    : (∀ fieldName arguments directives subselections,
        Selection.field responseName fieldName arguments directives subselections
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
        -> Validation.selectionSetValid schema variableDefinitions childType
            subselections)
      -> Validation.selectionSetValid schema variableDefinitions childType
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet)) := by
  intro hfields
  apply selectionSetValid_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName
      selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem fieldMerge_collectFields_mergeSelectionSets_mem
    (schema : Schema) (parentType : Name) (selections : List Selection)
    (scopedField : FieldMerge.ScopedField)
    : scopedField
        ∈ FieldMerge.collectFields schema parentType (mergeSelectionSets selections)
      -> ∃ selection,
          selection ∈ selections
          ∧ scopedField
            ∈ FieldMerge.collectFields schema parentType selection.subselections := by
  induction selections with
  | nil =>
      intro hfield
      simp [mergeSelectionSets, FieldMerge.collectFields] at hfield
  | cons selection rest ih =>
      intro hfield
      simp [mergeSelectionSets] at hfield
      rw [FieldMerge.collectFields_append] at hfield
      rcases List.mem_append.mp hfield with hhead | hrest
      · exact ⟨selection, by simp, hhead⟩
      · rcases ih hrest with
          ⟨sourceSelection, hsourceSelection, hsourceField⟩
        exact ⟨sourceSelection, by simp [hsourceSelection],
          hsourceField⟩

theorem fieldsInSetCanMerge_mergeSelectionSets_of_pairwise
    (schema : Schema) (parentType : Name) (selections : List Selection)
    : (∀ leftSelection,
        leftSelection ∈ selections
        -> ∀ rightSelection,
            rightSelection ∈ selections
            -> FieldMerge.fieldsInSetCanMerge schema parentType
                (leftSelection.subselections ++ rightSelection.subselections))
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (mergeSelectionSets selections) := by
  intro hpairwise
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (mergeSelectionSets selections) ?_
  dsimp
  intro left hleft right hright hresponse
  rcases fieldMerge_collectFields_mergeSelectionSets_mem schema parentType
      selections left hleft with
    ⟨leftSelection, hleftSelection, hleftField⟩
  rcases fieldMerge_collectFields_mergeSelectionSets_mem schema parentType
      selections right hright with
    ⟨rightSelection, hrightSelection, hrightField⟩
  have hpair :
      FieldMerge.fieldsInSetCanMerge schema parentType
        (leftSelection.subselections ++ rightSelection.subselections) :=
    hpairwise leftSelection hleftSelection rightSelection hrightSelection
  have hleftPair :
      left ∈ FieldMerge.collectFields schema parentType
        (leftSelection.subselections ++ rightSelection.subselections) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_left
      (FieldMerge.collectFields schema parentType
        rightSelection.subselections)
      hleftField
  have hrightPair :
      right ∈ FieldMerge.collectFields schema parentType
        (leftSelection.subselections ++ rightSelection.subselections) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_right
      (FieldMerge.collectFields schema parentType leftSelection.subselections)
      hrightField
  exact FieldMerge.fieldsInSetCanMerge_pair hpair hleftPair hrightPair
    hresponse

theorem fieldMerge_collectFields_tail_mem
    (schema : Schema) (parentType : Name)
    (selection : Selection) (rest : List Selection)
    (scopedField : FieldMerge.ScopedField)
    : scopedField ∈ FieldMerge.collectFields schema parentType rest
      -> scopedField
          ∈ FieldMerge.collectFields schema parentType (selection :: rest) := by
  intro hfield
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      cases hlookup : schema.lookupField parentType fieldName with
      | none =>
          simpa [FieldMerge.collectFields, hlookup] using hfield
      | some fieldDefinition =>
          simp [FieldMerge.collectFields, hlookup, hfield]
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          simp [FieldMerge.collectFields, hfield]
      | some typeCondition =>
          simp [FieldMerge.collectFields, hfield]

theorem fieldMerge_collectFields_append_left_mem
    (schema : Schema) (parentType : Name)
    (left right : List Selection) (scopedField : FieldMerge.ScopedField)
    : scopedField ∈ FieldMerge.collectFields schema parentType left
      -> scopedField ∈ FieldMerge.collectFields schema parentType (left ++ right) := by
  intro hfield
  rw [FieldMerge.collectFields_append]
  exact List.mem_append_left
    (FieldMerge.collectFields schema parentType right) hfield

theorem fieldMerge_collectFields_append_right_mem
    (schema : Schema) (parentType : Name)
    (left right : List Selection) (scopedField : FieldMerge.ScopedField)
    : scopedField ∈ FieldMerge.collectFields schema parentType right
      -> scopedField ∈ FieldMerge.collectFields schema parentType (left ++ right) := by
  intro hfield
  rw [FieldMerge.collectFields_append]
  exact List.mem_append_right
    (FieldMerge.collectFields schema parentType left) hfield

theorem fieldsInSetCanMerge_tail
    (schema : Schema) (parentType : Name)
    (selection : Selection) (rest : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType (selection :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType rest := by
  intro hmerge
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType rest ?_
  dsimp
  intro left hleft right hright hresponse
  exact FieldMerge.fieldsInSetCanMerge_pair hmerge
    (fieldMerge_collectFields_tail_mem schema parentType selection rest left
      hleft)
    (fieldMerge_collectFields_tail_mem schema parentType selection rest right
      hright)
    hresponse

theorem fieldsInSetCanMerge_append_left
    (schema : Schema) (parentType : Name)
    (left right : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType (left ++ right)
      -> FieldMerge.fieldsInSetCanMerge schema parentType left := by
  intro hmerge
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType left ?_
  dsimp
  intro leftField hleft rightField hright hresponse
  exact FieldMerge.fieldsInSetCanMerge_pair hmerge
    (fieldMerge_collectFields_append_left_mem schema parentType left right
      leftField hleft)
    (fieldMerge_collectFields_append_left_mem schema parentType left right
      rightField hright)
    hresponse

theorem fieldsInSetCanMerge_append_right
    (schema : Schema) (parentType : Name)
    (left right : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType (left ++ right)
      -> FieldMerge.fieldsInSetCanMerge schema parentType right := by
  intro hmerge
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType right ?_
  dsimp
  intro leftField hleft rightField hright hresponse
  exact FieldMerge.fieldsInSetCanMerge_pair hmerge
    (fieldMerge_collectFields_append_right_mem schema parentType left right
      leftField hleft)
    (fieldMerge_collectFields_append_right_mem schema parentType left right
      rightField hright)
    hresponse

theorem fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
    (schema : Schema) (responseName parentType : Name)
    : ∀ selectionSet scopedField,
        scopedField
          ∈ FieldMerge.collectFields schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
        -> scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
  | [], scopedField, hfield => by
      simp [withoutFieldSelectionsWithResponseName, FieldMerge.collectFields] at hfield
  | selection :: rest, scopedField, hfield => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname] at hfield
            exact fieldMerge_collectFields_tail_mem schema parentType
              (Selection.field fieldResponseName fieldName arguments directives
                selectionSet)
              rest scopedField
              (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
                schema responseName parentType rest scopedField hfield)
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            cases hlookup : schema.lookupField parentType fieldName with
            | none =>
                simp [withoutFieldSelectionsWithResponseName, hfalse,
                  FieldMerge.collectFields, hlookup] at hfield ⊢
                exact
                  fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
                    schema responseName parentType rest scopedField hfield
            | some fieldDefinition =>
                simp [withoutFieldSelectionsWithResponseName, hfalse,
                  FieldMerge.collectFields, hlookup] at hfield ⊢
                rcases hfield with hhead | htail
                · exact Or.inl hhead
                · exact Or.inr
                    (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
                      schema responseName parentType rest scopedField htail)
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [withoutFieldSelectionsWithResponseName, FieldMerge.collectFields]
                at hfield ⊢
              rcases hfield with hselection | hrest
              · exact Or.inl
                  (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
                    schema responseName parentType selectionSet scopedField
                    hselection)
              · exact Or.inr
                  (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
                    schema responseName parentType rest scopedField hrest)
          | some typeCondition =>
              simp [withoutFieldSelectionsWithResponseName, FieldMerge.collectFields]
                at hfield ⊢
              rcases hfield with hselection | hrest
              · exact Or.inl
                  (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
                    schema responseName typeCondition selectionSet scopedField
                    hselection)
              · exact Or.inr
                  (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
                    schema responseName parentType rest scopedField hrest)

theorem fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName parentType : Name)
    (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet) := by
  intro hmerge
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (withoutFieldSelectionsWithResponseName schema responseName selectionSet) ?_
  dsimp
  intro left hleft right hright hresponse
  exact FieldMerge.fieldsInSetCanMerge_pair hmerge
    (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem schema
      responseName parentType selectionSet left hleft)
    (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem schema
      responseName parentType selectionSet right hright)
    hresponse

theorem fieldsInSetCanMerge_inlineFragment_none_flatten
    (schema : Schema) (parentType : Name)
    (selectionSet rest : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType
        (Selection.inlineFragment none [] selectionSet :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType (selectionSet ++ rest) := by
  intro hmerge
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (selectionSet ++ rest) ?_
  dsimp
  intro left hleft right hright hresponse
  have hleftOriginal :
      left ∈ FieldMerge.collectFields schema parentType
        (Selection.inlineFragment none [] selectionSet :: rest) := by
    simpa [FieldMerge.collectFields, FieldMerge.collectFields_append]
      using hleft
  have hrightOriginal :
      right ∈ FieldMerge.collectFields schema parentType
        (Selection.inlineFragment none [] selectionSet :: rest) := by
    simpa [FieldMerge.collectFields, FieldMerge.collectFields_append]
      using hright
  exact FieldMerge.fieldsInSetCanMerge_pair hmerge hleftOriginal
    hrightOriginal hresponse

theorem fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName objectType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> Validation.selectionSetValid schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> FieldMerge.fieldsInSetCanMerge schema objectType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hobject hvalid hmerge hlookup
  let headSelection : Selection :=
    Selection.field responseName fieldName arguments [] subselections
  let matching :=
    fieldSelectionsWithResponseNameInScope schema parentType responseName rest
  let group := headSelection :: matching
  let headScoped : FieldMerge.ScopedField :=
    {
      parentType := parentType,
      responseName := responseName,
      fieldName := fieldName,
      arguments := arguments,
      outputType := fieldDefinition.outputType,
      selectionSet := subselections
    }
  have htailValid :
      Validation.selectionSetValid schema variableDefinitions parentType rest :=
    Validation.selectionSetValid_tail hvalid
  have hoverlapSelf :
      schema.objectType parentType ->
        schema.typesOverlapBool parentType parentType = true := by
    intro hparentObject
    exact object_typesOverlapBool_self schema hparentObject
  have hheadMem :
      headScoped ∈ FieldMerge.collectFields schema parentType
        (headSelection :: rest) := by
    simp [headScoped, headSelection, FieldMerge.collectFields, hlookup]
  have hscopedOf :
      ∀ selection, selection ∈ group ->
        ∃ scopedField,
          scopedField ∈ FieldMerge.collectFields schema parentType
            (headSelection :: rest)
            ∧ scopedField.responseName = responseName
            ∧ scopedField.selectionSet = selection.subselections
            ∧ (schema.objectType scopedField.parentType ->
              schema.typesOverlapBool parentType scopedField.parentType =
                true) := by
    intro selection hselection
    rcases List.mem_cons.mp hselection with hhead | hmatched
    · subst selection
      exact ⟨headScoped, hheadMem, rfl, by
        simp [headScoped, headSelection, Selection.subselections],
        by
          intro _hscopedObject
          simp [headScoped]
          exact object_typesOverlapBool_self schema hobject⟩
    · rcases
        fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName
          rest selection hmatched with
        ⟨matchedFieldName, matchedArguments, matchedDirectives,
          matchedSubselections, hselectionEq⟩
      subst selection
      rcases
        fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped
          schema variableDefinitions parentType parentType responseName rest
          matchedFieldName matchedArguments matchedDirectives
          matchedSubselections hoverlapSelf htailValid
          hmatched with
        ⟨scopedField, hscopedRest, hresponse, _hfieldName,
          _harguments, hselectionSet, hoverlap⟩
      have hscoped :
          scopedField ∈ FieldMerge.collectFields schema parentType
            (headSelection :: rest) := by
        simp [headSelection, FieldMerge.collectFields, hlookup,
          hscopedRest]
      exact ⟨scopedField, hscoped, hresponse, by
        simpa [Selection.subselections] using hselectionSet, hoverlap⟩
  have hgroupMerge :
      FieldMerge.fieldsInSetCanMerge schema objectType
        (mergeSelectionSets group) := by
    apply fieldsInSetCanMerge_mergeSelectionSets_of_pairwise
    intro leftSelection hleftSelection rightSelection hrightSelection
    rcases hscopedOf leftSelection hleftSelection with
      ⟨leftScoped, hleftScoped, hleftResponse, hleftSelectionSet,
        hleftOverlap⟩
    rcases hscopedOf rightSelection hrightSelection with
      ⟨rightScoped, hrightScoped, hrightResponse, hrightSelectionSet,
        hrightOverlap⟩
    have hresponse :
        leftScoped.responseName = rightScoped.responseName :=
      hleftResponse.trans hrightResponse.symm
    have hfieldMerge :
        FieldMerge.fieldsForNameCanMerge schema leftScoped rightScoped :=
      FieldMerge.fieldsInSetCanMerge_pair hmerge hleftScoped hrightScoped
        hresponse
    have hparents :
        leftScoped.parentType = rightScoped.parentType
          ∨ ¬ schema.objectType leftScoped.parentType
          ∨ ¬ schema.objectType rightScoped.parentType := by
      by_cases hleftObject : schema.objectType leftScoped.parentType
      · by_cases hrightObject : schema.objectType rightScoped.parentType
        · have hleftParent :
              leftScoped.parentType = parentType :=
            object_typesOverlapBool_eq schema hobject hleftObject
              (hleftOverlap hleftObject)
          have hrightParent :
              rightScoped.parentType = parentType :=
            object_typesOverlapBool_eq schema hobject hrightObject
              (hrightOverlap hrightObject)
          exact Or.inl (hleftParent.trans hrightParent.symm)
        · exact Or.inr (Or.inr hrightObject)
      · exact Or.inr (Or.inl hleftObject)
    have hsubfields :=
      FieldMerge.fieldsForNameCanMerge_subfields hfieldMerge hparents
        objectType
    rw [hleftSelectionSet, hrightSelectionSet] at hsubfields
    exact hsubfields
  simpa [group, headSelection, matching, mergeSelectionSets,
    Selection.subselections] using hgroupMerge

theorem fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    : schema.objectType parentType
      -> Validation.selectionSetValid schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> matchedFieldName = fieldName := by
  intro hobject hvalid hmerge matchedFieldName matchedArguments
    matchedDirectives matchedSubselections hmatched
  rcases Validation.selectionSetValid_field_head_lookup hvalid with
    ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
  let headScoped : FieldMerge.ScopedField := {
    parentType := parentType,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    outputType := fieldDefinition.outputType,
    selectionSet := subselections
  }
  have hheadMem :
      headScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simp [headScoped, FieldMerge.collectFields, hlookup]
  have htailValid :
      Validation.selectionSetValid schema variableDefinitions parentType rest :=
    Validation.selectionSetValid_tail hvalid
  rcases
      fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped schema
        variableDefinitions parentType parentType responseName rest
        matchedFieldName matchedArguments matchedDirectives
        matchedSubselections
        (fun _hobject => object_typesOverlapBool_self schema hobject)
        htailValid hmatched with
    ⟨matchedScoped, hmatchedMemRest, hmatchedResponse, hmatchedField,
      _hmatchedArguments, _hmatchedSelectionSet, hmatchedOverlap⟩
  have hmatchedMem :
      matchedScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simpa [FieldMerge.collectFields, hlookup] using Or.inr hmatchedMemRest
  have hresponse :
      headScoped.responseName = matchedScoped.responseName := by
    simp [headScoped, hmatchedResponse]
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema headScoped matchedScoped :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hheadMem hmatchedMem
      hresponse
  have hparents :
      headScoped.parentType = matchedScoped.parentType
        ∨ ¬ schema.objectType headScoped.parentType
        ∨ ¬ schema.objectType matchedScoped.parentType := by
    by_cases hmatchedObject : schema.objectType matchedScoped.parentType
    · have hoverlap := hmatchedOverlap hmatchedObject
      have hmatchedParent :
          matchedScoped.parentType = parentType :=
        object_typesOverlapBool_eq schema hobject hmatchedObject hoverlap
      exact Or.inl (by simp [headScoped, hmatchedParent])
    · exact Or.inr (Or.inr hmatchedObject)
  have hidentity :=
    FieldMerge.fieldsForNameCanMerge_identity hfieldMerge hparents
  have hheadField : headScoped.fieldName = fieldName := by
    rfl
  exact hmatchedField.symm.trans (hidentity.1.symm.trans hheadField)

theorem fieldSelectionsWithResponseNameInScope_matching_field_shape_of_canMerge_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    : schema.objectType parentType
      -> Validation.selectionSetValid schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> ∀ selection,
          selection
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> ∃ matchedArguments matchedDirectives matchedSubselections,
              selection
              = Selection.field responseName fieldName matchedArguments
                  matchedDirectives matchedSubselections := by
  intro hobject hvalid hmerge selection hselection
  rcases fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName
      rest selection hselection with
    ⟨matchedFieldName, matchedArguments, matchedDirectives,
      matchedSubselections, hselectionEq⟩
  subst selection
  have hsame :=
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object
      schema variableDefinitions parentType responseName fieldName arguments
      subselections rest hobject hvalid hmerge matchedFieldName
      matchedArguments matchedDirectives matchedSubselections hselection
  subst matchedFieldName
  exact ⟨matchedArguments, matchedDirectives, matchedSubselections, rfl⟩

theorem selectionSetValid_fieldHead_merged_of_matching
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName childType : Name)
    (_arguments : List Argument) (subselections rest : List Selection)
    : Validation.selectionSetValid schema variableDefinitions childType subselections
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
            -> Validation.selectionSetValid schema variableDefinitions childType
                matchedSubselections)
      -> Validation.selectionSetValid schema variableDefinitions childType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hhead hshape hmatching
  apply Validation.selectionSetValid_append hhead
  apply selectionSetValid_mergeSelectionSets_of_field_subselections
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

end NormalForm

end GraphQL
