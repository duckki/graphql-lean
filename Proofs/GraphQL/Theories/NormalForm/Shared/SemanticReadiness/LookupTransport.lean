import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness.Readiness

/-! Lookup and merge transport facts for semantic readiness. -/

namespace GraphQL

namespace NormalForm

theorem selectionSetLookupValid_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName : Name)
    : ∀ parentType selectionSet,
        selectionSetLookupValid schema parentType selectionSet
        -> selectionSetLookupValid schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | _parentType, [], _hvalid => by
      simp [withoutFieldSelectionsWithResponseName, selectionSetLookupValid]
  | parentType, selection :: rest, hvalid => by
      have hhead :
          selectionLookupValid schema parentType selection := by
        unfold selectionSetLookupValid at hvalid
        exact hvalid selection (by simp)
      have htail :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hvalid
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname]
            simpa [selectionSetLookupValid] using
              selectionSetLookupValid_withoutFieldSelectionsWithResponseName
                schema responseName parentType rest htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse,
              selectionSetLookupValid]
            constructor
            · exact hhead
            · simpa [selectionSetLookupValid] using
                selectionSetLookupValid_withoutFieldSelectionsWithResponseName
                  schema responseName parentType rest htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [withoutFieldSelectionsWithResponseName,
                selectionSetLookupValid, selectionLookupValid]
              constructor
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldSelectionsWithResponseName
                    schema responseName parentType selectionSet
                    (by simpa [selectionLookupValid] using hhead)
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldSelectionsWithResponseName
                    schema responseName parentType rest htail
          | some typeCondition =>
              simp [withoutFieldSelectionsWithResponseName,
                selectionSetLookupValid, selectionLookupValid]
              constructor
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldSelectionsWithResponseName
                    schema responseName typeCondition selectionSet
                    (by simpa [selectionLookupValid] using hhead)
              · simpa [selectionSetLookupValid] using
                  selectionSetLookupValid_withoutFieldSelectionsWithResponseName
                    schema responseName parentType rest htail

theorem fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
    (schema : Schema) (filterParent collectParent responseName : Name)
    : ∀ selectionSet fieldName arguments directives subselections,
        (schema.objectType collectParent
          -> schema.typesOverlapBool filterParent collectParent = true)
        -> selectionSetLookupValid schema collectParent selectionSet
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
      _hlookupValid, hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | selection :: rest, fieldName, arguments, directives, subselections,
      hoverlapScope, hlookupValid, hfield => by
      have hheadLookup :
          selectionLookupValid schema collectParent selection := by
        unfold selectionSetLookupValid at hlookupValid
        exact hlookupValid selection (by simp)
      have htailLookup :
          selectionSetLookupValid schema collectParent rest :=
        selectionSetLookupValid_tail hlookupValid
      cases selection with
      | field selectionResponseName selectionFieldName selectionArguments
          selectionDirectives selectionSubselections =>
          simp [selectionLookupValid] at hheadLookup
          rcases hheadLookup with ⟨fieldDefinition, hlookup⟩
          by_cases hname : selectionResponseName == responseName
          · simp [fieldSelectionsWithResponseNameInScope, hname] at hfield
            rcases hfield with hfield | hfield
            · rcases hfield with
                ⟨hresponse, hfieldName, harguments, hdirectives,
                  hsubselections⟩
              subst selectionResponseName
              subst selectionFieldName
              subst selectionArguments
              subst selectionDirectives
              subst selectionSubselections
              refine ⟨{
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  outputType := fieldDefinition.outputType,
                  selectionSet := subselections
                }, ?_, rfl, rfl, rfl, rfl, ?_⟩
              simp [FieldMerge.collectFields, hlookup]
              simpa using hoverlapScope
            · rcases
                fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
                  schema filterParent collectParent responseName rest
                  fieldName arguments directives subselections hoverlapScope
                  htailLookup
                  hfield with
                ⟨scopedField, hscoped, hresponse, hfieldName,
                  harguments, hselectionSet, hscopedOverlap⟩
              refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                hselectionSet, hscopedOverlap⟩
              simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
          · have hfalse : (selectionResponseName == responseName) = false := by
              cases hmatch : selectionResponseName == responseName
              · rfl
              · exact False.elim (hname hmatch)
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            rcases
              fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
                schema filterParent collectParent responseName rest
                fieldName arguments directives subselections hoverlapScope
                htailLookup hfield
              with
                ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
            refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
              hselectionSet, hscopedOverlap⟩
            simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
      | inlineFragment typeCondition selectionDirectives selectionSet =>
          cases typeCondition with
          | none =>
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              simp [selectionLookupValid] at hheadLookup
              rcases hfield with hfield | hfield
              · rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
                    schema filterParent collectParent responseName selectionSet
                    fieldName arguments directives subselections hoverlapScope
                    hheadLookup
                    hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]
              · rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
                    schema filterParent collectParent responseName rest
                    fieldName arguments directives subselections hoverlapScope
                    htailLookup
                    hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool filterParent typeCondition = true
              · simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                simp [selectionLookupValid] at hheadLookup
                rcases hfield with hfield | hfield
                · rcases
                    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
                      schema filterParent typeCondition responseName
                      selectionSet fieldName arguments directives
                      subselections (fun _hobject => hoverlap) hheadLookup
                      hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName,
                      harguments, hselectionSet, hscopedOverlap⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases
                    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
                      schema filterParent collectParent responseName rest
                      fieldName arguments directives subselections
                      hoverlapScope htailLookup hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName,
                      harguments, hselectionSet, hscopedOverlap⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                  simp [FieldMerge.collectFields, hscoped]
              · have hfalse :
                    schema.typesOverlapBool filterParent typeCondition =
                      false := by
                    cases hmatch :
                        schema.typesOverlapBool filterParent typeCondition
                    · rfl
                    · exact False.elim (hoverlap hmatch)
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
                    schema filterParent collectParent responseName rest
                    fieldName arguments directives subselections hoverlapScope
                    htailLookup hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                    hselectionSet, hscopedOverlap⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedOverlap⟩
                simp [FieldMerge.collectFields, hscoped]

theorem fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
    (schema : Schema)
    (parentType responseName fieldName objectType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> FieldMerge.fieldsInSetCanMerge schema objectType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hobject hlookupValid hmerge hlookup
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
  have htailLookup :
      selectionSetLookupValid schema parentType rest :=
    selectionSetLookupValid_tail hlookupValid
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
        fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
          schema parentType parentType responseName rest matchedFieldName
          matchedArguments matchedDirectives matchedSubselections
          hoverlapSelf htailLookup hmatched with
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

theorem
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> matchedFieldName = fieldName := by
  intro hobject hlookupValid hmerge matchedFieldName matchedArguments
    matchedDirectives matchedSubselections hmatched
  have hheadLookup :
      selectionLookupValid schema parentType
        (Selection.field responseName fieldName arguments [] subselections) := by
    unfold selectionSetLookupValid at hlookupValid
    exact hlookupValid _ (by simp)
  simp [selectionLookupValid] at hheadLookup
  rcases hheadLookup with ⟨fieldDefinition, hlookup⟩
  let headScoped : FieldMerge.ScopedField :=
    {
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
  have htailLookup :
      selectionSetLookupValid schema parentType rest :=
    selectionSetLookupValid_tail hlookupValid
  rcases
    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
      schema parentType parentType responseName rest matchedFieldName
      matchedArguments matchedDirectives matchedSubselections
      (fun hobject => object_typesOverlapBool_self schema hobject)
      htailLookup hmatched with
    ⟨matchedScoped, hmatchedMemRest, hmatchedResponse,
      hmatchedField, _hmatchedArguments, _hmatchedSelectionSet,
      hmatchedOverlap⟩
  have hmatchedMem :
      matchedScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simpa [FieldMerge.collectFields, hlookup] using Or.inr hmatchedMemRest
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema headScoped matchedScoped :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hheadMem hmatchedMem
      (by simpa [headScoped] using hmatchedResponse.symm)
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

theorem
    fieldSelectionsWithResponseNameInScope_matching_field_shape_of_canMerge_object_lookupValid
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
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
  intro hobject hlookupValid hmerge selection hselection
  rcases fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName
      rest selection hselection with
    ⟨matchedFieldName, matchedArguments, matchedDirectives,
      matchedSubselections, hselectionEq⟩
  subst selection
  have hsame :=
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hselection
  subst matchedFieldName
  exact ⟨matchedArguments, matchedDirectives, matchedSubselections, rfl⟩

theorem
    fieldSelectionsWithResponseNameInScope_matching_subselections_lookupValid_of_child_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName runtimeType : Name) (arguments : List Argument)
    (subselections rest : List Selection) (fieldDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.objectType parentType
      -> Validation.selectionSetValid schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> selectionSetLookupValid schema runtimeType matchedSubselections := by
  intro hschema hobject hvalid hmerge hlookup hinclude matchedFieldName
    matchedArguments matchedDirectives matchedSubselections hmatched
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
    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_source_object
      schema variableDefinitions parentType parentType responseName rest
      matchedFieldName matchedArguments matchedDirectives matchedSubselections
      (fun hobject => object_typeIncludesObjectBool_self schema hobject)
      htailValid hmatched with
    ⟨matchedScoped, hmatchedMemRest, hmatchedResponse, hmatchedField,
      _hmatchedArguments, hmatchedSelectionSet, hmatchedSource⟩
  have hmatchedMem :
      matchedScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simpa [FieldMerge.collectFields, hlookup] using Or.inr hmatchedMemRest
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema headScoped matchedScoped :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hheadMem hmatchedMem
      (by simpa [headScoped] using hmatchedResponse.symm)
  have hparents :
      headScoped.parentType = matchedScoped.parentType
        ∨ ¬ schema.objectType headScoped.parentType
        ∨ ¬ schema.objectType matchedScoped.parentType := by
    by_cases hmatchedObject : schema.objectType matchedScoped.parentType
    · have hsource := hmatchedSource hobject
      have hparentEq :
          parentType = matchedScoped.parentType :=
        object_typeIncludesObjectBool_eq_self schema hmatchedObject hsource
      exact Or.inl (by simp [headScoped, hparentEq])
    · exact Or.inr (Or.inr hmatchedObject)
  have hidentity :=
    FieldMerge.fieldsForNameCanMerge_identity hfieldMerge hparents
  have hmatchedFieldName :
      matchedFieldName = fieldName := by
    have hsame : headScoped.fieldName = matchedScoped.fieldName :=
      hidentity.1
    exact hmatchedField.symm.trans (hsame.symm.trans (by rfl))
  rcases
    collectFields_scoped_mem_fieldSelectionSetValid schema variableDefinitions
      parentType rest matchedScoped htailValid hmatchedMemRest with
    ⟨matchedDefinition, hmatchedLookup, hmatchedOutput,
      hmatchedChild⟩
  have hmatchedPossible :
      runtimeType ∈
        schema.getPossibleTypes matchedDefinition.outputType.namedType := by
    by_cases hmatchedObject : schema.objectType matchedScoped.parentType
    · have hsource := hmatchedSource hobject
      have hparentEq :
          parentType = matchedScoped.parentType :=
        object_typeIncludesObjectBool_eq_self schema hmatchedObject hsource
      have hlookupEq :
          matchedDefinition = fieldDefinition := by
        have hlookup' :
            schema.lookupField parentType fieldName = some matchedDefinition := by
          simpa [hparentEq, hmatchedFieldName, hmatchedField] using
            hmatchedLookup
        rw [hlookup] at hlookup'
        cases hlookup'
        rfl
      subst matchedDefinition
      exact List.contains_iff_mem.mp hinclude
    · have hmatchedFieldEq : matchedScoped.fieldName = fieldName := by
        simpa [hmatchedFieldName] using hmatchedField
      have himplementationLookup :
          schema.lookupField parentType matchedScoped.fieldName =
            some fieldDefinition := by
        simpa [hmatchedFieldEq] using hlookup
      have hpossibleParent :
          parentType ∈ schema.getPossibleTypes matchedScoped.parentType :=
        List.contains_iff_mem.mp (hmatchedSource hobject)
      have hsubtype :
          schema.outputTypeSubtype fieldDefinition.outputType
            matchedDefinition.outputType :=
        SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
          hschema hpossibleParent hmatchedLookup himplementationLookup
      have hmatchedInclude :
          schema.typeIncludesObjectBool matchedDefinition.outputType.namedType
            runtimeType = true :=
        typeIncludesObjectBool_of_outputTypeSubtype_namedType schema hsubtype
          hinclude
      exact List.contains_iff_mem.mp hmatchedInclude
  have hmatchedSelectionValid :
      Validation.selectionSetValid schema variableDefinitions
        matchedDefinition.outputType.namedType matchedSubselections := by
    have hchild :
        Validation.fieldSelectionSetValid schema variableDefinitions
          matchedDefinition matchedSubselections := by
      simpa [hmatchedSelectionSet, hmatchedOutput] using hmatchedChild
    exact fieldSelectionSetValid_child_of_possibleType hchild
      hmatchedPossible
  exact selectionSetLookupValid_of_selectionSetValid_possibleObject schema
    variableDefinitions matchedDefinition.outputType.namedType runtimeType
    hschema hmatchedPossible matchedSubselections hmatchedSelectionValid

theorem
    fieldSelectionsWithResponseNameInScope_matching_subselections_semanticsReady_of_child_object
    (schema : Schema) (parentType responseName fieldName runtimeType : Name)
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
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> selectionSetSemanticsReady schema runtimeType matchedSubselections := by
  intro hobject hready hlookupValid hmerge hlookup hinclude
    matchedFieldName matchedArguments matchedDirectives matchedSubselections
    hmatched
  have htailReady :
      selectionSetSemanticsReady schema parentType rest :=
    selectionSetSemanticsReady_tail hready
  rcases
    fieldSelectionsWithResponseNameInScope_field_semanticsReady schema parentType
      responseName rest matchedFieldName matchedArguments matchedDirectives
      matchedSubselections htailReady hmatched with
    ⟨matchedDefinition, hmatchedLookup, hmatchedReady⟩
  have hsame :
      matchedFieldName = fieldName :=
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  subst matchedFieldName
  have hdefinitionEq : matchedDefinition = fieldDefinition := by
    rw [hlookup] at hmatchedLookup
    cases hmatchedLookup
    rfl
  subst matchedDefinition
  exact hmatchedReady runtimeType hinclude

end NormalForm

end GraphQL
