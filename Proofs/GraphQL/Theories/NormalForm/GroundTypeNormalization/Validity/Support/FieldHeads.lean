import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Support.PossibleTypes

/-!
Field-head validity facts for ground-type normalization.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem fieldsInSetCanMerge_field_cons_of_lookup_none
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (selectionSet rest : List Selection)
    : schema.lookupField parentType fieldName = none
      -> FieldMerge.fieldsInSetCanMerge schema parentType rest
      -> FieldMerge.fieldsInSetCanMerge schema parentType (rest ++ rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
            (Selection.field responseName fieldName arguments [] selectionSet :: rest)
          ∧ FieldMerge.fieldsInSetCanMerge schema parentType
              ((Selection.field responseName fieldName arguments [] selectionSet :: rest)
                ++ (Selection.field responseName fieldName arguments [] selectionSet
                    :: rest)) := by
  intro hlookup hrestMerge hrestSelf
  constructor
  · unfold FieldMerge.fieldsInSetCanMerge
    refine FieldMerge.FieldsInSetCanMerge.intro parentType
      (Selection.field responseName fieldName arguments [] selectionSet
        :: rest) ?_
    dsimp
    intro left hleft right hright hresponse
    simp [FieldMerge.collectFields, hlookup] at hleft hright
    exact FieldMerge.fieldsInSetCanMerge_pair hrestMerge hleft hright
      hresponse
  · unfold FieldMerge.fieldsInSetCanMerge
    refine FieldMerge.FieldsInSetCanMerge.intro parentType
      ((Selection.field responseName fieldName arguments [] selectionSet
        :: rest)
        ++
        (Selection.field responseName fieldName arguments [] selectionSet
          :: rest)) ?_
    dsimp
    intro left hleft right hright hresponse
    simp [FieldMerge.collectFields, hlookup, FieldMerge.collectFields_append]
      at hleft hright
    exact FieldMerge.fieldsInSetCanMerge_pair hrestMerge hleft hright
      hresponse

theorem collectFields_responseName_ne_of_allFields_responseNameFree
    (schema : Schema) (parentType responseName : Name)
    : ∀ selectionSet scopedField,
        selectionsAllFields selectionSet
        -> selectionSetResponseNameFree schema parentType responseName selectionSet
        -> scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
        -> scopedField.responseName ≠ responseName
  | [], scopedField, _hallFields, _hfree, hmem => by
      simp [FieldMerge.collectFields] at hmem
  | selection :: rest, scopedField, hallFields, hfree, hmem => by
      have hheadField : Selection.isField selection :=
        hallFields selection (by simp)
      have htailAllFields : selectionsAllFields rest := by
        intro candidate hcandidate
        exact hallFields candidate (List.mem_cons_of_mem selection hcandidate)
      have htailFree :
          selectionSetResponseNameFree schema parentType responseName rest :=
        selectionSetResponseNameFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hheadFree :
              fieldResponseName ≠ responseName := by
            have hselectionFree := selectionSetResponseNameFree_head hfree
            simpa [selectionResponseNameFree] using hselectionFree
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hmem
              exact
                collectFields_responseName_ne_of_allFields_responseNameFree
                  schema parentType responseName rest scopedField
                  htailAllFields htailFree hmem
          | some fieldDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hmem
              rcases hmem with hhead | htail
              · subst scopedField
                exact hheadFree
              · exact
                  collectFields_responseName_ne_of_allFields_responseNameFree
                    schema parentType responseName rest scopedField
                    htailAllFields htailFree htail
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

theorem selectionSetResponseNameFree_of_allFields_anyParent
    (schema : Schema) (sourceParent targetParent responseName : Name)
    : ∀ selectionSet,
        selectionsAllFields selectionSet
        -> selectionSetResponseNameFree schema sourceParent responseName selectionSet
        -> selectionSetResponseNameFree schema targetParent responseName selectionSet
  | [], _hallFields, _hfree => by
      simp [selectionSetResponseNameFree]
  | selection :: rest, hallFields, hfree => by
      have hheadField : Selection.isField selection :=
        hallFields selection (by simp)
      have htailAllFields : selectionsAllFields rest := by
        intro candidate hcandidate
        exact hallFields candidate (List.mem_cons_of_mem selection hcandidate)
      have htailFree :
          selectionSetResponseNameFree schema sourceParent responseName rest :=
        selectionSetResponseNameFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hheadFree :=
            selectionSetResponseNameFree_head hfree
          simp [selectionSetResponseNameFree, selectionResponseNameFree]
          exact ⟨by
            simpa [selectionResponseNameFree] using hheadFree,
            by
              simpa [selectionSetResponseNameFree] using
                selectionSetResponseNameFree_of_allFields_anyParent schema
                  sourceParent targetParent responseName rest htailAllFields
                  htailFree⟩
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

theorem fieldsInSetCanMerge_field_cons_of_rest_responseNameFree
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> FieldMerge.sameResponseShape schema fieldDefinition.outputType
          fieldDefinition.outputType
      -> Argument.argumentsEquivalent arguments arguments
      -> (∀ objectType,
            FieldMerge.fieldsInSetCanMerge schema objectType
              (selectionSet ++ selectionSet))
      -> FieldMerge.fieldsInSetCanMerge schema parentType rest
      -> (∀ mergeParent, FieldMerge.fieldsInSetCanMerge schema mergeParent (rest ++ rest))
      -> selectionsAllFields rest
      -> selectionSetResponseNameFree schema parentType responseName rest
      -> FieldMerge.fieldsInSetCanMerge schema parentType
            (Selection.field responseName fieldName arguments [] selectionSet :: rest)
          ∧ ∀ mergeParent,
              FieldMerge.fieldsInSetCanMerge schema mergeParent
                ((Selection.field responseName fieldName arguments [] selectionSet
                    :: rest)
                  ++ (Selection.field responseName fieldName arguments [] selectionSet
                      :: rest)) := by
  intro hschema hlookup hshape harguments hchildSelf hrestMerge hrestSelf
    hallFields hfree
  let headScoped : FieldMerge.ScopedField := {
    parentType := parentType,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    outputType := fieldDefinition.outputType,
    selectionSet := selectionSet
  }
  have hheadMerge :
      FieldMerge.fieldsForNameCanMerge schema headScoped headScoped := by
    refine FieldMerge.FieldsForNameCanMerge.intro headScoped headScoped
      hshape ?_ ?_
    · intro _hparents
      exact ⟨rfl, harguments⟩
    · intro _hparents objectType
      simpa [FieldMerge.fieldsInSetCanMerge, headScoped]
        using hchildSelf objectType
  have hrestNoResponse :
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema parentType rest ->
          scopedField.responseName ≠ responseName :=
    fun scopedField hmem =>
      collectFields_responseName_ne_of_allFields_responseNameFree schema
        parentType responseName rest scopedField hallFields hfree hmem
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema parentType
        (Selection.field responseName fieldName arguments [] selectionSet
          :: rest) := by
    unfold FieldMerge.fieldsInSetCanMerge
    refine FieldMerge.FieldsInSetCanMerge.intro parentType
      (Selection.field responseName fieldName arguments [] selectionSet
        :: rest) ?_
    dsimp
    intro left hleft right hright hresponse
    simp [FieldMerge.collectFields, hlookup] at hleft hright
    rcases hleft with hleftHead | hleftRest
    · subst left
      rcases hright with hrightHead | hrightRest
      · subst right
        exact hheadMerge
      · exact False.elim ((hrestNoResponse right hrightRest)
          hresponse.symm)
    · rcases hright with hrightHead | hrightRest
      · subst right
        exact False.elim ((hrestNoResponse left hleftRest) hresponse)
      · exact FieldMerge.fieldsInSetCanMerge_pair hrestMerge hleftRest
          hrightRest hresponse
  have hself :
      ∀ mergeParent,
        FieldMerge.fieldsInSetCanMerge schema mergeParent
          ((Selection.field responseName fieldName arguments [] selectionSet
            :: rest)
            ++
            (Selection.field responseName fieldName arguments [] selectionSet
              :: rest)) := by
    intro mergeParent
    have hrestNoResponseForMerge :
        ∀ scopedField,
          scopedField ∈ FieldMerge.collectFields schema mergeParent rest ->
            scopedField.responseName ≠ responseName := by
      intro scopedField hmem
      exact collectFields_responseName_ne_of_allFields_responseNameFree schema
        mergeParent responseName rest scopedField hallFields
        (selectionSetResponseNameFree_of_allFields_anyParent schema
          parentType mergeParent responseName rest hallFields hfree)
        hmem
    cases hmergeLookup : schema.lookupField mergeParent fieldName with
    | none =>
        exact (fieldsInSetCanMerge_field_cons_of_lookup_none schema
          mergeParent responseName fieldName arguments selectionSet rest
          hmergeLookup
          (fieldsInSetCanMerge_append_left schema mergeParent rest rest
            (hrestSelf mergeParent))
          (hrestSelf mergeParent)).2
    | some mergeFieldDefinition =>
    have hheadMergeForMerge :
        FieldMerge.fieldsForNameCanMerge schema {
            parentType := mergeParent,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            outputType := mergeFieldDefinition.outputType,
            selectionSet := selectionSet
          } {
            parentType := mergeParent,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            outputType := mergeFieldDefinition.outputType,
            selectionSet := selectionSet
          } := by
      refine FieldMerge.FieldsForNameCanMerge.intro _ _ ?_ ?_ ?_
      · exact FieldMerge.sameResponseShape_refl schema
          mergeFieldDefinition.outputType
          (SchemaWellFormedness.schemaWellFormed_lookupField_outputType
            hschema hmergeLookup)
      · intro _hparents
        exact ⟨rfl, harguments⟩
      · intro _hparents objectType
        exact hchildSelf objectType
    unfold FieldMerge.fieldsInSetCanMerge
    refine FieldMerge.FieldsInSetCanMerge.intro mergeParent
      ((Selection.field responseName fieldName arguments [] selectionSet
        :: rest)
        ++
        (Selection.field responseName fieldName arguments [] selectionSet
          :: rest)) ?_
    dsimp
    intro left hleft right hright hresponse
    simp [FieldMerge.collectFields, hmergeLookup,
      FieldMerge.collectFields_append]
      at hleft hright
    rcases hleft with hleftHead | hleft
    · subst left
      rcases hright with hrightHead | hright
      · subst right
        exact hheadMergeForMerge
      · rcases hright with hrightRest | hrightHead
        · exact False.elim ((hrestNoResponseForMerge right hrightRest)
            hresponse.symm)
        · rcases hrightHead with hrightHead | hrightRest
          · subst right
            exact hheadMergeForMerge
          · exact False.elim ((hrestNoResponseForMerge right hrightRest)
              hresponse.symm)
    · rcases hleft with hleftRest | hleftHead
      · rcases hright with hrightHead | hright
        · subst right
          exact False.elim ((hrestNoResponseForMerge left hleftRest)
            hresponse)
        · rcases hright with hrightRest | hrightHead
          · exact FieldMerge.fieldsInSetCanMerge_pair (hrestSelf mergeParent)
              (by
                rw [FieldMerge.collectFields_append]
                exact List.mem_append_left
                  (FieldMerge.collectFields schema mergeParent rest)
                  hleftRest)
              (by
                rw [FieldMerge.collectFields_append]
                exact List.mem_append_left
                  (FieldMerge.collectFields schema mergeParent rest)
                  hrightRest)
              hresponse
          · rcases hrightHead with hrightHead | hrightRest
            · subst right
              exact False.elim ((hrestNoResponseForMerge left hleftRest)
                hresponse)
            · exact FieldMerge.fieldsInSetCanMerge_pair (hrestSelf mergeParent)
                (by
                  rw [FieldMerge.collectFields_append]
                  exact List.mem_append_left
                    (FieldMerge.collectFields schema mergeParent rest)
                    hleftRest)
                (by
                  rw [FieldMerge.collectFields_append]
                  exact List.mem_append_right
                    (FieldMerge.collectFields schema mergeParent rest)
                    hrightRest)
                hresponse
      · rcases hleftHead with hleftHead | hleftRest
        · subst left
          rcases hright with hrightHead | hright
          · subst right
            exact hheadMergeForMerge
          · rcases hright with hrightRest | hrightHead
            · exact False.elim ((hrestNoResponseForMerge right hrightRest)
                hresponse.symm)
            · rcases hrightHead with hrightHead | hrightRest
              · subst right
                exact hheadMergeForMerge
              · exact False.elim ((hrestNoResponseForMerge right hrightRest)
                  hresponse.symm)
        · rcases hright with hrightHead | hright
          · subst right
            exact False.elim ((hrestNoResponseForMerge left hleftRest)
              hresponse)
          · rcases hright with hrightRest | hrightHead
            · exact FieldMerge.fieldsInSetCanMerge_pair (hrestSelf mergeParent)
                (by
                  rw [FieldMerge.collectFields_append]
                  exact List.mem_append_right
                    (FieldMerge.collectFields schema mergeParent rest)
                    hleftRest)
                (by
                  rw [FieldMerge.collectFields_append]
                  exact List.mem_append_left
                    (FieldMerge.collectFields schema mergeParent rest)
                    hrightRest)
                hresponse
            · rcases hrightHead with hrightHead | hrightRest
              · subst right
                exact False.elim ((hrestNoResponseForMerge left hleftRest)
                  hresponse)
              · exact FieldMerge.fieldsInSetCanMerge_pair (hrestSelf mergeParent)
                  (by
                    rw [FieldMerge.collectFields_append]
                    exact List.mem_append_right
                      (FieldMerge.collectFields schema mergeParent rest)
                      hleftRest)
                  (by
                    rw [FieldMerge.collectFields_append]
                    exact List.mem_append_right
                      (FieldMerge.collectFields schema mergeParent rest)
                      hrightRest)
                  hresponse
  exact ⟨hmerge, hself⟩

theorem selectionValidInPossibleTypes_field_child
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {subselections : List Selection} {fieldDefinition : FieldDefinition}
    {childType : Name}
    : Validation.selectionValidInPossibleTypes schema variableDefinitions
        parentType
        (Selection.field responseName fieldName arguments directives subselections)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> childType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions childType subselections := by
  intro hvalid hlookup hchildType
  simp [Validation.selectionValidInPossibleTypes, hlookup] at hvalid
  exact hvalid.2 childType hchildType

theorem selectionSetLookupValid_of_fieldSelectionSetValid_namedType
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fieldDefinition : FieldDefinition} {selectionSet : List Selection}
    : Validation.fieldSelectionSetValid schema variableDefinitions
        fieldDefinition selectionSet
      -> selectionSetLookupValid schema fieldDefinition.outputType.namedType
          selectionSet := by
  intro hvalid
  simp [Validation.fieldSelectionSetValid] at hvalid
  rcases hvalid with ⟨_houtput, hchild⟩
  rcases hchild with hleaf | hcomposite
  · simpa [hleaf.2] using
      selectionSetLookupValid_nil schema
        fieldDefinition.outputType.namedType
  · exact selectionSetLookupValid_of_selectionSetValid selectionSet
      hcomposite.2.2

theorem fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName : Name)
    : schema.objectType parentType
      -> ∀ selectionSet,
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType selectionSet
          -> ∀ fieldName arguments directives subselections,
              Selection.field responseName fieldName arguments directives subselections
                ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
                    selectionSet
              -> Validation.selectionValidInPossibleTypes schema variableDefinitions
                  parentType
                  (Selection.field responseName fieldName arguments directives
                    subselections)
  | hobject, [], himplementation, fieldName, arguments, directives,
      subselections, hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | hobject, selection :: rest, himplementation, fieldName, arguments,
      directives, subselections, hfield => by
      have hheadImplementation :
          Validation.selectionValidInPossibleTypes schema variableDefinitions
            parentType selection :=
        selectionSetValidInPossibleTypes_head himplementation
      have htailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType rest :=
        selectionSetValidInPossibleTypes_tail himplementation
      cases selection with
      | field fieldResponseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · have hresponse : fieldResponseName = responseName :=
              beq_iff_eq.mp hname
            subst fieldResponseName
            simp [fieldSelectionsWithResponseNameInScope] at hfield
            rcases hfield with hhead | htail
            · rcases hhead with
                ⟨hfieldName, harguments, hdirectives, hsubselections⟩
              subst fieldName
              subst arguments
              subst directives
              subst subselections
              exact hheadImplementation
            · exact
                fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes
                  schema variableDefinitions parentType responseName hobject
                  rest htailImplementation fieldName arguments directives
                  subselections htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            exact
              fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes
                schema variableDefinitions parentType responseName hobject
                rest htailImplementation fieldName arguments directives
                subselections hfield
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hbodyImplementation :
                  Validation.selectionSetValidInPossibleTypes schema
                    variableDefinitions parentType selectionSet := by
                have hparentPossible :
                    parentType ∈ schema.getPossibleTypes parentType :=
                  List.contains_iff_mem.mp
                    (object_typeIncludesObjectBool_self schema hobject)
                simpa [Validation.selectionValidInPossibleTypes] using
                  hheadImplementation parentType hparentPossible
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hbody | htail
              · exact
                  fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes
                    schema variableDefinitions parentType responseName
                    hobject selectionSet hbodyImplementation fieldName
                    arguments directives subselections hbody
              · exact
                  fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes
                    schema variableDefinitions parentType responseName
                    hobject rest htailImplementation fieldName arguments
                    directives subselections htail
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · have hfragment :
                    ∀ objectType,
                      objectType ∈ schema.getPossibleTypes typeCondition ->
                        Validation.selectionSetValidInPossibleTypes
                          schema variableDefinitions objectType
                          selectionSet := by
                  simpa [Validation.selectionValidInPossibleTypes] using
                    hheadImplementation hoverlap
                have hparentPossible :
                    parentType ∈ schema.getPossibleTypes typeCondition :=
                  List.contains_iff_mem.mp
                    (typeIncludesObjectBool_of_object_typesOverlapBool schema
                  hobject hoverlap)
                have hbodyImplementation :
                    Validation.selectionSetValidInPossibleTypes schema
                      variableDefinitions parentType selectionSet :=
                  hfragment parentType hparentPossible
                simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                rcases hfield with hbody | htail
                · exact
                    fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes
                      schema variableDefinitions parentType responseName
                      hobject selectionSet hbodyImplementation fieldName
                      arguments directives subselections hbody
                · exact
                    fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes
                      schema variableDefinitions parentType responseName
                      hobject rest htailImplementation fieldName arguments
                      directives subselections htail
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                exact
                  fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes
                    schema variableDefinitions parentType responseName
                    hobject rest htailImplementation fieldName arguments
                    directives subselections hfield

theorem fieldSelectionsWithResponseNameInScope_matching_subselections_validInPossibleTypes_of_child_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName runtimeType : Name) (arguments : List Argument)
    (subselections rest : List Selection) (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType
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
          -> Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions runtimeType matchedSubselections := by
  intro hobject hlookupValid himplementation hmerge hlookup hinclude
    matchedFieldName matchedArguments matchedDirectives matchedSubselections
    hmatched
  have htailImplementation :
      Validation.selectionSetValidInPossibleTypes schema
        variableDefinitions parentType rest :=
    selectionSetValidInPossibleTypes_tail himplementation
  have hmatchedImplementation :
      Validation.selectionValidInPossibleTypes schema variableDefinitions
        parentType
        (Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections) :=
    fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes
      schema variableDefinitions parentType responseName hobject rest
      htailImplementation matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  have hsame :
      matchedFieldName = fieldName :=
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  subst matchedFieldName
  simp [Validation.selectionValidInPossibleTypes] at hmatchedImplementation
  rcases hmatchedImplementation with
    ⟨hmatchedSelection, hmatchedBody⟩
  rcases Validation.selectionValid_field_lookup hmatchedSelection with
    ⟨matchedDefinition, hmatchedLookup, _hmatchedArguments,
      _hmatchedSelectionSet⟩
  rw [hmatchedLookup] at hmatchedBody
  have hdefinitionEq : matchedDefinition = fieldDefinition := by
    rw [hlookup] at hmatchedLookup
    cases hmatchedLookup
    rfl
  subst matchedDefinition
  exact hmatchedBody runtimeType
    (List.contains_iff_mem.mp hinclude)

theorem fieldSelectionsWithResponseNameInScope_matching_subselections_lookupValid_of_returnType
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name) (arguments : List Argument)
    (subselections rest : List Selection) (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> selectionSetLookupValid schema
              fieldDefinition.outputType.namedType matchedSubselections := by
  intro hobject hlookupValid himplementation hmerge hlookup
    matchedFieldName matchedArguments matchedDirectives matchedSubselections
    hmatched
  have htailImplementation :
      Validation.selectionSetValidInPossibleTypes schema
        variableDefinitions parentType rest :=
    selectionSetValidInPossibleTypes_tail himplementation
  have hmatchedImplementation :
      Validation.selectionValidInPossibleTypes schema variableDefinitions
        parentType
        (Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections) :=
    fieldSelectionsWithResponseNameInScope_field_validInPossibleTypes
      schema variableDefinitions parentType responseName hobject rest
      htailImplementation matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  have hsame :
      matchedFieldName = fieldName :=
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  subst matchedFieldName
  simp [Validation.selectionValidInPossibleTypes] at hmatchedImplementation
  rcases hmatchedImplementation with
    ⟨hmatchedSelection, _hmatchedBody⟩
  rcases Validation.selectionValid_field_lookup hmatchedSelection with
    ⟨matchedDefinition, hmatchedLookup, _hmatchedArguments,
      hmatchedSelectionSet⟩
  have hdefinitionEq : matchedDefinition = fieldDefinition := by
    rw [hlookup] at hmatchedLookup
    cases hmatchedLookup
    rfl
  subst matchedDefinition
  exact selectionSetLookupValid_of_fieldSelectionSetValid_namedType
    hmatchedSelectionSet

theorem selectionSetLookupValid_fieldHead_merged_of_returnType
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> selectionSetLookupValid schema fieldDefinition.outputType.namedType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hobject hlookupValid himplementation hmerge hlookup
  have hheadImplementation :
      Validation.selectionValidInPossibleTypes schema variableDefinitions
        parentType
        (Selection.field responseName fieldName arguments []
          subselections) :=
    selectionSetValidInPossibleTypes_head himplementation
  simp [Validation.selectionValidInPossibleTypes, hlookup] at hheadImplementation
  rcases hheadImplementation with
    ⟨hheadSelection, _hheadBody⟩
  rcases Validation.selectionValid_field_lookup hheadSelection with
    ⟨headDefinition, hheadLookup, _harguments, hheadSelectionSet⟩
  have hdefinitionEq : headDefinition = fieldDefinition := by
    rw [hlookup] at hheadLookup
    cases hheadLookup
    rfl
  subst headDefinition
  apply selectionSetLookupValid_fieldHead_merged_of_matching schema
    parentType responseName fieldName fieldDefinition.outputType.namedType
    arguments subselections rest
  · exact selectionSetLookupValid_of_fieldSelectionSetValid_namedType
      hheadSelectionSet
  · exact
      fieldSelectionsWithResponseNameInScope_matching_field_shape_of_canMerge_object_lookupValid
        schema parentType responseName fieldName arguments subselections rest
        hobject hlookupValid hmerge
  · intro matchedArguments matchedDirectives matchedSubselections hmatched
    exact
      fieldSelectionsWithResponseNameInScope_matching_subselections_lookupValid_of_returnType
        schema variableDefinitions parentType responseName fieldName arguments
        subselections rest fieldDefinition hobject hlookupValid
        himplementation hmerge hlookup fieldName matchedArguments
        matchedDirectives matchedSubselections hmatched

theorem selectionSetValidInPossibleTypes_fieldHead_merged_of_child_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions runtimeType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hobject hlookupValid himplementation hmerge hlookup hinclude
  apply selectionSetValidInPossibleTypes_append
  · have hheadImplementation :
        Validation.selectionValidInPossibleTypes schema variableDefinitions
          parentType
          (Selection.field responseName fieldName arguments []
            subselections) :=
      selectionSetValidInPossibleTypes_head himplementation
    exact selectionValidInPossibleTypes_field_child
      hheadImplementation hlookup
      (List.contains_iff_mem.mp hinclude)
  · apply
      selectionSetValidInPossibleTypes_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    exact
      fieldSelectionsWithResponseNameInScope_matching_subselections_validInPossibleTypes_of_child_object
        schema variableDefinitions parentType responseName fieldName
        runtimeType arguments subselections rest fieldDefinition hobject
        hlookupValid himplementation hmerge hlookup hinclude
        matchedFieldName matchedArguments matchedDirectives
        matchedSubselections hmatched

end GroundTypeNormalization

end NormalForm

end GraphQL
