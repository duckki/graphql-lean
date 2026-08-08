import Proofs.GraphQL.Theories.NormalForm.Shared.LookupValidity
import Proofs.GraphQL.Theories.NormalForm.Shared.FieldMerge

/-!
Field-merge lookup bridge facts shared by NormalForm proof families.
-/

namespace GraphQL

namespace NormalForm

theorem fieldMerge_collectFields_mem_outputType (schema : Schema)
    : ∀ parentType selectionSet scopedField,
        SchemaWellFormedness.schemaWellFormed schema
        -> selectionSetLookupValid schema parentType selectionSet
        -> scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
        -> scopedField.outputType.isOutputType schema
  | _parentType, [], _scopedField, _hschema, _hvalid, hfield => by
      simp [FieldMerge.collectFields] at hfield
  | parentType, selection :: rest, scopedField, hschema, hvalid, hfield => by
      have htailValid :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hvalid
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              exact fieldMerge_collectFields_mem_outputType schema parentType
                rest scopedField hschema htailValid hfield
          | some fieldDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              rcases hfield with hhead | htail
              · subst scopedField
                exact
                  SchemaWellFormedness.schemaWellFormed_lookupField_outputType
                    hschema hlookup
              · exact fieldMerge_collectFields_mem_outputType schema
                  parentType rest scopedField hschema htailValid htail
      | inlineFragment typeCondition directives selectionSet =>
          have hheadValid :
              selectionLookupValid schema parentType
                (Selection.inlineFragment typeCondition directives
                  selectionSet) :=
            selectionSetLookupValid_head hvalid
          cases typeCondition with
          | none =>
              have hselectionValid :
                  selectionSetLookupValid schema parentType selectionSet := by
                simpa [selectionLookupValid] using hheadValid
              simp [FieldMerge.collectFields] at hfield
              rcases hfield with hselection | hrest
              · exact fieldMerge_collectFields_mem_outputType schema
                  parentType selectionSet scopedField hschema
                  hselectionValid hselection
              · exact fieldMerge_collectFields_mem_outputType schema
                  parentType rest scopedField hschema htailValid hrest
          | some typeCondition =>
              have hselectionValid :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hheadValid
              simp [FieldMerge.collectFields] at hfield
              rcases hfield with hselection | hrest
              · exact fieldMerge_collectFields_mem_outputType schema
                  typeCondition selectionSet scopedField hschema
                  hselectionValid hselection
              · exact fieldMerge_collectFields_mem_outputType schema
                  parentType rest scopedField hschema htailValid hrest

theorem fieldMerge_collectFields_mem_lookupField_outputType (schema : Schema)
    : ∀ parentType selectionSet scopedField,
        scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
        -> ∃ fieldDefinition,
            schema.lookupField scopedField.parentType scopedField.fieldName
              = some fieldDefinition
            ∧ scopedField.outputType = fieldDefinition.outputType
  | _parentType, [], _scopedField, hfield => by
      simp [FieldMerge.collectFields] at hfield
  | parentType, selection :: rest, scopedField, hfield => by
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              exact
                fieldMerge_collectFields_mem_lookupField_outputType schema
                  parentType rest scopedField hfield
          | some fieldDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              rcases hfield with hhead | htail
              · subst scopedField
                exact ⟨fieldDefinition, by simp [hlookup]⟩
              · exact
                  fieldMerge_collectFields_mem_lookupField_outputType schema
                    parentType rest scopedField htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [FieldMerge.collectFields] at hfield
              rcases hfield with hselection | hrest
              · exact
                  fieldMerge_collectFields_mem_lookupField_outputType schema
                    parentType selectionSet scopedField hselection
              · exact
                  fieldMerge_collectFields_mem_lookupField_outputType schema
                    parentType rest scopedField hrest
          | some typeCondition =>
              simp [FieldMerge.collectFields] at hfield
              rcases hfield with hselection | hrest
              · exact
                  fieldMerge_collectFields_mem_lookupField_outputType schema
                    typeCondition selectionSet scopedField hselection
              · exact
                  fieldMerge_collectFields_mem_lookupField_outputType schema
                    parentType rest scopedField hrest

theorem fieldMerge_collectFields_outputType_eq_of_same_parent_field
    (schema : Schema)
    {leftParent rightParent : Name}
    {leftSet rightSet : List Selection}
    {left right : FieldMerge.ScopedField}
    : left ∈ FieldMerge.collectFields schema leftParent leftSet
      -> right ∈ FieldMerge.collectFields schema rightParent rightSet
      -> left.parentType = right.parentType
      -> left.fieldName = right.fieldName
      -> left.outputType = right.outputType := by
  intro hleft hright hparent hfield
  rcases
    fieldMerge_collectFields_mem_lookupField_outputType schema leftParent
      leftSet left hleft with
    ⟨leftDefinition, hleftLookup, hleftOutput⟩
  rcases
    fieldMerge_collectFields_mem_lookupField_outputType schema rightParent
      rightSet right hright with
    ⟨rightDefinition, hrightLookup, hrightOutput⟩
  have hsome : some leftDefinition = some rightDefinition := by
    calc
      some leftDefinition = schema.lookupField left.parentType left.fieldName :=
        hleftLookup.symm
      _ = schema.lookupField right.parentType right.fieldName := by
        simp [hparent, hfield]
      _ = some rightDefinition := hrightLookup
  injection hsome with hdefinitions
  simp [hleftOutput, hrightOutput, hdefinitions]

def scopedFieldSameSelection (left right : FieldMerge.ScopedField) : Prop :=
  left.responseName = right.responseName
  ∧ left.fieldName = right.fieldName
  ∧ left.arguments = right.arguments
  ∧ left.selectionSet = right.selectionSet

theorem scopedFieldSameSelection_refl (field : FieldMerge.ScopedField)
    : scopedFieldSameSelection field field := by
  simp [scopedFieldSameSelection]

theorem fieldMerge_collectFields_allFields_lookupParent_sameSelection (schema : Schema)
    : ∀ lookupParent collectParent selectionSet scopedField,
        selectionsAllFields selectionSet
        -> selectionSetLookupValid schema lookupParent selectionSet
        -> scopedField ∈ FieldMerge.collectFields schema collectParent selectionSet
        -> ∃ lookupField,
            lookupField ∈ FieldMerge.collectFields schema lookupParent selectionSet
            ∧ scopedFieldSameSelection scopedField lookupField
  | _lookupParent, _collectParent, [], _scopedField, _hallFields,
      _hlookupValid, hfield => by
      simp [FieldMerge.collectFields] at hfield
  | lookupParent, collectParent, selection :: rest, scopedField,
      hallFields, hlookupValid, hfield => by
      have hheadField : Selection.isField selection :=
        hallFields selection (by simp)
      have htailAll : selectionsAllFields rest := by
        intro candidate hcandidate
        exact hallFields candidate (by simp [hcandidate])
      have htailLookup :
          selectionSetLookupValid schema lookupParent rest :=
        selectionSetLookupValid_tail hlookupValid
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          have hheadLookup :
              selectionLookupValid schema lookupParent
                (Selection.field responseName fieldName arguments directives
                  selectionSet) :=
            selectionSetLookupValid_head hlookupValid
          rcases (by simpa [selectionLookupValid] using hheadLookup) with
            ⟨lookupDefinition, hlookup⟩
          cases hcollectLookup :
              schema.lookupField collectParent fieldName with
          | none =>
              simp [FieldMerge.collectFields, hcollectLookup] at hfield
              rcases
                fieldMerge_collectFields_allFields_lookupParent_sameSelection
                  schema lookupParent collectParent rest scopedField
                  htailAll htailLookup hfield with
                ⟨lookupField, hlookupField, hsame⟩
              exact ⟨lookupField,
                fieldMerge_collectFields_tail_mem schema lookupParent
                  (Selection.field responseName fieldName arguments
                    directives selectionSet)
                  rest lookupField hlookupField,
                hsame⟩
          | some collectDefinition =>
              simp [FieldMerge.collectFields, hcollectLookup] at hfield
              rcases hfield with hhead | htail
              · subst scopedField
                let lookupField : FieldMerge.ScopedField := {
                  parentType := lookupParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  outputType := lookupDefinition.outputType,
                  selectionSet := selectionSet
                }
                refine ⟨lookupField, ?_, ?_⟩
                · simp [lookupField, FieldMerge.collectFields, hlookup]
                · simp [lookupField, scopedFieldSameSelection]
              · rcases
                  fieldMerge_collectFields_allFields_lookupParent_sameSelection
                    schema lookupParent collectParent rest scopedField
                    htailAll htailLookup htail with
                  ⟨lookupField, hlookupField, hsame⟩
                exact ⟨lookupField,
                  fieldMerge_collectFields_tail_mem schema lookupParent
                    (Selection.field responseName fieldName arguments
                      directives selectionSet)
                    rest lookupField hlookupField,
                  hsame⟩
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

theorem possibleObjectParent_eq_or_abstract_not_object
    (schema : Schema) {objectParent abstractParent : Name}
    : objectParent ∈ schema.getPossibleTypes abstractParent
      -> abstractParent = objectParent ∨ ¬ schema.objectType abstractParent := by
  intro hpossible
  by_cases habstractObject : schema.objectType abstractParent
  · have hinclude :
        schema.typeIncludesObjectBool abstractParent objectParent = true :=
      List.contains_iff_mem.mpr hpossible
    have heq :
        objectParent = abstractParent :=
      object_typeIncludesObjectBool_eq_self schema habstractObject hinclude
    exact Or.inl heq.symm
  · exact Or.inr habstractObject

theorem fieldsForNameCanMerge_of_sameSelection_bridge
    (schema : Schema)
    (objectLeft objectRight abstractLeft abstractRight : FieldMerge.ScopedField)
    : scopedFieldSameSelection objectLeft abstractLeft
      -> scopedFieldSameSelection objectRight abstractRight
      -> FieldMerge.sameResponseShape schema objectLeft.outputType abstractLeft.outputType
      -> FieldMerge.sameResponseShape schema objectRight.outputType
          abstractRight.outputType
      -> (abstractLeft.parentType = objectLeft.parentType
          ∨ ¬ schema.objectType abstractLeft.parentType)
      -> (abstractRight.parentType = objectRight.parentType
          ∨ ¬ schema.objectType abstractRight.parentType)
      -> objectLeft.responseName = objectRight.responseName
      -> FieldMerge.fieldsForNameCanMerge schema abstractLeft abstractRight
      -> FieldMerge.fieldsForNameCanMerge schema objectLeft objectRight := by
  intro hleftSame hrightSame hleftShape hrightShape hleftParent
    hrightParent hresponse habstractMerge
  rcases hleftSame with
    ⟨hleftResponse, hleftField, hleftArguments, hleftSelectionSet⟩
  rcases hrightSame with
    ⟨hrightResponse, hrightField, hrightArguments, hrightSelectionSet⟩
  refine FieldMerge.FieldsForNameCanMerge.intro objectLeft objectRight ?_ ?_ ?_
  · have habstractShape :=
      FieldMerge.fieldsForNameCanMerge_sameResponseShape habstractMerge
    exact
      FieldMerge.sameResponseShape_trans schema objectLeft.outputType
        abstractLeft.outputType objectRight.outputType hleftShape
        (FieldMerge.sameResponseShape_trans schema abstractLeft.outputType
          abstractRight.outputType objectRight.outputType habstractShape
          (FieldMerge.sameResponseShape_symm schema objectRight.outputType
            abstractRight.outputType hrightShape))
  · intro hobjectParentCondition
    have habstractParentCondition :
        abstractLeft.parentType = abstractRight.parentType
          ∨ ¬ schema.objectType abstractLeft.parentType
          ∨ ¬ schema.objectType abstractRight.parentType := by
      rcases hleftParent with hleftParentEq | hleftNotObject
      · rcases hrightParent with hrightParentEq | hrightNotObject
        · rcases hobjectParentCondition with hobjectParentEq
            | hobjectNotObject
          · exact Or.inl
              (hleftParentEq.trans
                (hobjectParentEq.trans hrightParentEq.symm))
          · rcases hobjectNotObject with hobjectLeftNotObject
              | hobjectRightNotObject
            · exact Or.inr (Or.inl
                (by
                  intro habstractObject
                  exact hobjectLeftNotObject
                    (by simpa [hleftParentEq] using habstractObject)))
            · exact Or.inr (Or.inr
                (by
                  intro habstractObject
                  exact hobjectRightNotObject
                    (by simpa [hrightParentEq] using habstractObject)))
        · exact Or.inr (Or.inr hrightNotObject)
      · exact Or.inr (Or.inl hleftNotObject)
    rcases
      FieldMerge.fieldsForNameCanMerge_identity habstractMerge
        habstractParentCondition with
      ⟨habstractField, habstractArguments⟩
    have hfield :
        objectLeft.fieldName = objectRight.fieldName :=
      hleftField.trans (habstractField.trans hrightField.symm)
    have harguments :
        Argument.argumentsEquivalent objectLeft.arguments
          objectRight.arguments := by
      simpa [hleftArguments, hrightArguments] using habstractArguments
    exact ⟨hfield, harguments⟩
  · intro hobjectParentCondition objectType
    have habstractParentCondition :
        abstractLeft.parentType = abstractRight.parentType
          ∨ ¬ schema.objectType abstractLeft.parentType
          ∨ ¬ schema.objectType abstractRight.parentType := by
      rcases hleftParent with hleftParentEq | hleftNotObject
      · rcases hrightParent with hrightParentEq | hrightNotObject
        · rcases hobjectParentCondition with hobjectParentEq
            | hobjectNotObject
          · exact Or.inl
              (hleftParentEq.trans
                (hobjectParentEq.trans hrightParentEq.symm))
          · rcases hobjectNotObject with hobjectLeftNotObject
              | hobjectRightNotObject
            · exact Or.inr (Or.inl
                (by
                  intro habstractObject
                  exact hobjectLeftNotObject
                    (by simpa [hleftParentEq] using habstractObject)))
            · exact Or.inr (Or.inr
                (by
                  intro habstractObject
                  exact hobjectRightNotObject
                    (by simpa [hrightParentEq] using habstractObject)))
        · exact Or.inr (Or.inr hrightNotObject)
      · exact Or.inr (Or.inl hleftNotObject)
    have hsubfields :=
      FieldMerge.fieldsForNameCanMerge_subfields habstractMerge
        habstractParentCondition objectType
    simpa [FieldMerge.fieldsInSetCanMerge, hleftSelectionSet, hrightSelectionSet]
      using hsubfields

theorem fieldMerge_collectFields_objectParent_possibleParent (schema : Schema)
    : ∀ objectParent abstractParent selectionSet objectField,
        SchemaWellFormedness.schemaWellFormed schema
        -> schema.objectType objectParent
        -> objectParent ∈ schema.getPossibleTypes abstractParent
        -> selectionSetLookupValid schema objectParent selectionSet
        -> selectionSetLookupValid schema abstractParent selectionSet
        -> objectField ∈ FieldMerge.collectFields schema objectParent selectionSet
        -> ∃ abstractField,
            abstractField ∈ FieldMerge.collectFields schema abstractParent selectionSet
            ∧ scopedFieldSameSelection objectField abstractField
            ∧ FieldMerge.sameResponseShape schema
                objectField.outputType abstractField.outputType
            ∧ (abstractField.parentType = objectField.parentType
                ∨ ¬ schema.objectType abstractField.parentType)
  | _objectParent, _abstractParent, [], _objectField, _hschema, _hobject,
      _hpossible, _hvalidObject, _hvalidAbstract, hfield => by
      simp [FieldMerge.collectFields] at hfield
  | objectParent, abstractParent, selection :: rest, objectField, hschema,
      hobject, hpossible, hvalidObject, hvalidAbstract, hfield => by
      have htailObject :
          selectionSetLookupValid schema objectParent rest :=
        selectionSetLookupValid_tail hvalidObject
      have htailAbstract :
          selectionSetLookupValid schema abstractParent rest :=
        selectionSetLookupValid_tail hvalidAbstract
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          have hheadObject :
              selectionLookupValid schema objectParent
                (Selection.field responseName fieldName arguments directives
                  selectionSet) :=
            selectionSetLookupValid_head hvalidObject
          have hheadAbstract :
              selectionLookupValid schema abstractParent
                (Selection.field responseName fieldName arguments directives
                  selectionSet) :=
            selectionSetLookupValid_head hvalidAbstract
          rcases (by
            simpa [selectionLookupValid] using hheadAbstract) with
            ⟨abstractDefinition, habstractLookup⟩
          cases hlookup : schema.lookupField objectParent fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              rcases
                fieldMerge_collectFields_objectParent_possibleParent schema
                  objectParent abstractParent rest objectField hschema hobject
                  hpossible htailObject htailAbstract hfield with
                ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
              exact ⟨abstractField,
                fieldMerge_collectFields_tail_mem schema abstractParent
                  (Selection.field responseName fieldName arguments directives
                    selectionSet)
                  rest abstractField habstractMem,
                hsame, hshape, hparent⟩
          | some objectDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              rcases hfield with hhead | htail
              · subst objectField
                let abstractField : FieldMerge.ScopedField :=
                  {
                    parentType := abstractParent,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    outputType := abstractDefinition.outputType,
                    selectionSet := selectionSet
                  }
                refine ⟨abstractField, ?_, ?_, ?_, ?_⟩
                · simp [abstractField, FieldMerge.collectFields,
                    habstractLookup]
                · simp [scopedFieldSameSelection, abstractField]
                · exact
                    SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_sameResponseShape
                      hschema hpossible habstractLookup hlookup
                · rcases
                    possibleObjectParent_eq_or_abstract_not_object schema
                      hpossible with
                    heq | hnotObject
                  · exact Or.inl (by simp [abstractField, heq])
                  · exact Or.inr (by simpa [abstractField] using hnotObject)
              · rcases
                  fieldMerge_collectFields_objectParent_possibleParent schema
                    objectParent abstractParent rest objectField hschema
                    hobject hpossible htailObject htailAbstract htail with
                  ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
                exact ⟨abstractField,
                  fieldMerge_collectFields_tail_mem schema abstractParent
                    (Selection.field responseName fieldName arguments
                      directives selectionSet)
                    rest abstractField habstractMem,
                  hsame, hshape, hparent⟩
      | inlineFragment typeCondition directives selectionSet =>
          have hheadObject :
              selectionLookupValid schema objectParent
                (Selection.inlineFragment typeCondition directives
                  selectionSet) :=
            selectionSetLookupValid_head hvalidObject
          have hheadAbstract :
              selectionLookupValid schema abstractParent
                (Selection.inlineFragment typeCondition directives
                  selectionSet) :=
            selectionSetLookupValid_head hvalidAbstract
          cases typeCondition with
          | none =>
              have hselectionObject :
                  selectionSetLookupValid schema objectParent selectionSet := by
                simpa [selectionLookupValid] using hheadObject
              have hselectionAbstract :
                  selectionSetLookupValid schema abstractParent selectionSet := by
                simpa [selectionLookupValid] using hheadAbstract
              simp [FieldMerge.collectFields] at hfield
              rcases hfield with hselection | hrest
              · rcases
                  fieldMerge_collectFields_objectParent_possibleParent schema
                    objectParent abstractParent selectionSet objectField
                    hschema hobject hpossible hselectionObject
                    hselectionAbstract hselection with
                  ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
                exact ⟨abstractField, by
                  simp [FieldMerge.collectFields, habstractMem],
                  hsame, hshape, hparent⟩
              · rcases
                  fieldMerge_collectFields_objectParent_possibleParent schema
                    objectParent abstractParent rest objectField hschema
                    hobject hpossible htailObject htailAbstract hrest with
                  ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
                exact ⟨abstractField,
                  fieldMerge_collectFields_tail_mem schema abstractParent
                    (Selection.inlineFragment none directives selectionSet)
                    rest abstractField habstractMem,
                  hsame, hshape, hparent⟩
          | some typeCondition =>
              have hselectionLookup :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hheadObject
              simp [FieldMerge.collectFields] at hfield
              rcases hfield with hselection | hrest
              · refine ⟨objectField, ?_, ?_, ?_, ?_⟩
                · simp [FieldMerge.collectFields, hselection]
                · exact scopedFieldSameSelection_refl objectField
                · exact
                    FieldMerge.sameResponseShape_refl schema
                      objectField.outputType
                      (fieldMerge_collectFields_mem_outputType schema
                        typeCondition selectionSet objectField hschema
                        hselectionLookup hselection)
                · exact Or.inl rfl
              · rcases
                  fieldMerge_collectFields_objectParent_possibleParent schema
                    objectParent abstractParent rest objectField hschema
                    hobject hpossible htailObject htailAbstract hrest with
                  ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
                exact ⟨abstractField,
                  fieldMerge_collectFields_tail_mem schema abstractParent
                    (Selection.inlineFragment (some typeCondition) directives
                      selectionSet)
                    rest abstractField habstractMem,
                  hsame, hshape, hparent⟩

theorem fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
    (schema : Schema) (parentType typeCondition : Name)
    (selectionSet rest : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.objectType parentType
      -> schema.typesOverlapBool parentType typeCondition = true
      -> selectionSetLookupValid schema parentType selectionSet
      -> selectionSetLookupValid schema typeCondition selectionSet
      -> selectionSetLookupValid schema parentType rest
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType (selectionSet ++ rest) := by
  intro hschema hobject hoverlap hselectionParentLookup
    hselectionTypeLookup hrestLookup hmerge
  have hpossible :
      parentType ∈ schema.getPossibleTypes typeCondition :=
    List.contains_iff_mem.mp
      (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject
        hoverlap)
  have horiginalOf :
      ∀ objectField,
        objectField ∈ FieldMerge.collectFields schema parentType
          (selectionSet ++ rest) ->
          ∃ abstractField,
            abstractField ∈ FieldMerge.collectFields schema parentType
              (Selection.inlineFragment (some typeCondition) [] selectionSet
                :: rest)
              ∧ scopedFieldSameSelection objectField abstractField
              ∧ FieldMerge.sameResponseShape schema objectField.outputType
                abstractField.outputType
              ∧ (abstractField.parentType = objectField.parentType
                ∨ ¬ schema.objectType abstractField.parentType) := by
    intro objectField hfield
    rw [FieldMerge.collectFields_append] at hfield
    rcases List.mem_append.mp hfield with hselection | hrest
    · rcases
        fieldMerge_collectFields_objectParent_possibleParent schema
          parentType typeCondition selectionSet objectField hschema hobject
          hpossible hselectionParentLookup hselectionTypeLookup hselection with
        ⟨abstractField, habstractMem, hsame, hshape, hparent⟩
      have habstractOriginal :
          abstractField ∈ FieldMerge.collectFields schema parentType
            (Selection.inlineFragment (some typeCondition) [] selectionSet
              :: rest) := by
        simp [FieldMerge.collectFields, habstractMem]
      exact ⟨abstractField, habstractOriginal, hsame, hshape, hparent⟩
    · have hshape :
          FieldMerge.sameResponseShape schema objectField.outputType
            objectField.outputType :=
        FieldMerge.sameResponseShape_refl schema objectField.outputType
          (fieldMerge_collectFields_mem_outputType schema parentType rest
            objectField hschema hrestLookup hrest)
      exact ⟨objectField,
        fieldMerge_collectFields_tail_mem schema parentType
          (Selection.inlineFragment (some typeCondition) [] selectionSet)
          rest objectField hrest,
        scopedFieldSameSelection_refl objectField, hshape, Or.inl rfl⟩
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (selectionSet ++ rest) ?_
  dsimp
  intro left hleft right hright hresponse
  rcases horiginalOf left hleft with
    ⟨abstractLeft, habstractLeftMem, hleftSame, hleftShape,
      hleftParent⟩
  rcases horiginalOf right hright with
    ⟨abstractRight, habstractRightMem, hrightSame, hrightShape,
      hrightParent⟩
  have habstractResponse :
      abstractLeft.responseName = abstractRight.responseName := by
    exact hleftSame.1.symm.trans (hresponse.trans hrightSame.1)
  have habstractMerge :
      FieldMerge.fieldsForNameCanMerge schema abstractLeft abstractRight :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge habstractLeftMem
      habstractRightMem habstractResponse
  exact fieldsForNameCanMerge_of_sameSelection_bridge schema left right
    abstractLeft abstractRight hleftSame hrightSame hleftShape hrightShape
    hleftParent hrightParent hresponse habstractMerge

end NormalForm

end GraphQL
