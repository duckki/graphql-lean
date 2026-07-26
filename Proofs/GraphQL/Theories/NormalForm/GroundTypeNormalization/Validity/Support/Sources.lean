import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Support.Basics

/-!
Normalized source tracking facts for ground-type normalization validity.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

structure NormalizedSelectionSetValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selectionSet : List Selection)
    : Prop where
  selectionSetValid
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
  validInPossibleTypes
    : Validation.selectionSetValidInPossibleTypes schema variableDefinitions
        parentType selectionSet
  fieldsCanMerge : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
  fieldsCanMergeSelf
    : ∀ mergeParent,
        FieldMerge.fieldsInSetCanMerge schema mergeParent (selectionSet ++ selectionSet)

def normalizedBranchesPairwiseMerge
    (schema : Schema) (possibleTypeNames : List Name)
    (selectionSet : List Selection)
    : Prop :=
  ∀ leftType,
    leftType ∈ possibleTypeNames
    -> ∀ rightType,
        rightType ∈ possibleTypeNames
        -> ∀ leftField,
            leftField
              ∈ FieldMerge.collectFields schema leftType
                  (normalizeSelectionSet schema leftType selectionSet)
            -> ∀ rightField,
                rightField
                  ∈ FieldMerge.collectFields schema rightType
                      (normalizeSelectionSet schema rightType selectionSet)
                -> leftField.responseName = rightField.responseName
                -> FieldMerge.fieldsForNameCanMerge schema leftField rightField

def normalizedDistinctBranchesPairwiseMerge
    (schema : Schema) (possibleTypeNames : List Name)
    (selectionSet : List Selection)
    : Prop :=
  ∀ leftType,
    leftType ∈ possibleTypeNames
    -> ∀ rightType,
        rightType ∈ possibleTypeNames
        -> leftType ≠ rightType
        -> ∀ leftField,
            leftField
              ∈ FieldMerge.collectFields schema leftType
                  (normalizeSelectionSet schema leftType selectionSet)
            -> ∀ rightField,
                rightField
                  ∈ FieldMerge.collectFields schema rightType
                      (normalizeSelectionSet schema rightType selectionSet)
                -> leftField.responseName = rightField.responseName
                -> FieldMerge.fieldsForNameCanMerge schema leftField rightField

theorem normalizedBranchFieldsCanMerge_of_normalizedValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {branchType : Name} {selectionSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    : NormalizedSelectionSetValid schema variableDefinitions branchType
        (normalizeSelectionSet schema branchType selectionSet)
      -> leftField
          ∈ FieldMerge.collectFields schema branchType
              (normalizeSelectionSet schema branchType selectionSet)
      -> rightField
          ∈ FieldMerge.collectFields schema branchType
              (normalizeSelectionSet schema branchType selectionSet)
      -> leftField.responseName = rightField.responseName
      -> FieldMerge.fieldsForNameCanMerge schema leftField rightField := by
  intro hvalid hleft hright hresponse
  exact FieldMerge.fieldsInSetCanMerge_pair hvalid.fieldsCanMerge
    hleft hright hresponse

theorem normalizedSelectionSetsPairFieldsCanMerge
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {leftSelectionSet rightSelectionSet : List Selection}
    : NormalizedSelectionSetValid schema variableDefinitions parentType leftSelectionSet
      -> NormalizedSelectionSetValid schema variableDefinitions parentType
          rightSelectionSet
      -> (∀ leftField,
            leftField ∈ FieldMerge.collectFields schema parentType leftSelectionSet
            -> ∀ rightField,
                rightField ∈ FieldMerge.collectFields schema parentType rightSelectionSet
                -> leftField.responseName = rightField.responseName
                -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (leftSelectionSet ++ rightSelectionSet) := by
  intro hleftValid hrightValid hcross
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (leftSelectionSet ++ rightSelectionSet) ?_
  dsimp
  intro left hleft right hright hresponse
  rw [FieldMerge.collectFields_append] at hleft hright
  rcases List.mem_append.mp hleft with hleftMem | hleftMem
  · rcases List.mem_append.mp hright with hrightMem | hrightMem
    · exact FieldMerge.fieldsInSetCanMerge_pair hleftValid.fieldsCanMerge
        hleftMem hrightMem hresponse
    · exact hcross left hleftMem right hrightMem hresponse
  · rcases List.mem_append.mp hright with hrightMem | hrightMem
    · exact FieldMerge.fieldsForNameCanMerge_symm
        (hcross right hrightMem left hleftMem hresponse.symm)
    · exact FieldMerge.fieldsInSetCanMerge_pair hrightValid.fieldsCanMerge
        hleftMem hrightMem hresponse

theorem normalizedBranchesPairwiseMerge_of_distinct
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {possibleTypeNames : List Name} {selectionSet : List Selection}
    : (∀ objectType,
        objectType ∈ possibleTypeNames
        -> NormalizedSelectionSetValid schema variableDefinitions objectType
            (normalizeSelectionSet schema objectType selectionSet))
      -> normalizedDistinctBranchesPairwiseMerge schema possibleTypeNames selectionSet
      -> normalizedBranchesPairwiseMerge schema possibleTypeNames selectionSet := by
  intro hbranches hdistinct
  intro leftType hleftType rightType hrightType leftField hleftField
    rightField hrightField hresponse
  by_cases hsame : leftType = rightType
  · subst rightType
    exact normalizedBranchFieldsCanMerge_of_normalizedValid
      (hbranches leftType hleftType) hleftField hrightField hresponse
  · exact hdistinct leftType hleftType rightType hrightType hsame
      leftField hleftField rightField hrightField hresponse

structure NormalizedFieldSource
    (schema : Schema) (source normalized : FieldMerge.ScopedField)
    : Prop where
  responseName : source.responseName = normalized.responseName
  fieldName : source.fieldName = normalized.fieldName
  arguments : source.arguments = normalized.arguments
  outputShape
    : FieldMerge.sameResponseShape schema source.outputType normalized.outputType
  parentCondition
    : source.parentType = normalized.parentType ∨ ¬ schema.objectType source.parentType

theorem normalizedFieldSource_of_scopedFieldSameSelection {schema : Schema}
    {objectField abstractField normalizedField : FieldMerge.ScopedField}
    : scopedFieldSameSelection objectField abstractField
      -> FieldMerge.sameResponseShape schema objectField.outputType
          abstractField.outputType
      -> (abstractField.parentType = objectField.parentType
          ∨ ¬ schema.objectType abstractField.parentType)
      -> NormalizedFieldSource schema objectField normalizedField
      -> NormalizedFieldSource schema abstractField normalizedField := by
  intro hsame hshape hparent hsource
  rcases hsame with
    ⟨hresponse, hfieldName, hargumentsEq, _hselectionSet⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hresponse.symm.trans hsource.responseName
  · exact hfieldName.symm.trans hsource.fieldName
  · exact hargumentsEq.symm.trans hsource.arguments
  · exact FieldMerge.sameResponseShape_trans schema abstractField.outputType
      objectField.outputType normalizedField.outputType
      (FieldMerge.sameResponseShape_symm schema objectField.outputType
        abstractField.outputType hshape)
      hsource.outputShape
  · rcases hparent with hparentEq | hnotObject
    · rcases hsource.parentCondition with hsourceParent | hsourceNotObject
      · exact Or.inl (hparentEq.trans hsourceParent)
      · exact Or.inr (by
          intro habstractObject
          exact hsourceNotObject (by
            simpa [hparentEq] using habstractObject))
    · exact Or.inr hnotObject

theorem collectFields_normalizeSelectionSet_mem_source
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet normalizedField,
        schema.objectType parentType
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> normalizedField
            ∈ FieldMerge.collectFields schema parentType
                (normalizeSelectionSet schema parentType selectionSet)
        -> ∃ sourceField,
            sourceField ∈ FieldMerge.collectFields schema parentType selectionSet
            ∧ NormalizedFieldSource schema sourceField normalizedField := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro normalizedField _hobject _hready hfield
      simp [normalizeSelectionSet, FieldMerge.collectFields] at hfield
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup hrest =>
      intro normalizedField hobject hready hfield
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      rcases hrest normalizedField hobject hfilteredReady
          (by simpa [normalizeSelectionSet, hlookup] using hfield) with
        ⟨sourceField, hsourceMem, hsource⟩
      exact ⟨sourceField,
        fieldMerge_collectFields_tail_mem schema parentType
          (Selection.field responseName fieldName arguments directives
            subselections)
          rest sourceField
          (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem schema
            responseName parentType rest sourceField hsourceMem),
        hsource⟩
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro normalizedSelection hobject hready hfieldMem
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have htailSource
          (htail :
            normalizedSelection ∈
              FieldMerge.collectFields schema parentType
                (normalizeSelectionSet schema parentType
                  (withoutFieldSelectionsWithResponseName schema responseName rest))) :
          ∃ sourceField,
            sourceField ∈
                FieldMerge.collectFields schema parentType
                  (Selection.field responseName fieldName arguments directives
                    subselections :: rest)
              ∧ NormalizedFieldSource schema sourceField normalizedSelection := by
        rcases hrest normalizedSelection hobject hfilteredReady htail with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField,
          fieldMerge_collectFields_tail_mem schema parentType
            (Selection.field responseName fieldName arguments directives
              subselections)
            rest sourceField
            (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem schema
              responseName parentType rest sourceField hsourceMem),
          hsource⟩
      have hheadSource
          (hhead :
            normalizedSelection =
              { parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                outputType := fieldDefinition.outputType
                selectionSet := normalizedSubselections }) :
          ∃ sourceField,
            sourceField ∈
                FieldMerge.collectFields schema parentType
                  (Selection.field responseName fieldName arguments directives
                    subselections :: rest)
              ∧ NormalizedFieldSource schema sourceField normalizedSelection := by
        subst normalizedSelection
        let sourceField : FieldMerge.ScopedField := {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          outputType := fieldDefinition.outputType,
          selectionSet := subselections
        }
        exact ⟨sourceField, by
          simp [sourceField, FieldMerge.collectFields, hlookup],
          by
            refine ⟨rfl, rfl, rfl, ?_, Or.inl rfl⟩
            exact FieldMerge.sameResponseShape_refl schema
              fieldDefinition.outputType
              (SchemaWellFormedness.schemaWellFormed_lookupField_outputType
                hschema hlookup)⟩
      rw [normalizeSelectionSet.eq_2, hlookup] at hfieldMem
      change normalizedSelection ∈
        FieldMerge.collectFields schema parentType
          (normalizedFieldWithRest schema returnType responseName fieldName
            arguments directives normalizedSubselections
            (normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName
                rest))) at hfieldMem
      have hfieldMem' := hfieldMem
      unfold normalizedFieldWithRest at hfieldMem'
      simp [normalizedField, hlookup, FieldMerge.collectFields] at hfieldMem'
      rcases hfieldMem' with hhead | htail
      · exact hheadSource hhead
      · exact htailSource htail
  | case4 parentType rest directives subselections happend =>
      intro normalizedField hobject hready hfieldMem
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment none directives subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        simpa [selectionSemanticsReady] using hheadReady
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      rcases happend normalizedField hobject hbodyTailReady
          (by simpa [normalizeSelectionSet] using hfieldMem) with
        ⟨sourceField, hsourceMem, hsource⟩
      exact ⟨sourceField, by
        simpa [FieldMerge.collectFields, FieldMerge.collectFields_append]
          using hsourceMem,
        hsource⟩
  | case5 parentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro normalizedField hobject hready hfieldMem
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) directives
              subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have hbodyTypeLookup :
          selectionSetLookupValid schema typeCondition subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.1
      have hbodyParentLookup :
          selectionSetLookupValid schema parentType subselections :=
        selectionSetLookupValid_of_selectionSetSemanticsReady subselections
          hbodyReady
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_of_selectionSetSemanticsReady rest htailReady
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      rcases happend normalizedField hobject hbodyTailReady
          (by simpa [normalizeSelectionSet, hoverlap] using hfieldMem) with
        ⟨objectSource, hobjectSourceMem, hsource⟩
      rw [FieldMerge.collectFields_append] at hobjectSourceMem
      rcases List.mem_append.mp hobjectSourceMem with hbodyMem | hrestMem
      · have hpossible :
            parentType ∈ schema.getPossibleTypes typeCondition :=
          List.contains_iff_mem.mp
            (typeIncludesObjectBool_of_object_typesOverlapBool schema
              hobject hoverlap)
        rcases
          fieldMerge_collectFields_objectParent_possibleParent schema
            parentType typeCondition
            subselections
            objectSource hschema hobject hpossible
            hbodyParentLookup
            hbodyTypeLookup
            hbodyMem with
          ⟨abstractSource, habstractMem, hsame, hshape, hparent⟩
        exact ⟨abstractSource, by
          simp [FieldMerge.collectFields]
          exact Or.inl habstractMem,
          normalizedFieldSource_of_scopedFieldSameSelection
            hsame hshape hparent hsource⟩
      · exact ⟨objectSource,
          fieldMerge_collectFields_tail_mem schema parentType
            (Selection.inlineFragment (some typeCondition) directives
              subselections)
            rest objectSource hrestMem,
          hsource⟩
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro normalizedField hobject hready hfieldMem
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      rcases hrest normalizedField hobject htailReady
          (by simpa [normalizeSelectionSet, hfalse] using hfieldMem) with
        ⟨sourceField, hsourceMem, hsource⟩
      exact ⟨sourceField,
        fieldMerge_collectFields_tail_mem schema parentType
          (Selection.inlineFragment (some typeCondition) directives
            subselections)
          rest sourceField hsourceMem,
        hsource⟩

theorem fieldsForNameCanMerge_of_normalizedFieldSources
    {schema : Schema} {sourceLeft sourceRight left right : FieldMerge.ScopedField}
    : NormalizedFieldSource schema sourceLeft left
      -> NormalizedFieldSource schema sourceRight right
      -> left.responseName = right.responseName
      -> FieldMerge.fieldsForNameCanMerge schema sourceLeft sourceRight
      -> ((left.parentType = right.parentType
            ∨ ¬ schema.objectType left.parentType
            ∨ ¬ schema.objectType right.parentType)
          -> ∀ objectType,
              FieldMerge.fieldsInSetCanMerge schema objectType
                (left.selectionSet ++ right.selectionSet))
      -> FieldMerge.fieldsForNameCanMerge schema left right := by
  intro hleft hright _hresponse hsourceMerge hsubfields
  refine FieldMerge.FieldsForNameCanMerge.intro left right ?_ ?_ hsubfields
  · have hsourceShape :
        FieldMerge.sameResponseShape schema sourceLeft.outputType
          sourceRight.outputType :=
      FieldMerge.fieldsForNameCanMerge_sameResponseShape hsourceMerge
    exact FieldMerge.sameResponseShape_trans schema left.outputType
      sourceLeft.outputType right.outputType
      (FieldMerge.sameResponseShape_symm schema sourceLeft.outputType
        left.outputType hleft.outputShape)
      (FieldMerge.sameResponseShape_trans schema sourceLeft.outputType
        sourceRight.outputType right.outputType hsourceShape
        hright.outputShape)
  · intro hparents
    have hsourceParents :
        sourceLeft.parentType = sourceRight.parentType
          ∨ ¬ schema.objectType sourceLeft.parentType
          ∨ ¬ schema.objectType sourceRight.parentType := by
      rcases hleft.parentCondition with hleftParent | hleftNotObject
      · rcases hright.parentCondition with hrightParent | hrightNotObject
        · rcases hparents with hparentEq | hparentNotObject
          · exact Or.inl
              (hleftParent.trans (hparentEq.trans hrightParent.symm))
          · rcases hparentNotObject with hleftNormalizedNotObject
              | hrightNormalizedNotObject
            · exact Or.inr (Or.inl
                (by
                  intro hsourceObject
                  exact hleftNormalizedNotObject
                    (by simpa [hleftParent] using hsourceObject)))
            · exact Or.inr (Or.inr
                (by
                  intro hsourceObject
                  exact hrightNormalizedNotObject
                    (by simpa [hrightParent] using hsourceObject)))
        · exact Or.inr (Or.inr hrightNotObject)
      · exact Or.inr (Or.inl hleftNotObject)
    rcases FieldMerge.fieldsForNameCanMerge_identity hsourceMerge
        hsourceParents with
      ⟨hfieldName, harguments⟩
    exact ⟨hleft.fieldName.symm.trans
        (hfieldName.trans hright.fieldName),
      by
        simpa [← hleft.arguments, ← hright.arguments] using harguments⟩

theorem collectFields_mem_parent_eq_of_allFields (schema : Schema)
    : ∀ parentType selectionSet scopedField,
        selectionsAllFields selectionSet
        -> scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
        -> scopedField.parentType = parentType
  | _parentType, [], _scopedField, _hallFields, hfield => by
      simp [FieldMerge.collectFields] at hfield
  | parentType, selection :: rest, scopedField, hallFields, hfield => by
      have hheadField : Selection.isField selection :=
        hallFields selection (by simp)
      have htailAllFields : selectionsAllFields rest := by
        intro candidate hcandidate
        exact hallFields candidate (by simp [hcandidate])
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              exact collectFields_mem_parent_eq_of_allFields schema
                parentType rest scopedField htailAllFields hfield
          | some fieldDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hfield
              rcases hfield with hhead | htail
              · subst scopedField
                rfl
              · exact collectFields_mem_parent_eq_of_allFields schema
                  parentType rest scopedField htailAllFields htail
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

theorem normalizedDistinctBranchesPairwiseMerge_of_abstractMerge
    (schema : Schema) (_variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (returnType : Name) (possibleTypeNames : List Name)
    (selectionSet : List Selection)
    : (∀ objectType, objectType ∈ possibleTypeNames -> schema.objectType objectType)
      -> (∀ objectType,
            objectType ∈ possibleTypeNames
            -> objectType ∈ schema.getPossibleTypes returnType)
      -> selectionSetLookupValid schema returnType selectionSet
      -> (∀ objectType,
            objectType ∈ possibleTypeNames
            -> selectionSetSemanticsReady schema objectType selectionSet)
      -> FieldMerge.fieldsInSetCanMerge schema returnType selectionSet
      -> normalizedDistinctBranchesPairwiseMerge schema possibleTypeNames
          selectionSet := by
  intro hobjects hpossible hlookupReturn hreadyBranches hmergeReturn
  intro leftType hleftType rightType hrightType hdistinct leftField
    hleftField rightField hrightField hresponse
  have hleftObject : schema.objectType leftType :=
    hobjects leftType hleftType
  have hrightObject : schema.objectType rightType :=
    hobjects rightType hrightType
  have hleftLookup :
      selectionSetLookupValid schema leftType selectionSet :=
    selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
      (hreadyBranches leftType hleftType)
  have hrightLookup :
      selectionSetLookupValid schema rightType selectionSet :=
    selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
      (hreadyBranches rightType hrightType)
  rcases collectFields_normalizeSelectionSet_mem_source schema hschema
      leftType selectionSet leftField hleftObject
      (hreadyBranches leftType hleftType) hleftField with
    ⟨leftSource, hleftSourceMem, hleftSource⟩
  rcases collectFields_normalizeSelectionSet_mem_source schema hschema
      rightType selectionSet rightField hrightObject
      (hreadyBranches rightType hrightType) hrightField with
    ⟨rightSource, hrightSourceMem, hrightSource⟩
  rcases
    fieldMerge_collectFields_objectParent_possibleParent schema leftType
      returnType selectionSet leftSource hschema hleftObject
      (hpossible leftType hleftType) hleftLookup hlookupReturn
      hleftSourceMem with
    ⟨leftAbstract, hleftAbstractMem, hleftSame, hleftShape,
      hleftParent⟩
  rcases
    fieldMerge_collectFields_objectParent_possibleParent schema rightType
      returnType selectionSet rightSource hschema hrightObject
      (hpossible rightType hrightType) hrightLookup hlookupReturn
      hrightSourceMem with
    ⟨rightAbstract, hrightAbstractMem, hrightSame, hrightShape,
      hrightParent⟩
  have hleftAbstractSource :
      NormalizedFieldSource schema leftAbstract leftField :=
    normalizedFieldSource_of_scopedFieldSameSelection hleftSame hleftShape
      hleftParent hleftSource
  have hrightAbstractSource :
      NormalizedFieldSource schema rightAbstract rightField :=
    normalizedFieldSource_of_scopedFieldSameSelection hrightSame hrightShape
      hrightParent hrightSource
  have habstractResponse :
      leftAbstract.responseName = rightAbstract.responseName :=
    hleftAbstractSource.responseName.trans
      (hresponse.trans hrightAbstractSource.responseName.symm)
  have habstractMerge :
      FieldMerge.fieldsForNameCanMerge schema leftAbstract rightAbstract :=
    FieldMerge.fieldsInSetCanMerge_pair hmergeReturn hleftAbstractMem
      hrightAbstractMem habstractResponse
  have hleftParentEq :
      leftField.parentType = leftType :=
    collectFields_mem_parent_eq_of_allFields schema leftType
      (normalizeSelectionSet schema leftType selectionSet) leftField
      (normalizeSelectionSet_allFields schema leftType selectionSet)
      hleftField
  have hrightParentEq :
      rightField.parentType = rightType :=
    collectFields_mem_parent_eq_of_allFields schema rightType
      (normalizeSelectionSet schema rightType selectionSet) rightField
      (normalizeSelectionSet_allFields schema rightType selectionSet)
      hrightField
  apply fieldsForNameCanMerge_of_normalizedFieldSources
      hleftAbstractSource hrightAbstractSource hresponse habstractMerge
  intro hparents objectType
  rcases hparents with hparentEq | hnotObject
  · exact False.elim (hdistinct
      (hleftParentEq.symm.trans (hparentEq.trans hrightParentEq)))
  · rcases hnotObject with hleftNotObject | hrightNotObject
    · exact False.elim (hleftNotObject (by simpa [hleftParentEq] using hleftObject))
    · exact False.elim (hrightNotObject (by simpa [hrightParentEq] using hrightObject))

end GroundTypeNormalization

end NormalForm

end GraphQL
