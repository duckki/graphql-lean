import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.Sources.GroupSources

/-!
Child-pair merge transport facts for complete-normalization branch validity.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem fieldsInSetCanMerge_groupSource_rawChildSource_self
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType objectType : Name)
    {selectionSet : List Selection}
    {field : FieldMerge.ScopedField}
    (hgroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          selectionSet field)
    : schema.objectType parentType
      -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema objectType
          (hgroup.childSource ++ hgroup.childSource) := by
  intro hobject hmerge
  exact fieldsInSetCanMerge_groupSources_rawChildSource_pair schema
    variableDefinitions parentType objectType hgroup hgroup hobject
    (GroundTypeNormalization.fieldsInSetCanMerge_self schema parentType
      selectionSet hmerge)
    rfl

theorem normalizedFieldGroup_childBranchNormalizedValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType : Name)
    {selectionSet : List Selection}
    {field : FieldMerge.ScopedField}
    (hgroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          selectionSet field)
    : schema.objectType parentType
      -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> ∀ objectType,
          objectType ∈ schema.getPossibleTypes field.outputType.namedType
          -> GroundTypeNormalization.NormalizedSelectionSetValid schema
              variableDefinitions objectType
              (normalizeSelectionSet schema objectType hgroup.childSource) := by
  intro hparentObject hsourceMerge objectType hpossible
  have hobject :
      schema.objectType objectType :=
    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
      field.outputType.namedType objectType hpossible
  have hchildSelf :
      FieldMerge.fieldsInSetCanMerge schema objectType
        (hgroup.childSource ++ hgroup.childSource) :=
    fieldsInSetCanMerge_groupSource_rawChildSource_self schema
      variableDefinitions parentType objectType hgroup hparentObject
      hsourceMerge
  have hchildMerge :
      FieldMerge.fieldsInSetCanMerge schema objectType
        hgroup.childSource :=
    fieldsInSetCanMerge_append_left schema objectType hgroup.childSource
      hgroup.childSource hchildSelf
  have hstack :
      GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
        objectType [objectType] :=
    GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hobject
  exact GroundTypeNormalization.normalizeSelectionSet_normalizedValid_of_typeConditionFeasible
    schema variableDefinitions hschema objectType hgroup.childSource
    [objectType] hobject hstack (hgroup.childReady objectType hpossible)
    (hgroup.childImplementation objectType hpossible)
    hchildMerge hgroup.childDirectiveFree
    (hgroup.childFeasible objectType hpossible)

theorem normalizedFields_childSources_canMerge
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType objectType : Name)
    (leftSet rightSet : List Selection)
    (leftField rightField : FieldMerge.ScopedField)
    : schema.objectType parentType
      -> selectionSetSemanticsReady schema parentType leftSet
      -> selectionSetSemanticsReady schema parentType rightSet
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType leftSet
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType rightSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType leftSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType rightSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> selectionSetDirectiveFree leftSet
      -> selectionSetDirectiveFree rightSet
      -> selectionSetTypeConditionFeasible schema parentType [parentType]
          .allFields leftSet
      -> selectionSetTypeConditionFeasible schema parentType [parentType]
          .allFields rightSet
      -> leftField
          ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType leftSet)
      -> rightField
          ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType rightSet)
      -> leftField.responseName = rightField.responseName
      -> ∃ leftGroup
            : NormalizedFieldGroupSource schema variableDefinitions parentType
                leftSet leftField,
          ∃ rightGroup
              : NormalizedFieldGroupSource schema variableDefinitions parentType
                  rightSet rightField,
            FieldMerge.fieldsInSetCanMerge schema objectType
              (leftGroup.childSource ++ rightGroup.childSource) := by
  intro hobject hleftReady hrightReady hleftImplementation
    hrightImplementation hleftMerge hrightMerge hsourcePair hleftFree
    hrightFree hleftFeasible hrightFeasible hleftField hrightField
    hresponse
  let leftGroup :=
    collectFields_normalizeSelectionSet_mem_groupSource schema
      variableDefinitions hschema parentType leftSet leftField hobject
      hleftReady
      (selectionSetLookupValid_of_selectionSetSemanticsReady leftSet
        hleftReady)
      hleftImplementation hleftMerge hleftFree hleftFeasible hleftField
  let rightGroup :=
    collectFields_normalizeSelectionSet_mem_groupSource schema
      variableDefinitions hschema parentType rightSet rightField hobject
      hrightReady
      (selectionSetLookupValid_of_selectionSetSemanticsReady rightSet
        hrightReady)
      hrightImplementation hrightMerge hrightFree hrightFeasible hrightField
  refine ⟨leftGroup, rightGroup, ?_⟩
  exact fieldsInSetCanMerge_groupSources_rawChildSource_pair schema
    variableDefinitions parentType objectType leftGroup rightGroup hobject
    hsourcePair hresponse

theorem normalizedFieldGroupSources_identity_of_sourcePair
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> (leftField.parentType = rightField.parentType
          ∨ ¬ schema.objectType leftField.parentType
          ∨ ¬ schema.objectType rightField.parentType)
      -> leftField.fieldName = rightField.fieldName
          ∧ Argument.argumentsEquivalent leftField.arguments rightField.arguments := by
  intro hsourcePair hresponse hparents
  have hsourceResponse :
      hleftGroup.source.responseName = hrightGroup.source.responseName :=
    hleftGroup.sourceRel.responseName.trans
      (hresponse.trans hrightGroup.sourceRel.responseName.symm)
  have hleftSourceMem :
      hleftGroup.source ∈ FieldMerge.collectFields schema parentType
        (leftSet ++ rightSet) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_left
      (FieldMerge.collectFields schema parentType rightSet)
      hleftGroup.sourceMem
  have hrightSourceMem :
      hrightGroup.source ∈ FieldMerge.collectFields schema parentType
        (leftSet ++ rightSet) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_right
      (FieldMerge.collectFields schema parentType leftSet)
      hrightGroup.sourceMem
  have hsourceMerge :
      FieldMerge.fieldsForNameCanMerge schema hleftGroup.source
        hrightGroup.source :=
    FieldMerge.fieldsInSetCanMerge_pair hsourcePair hleftSourceMem
      hrightSourceMem hsourceResponse
  have hsourceParents :
      hleftGroup.source.parentType = hrightGroup.source.parentType
        ∨ ¬ schema.objectType hleftGroup.source.parentType
        ∨ ¬ schema.objectType hrightGroup.source.parentType := by
    rcases hleftGroup.sourceRel.parentCondition with
      hleftParent | hleftNotObject
    · rcases hrightGroup.sourceRel.parentCondition with
        hrightParent | hrightNotObject
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
  rcases
    FieldMerge.fieldsForNameCanMerge_identity hsourceMerge
      hsourceParents with
    ⟨hsourceField, hsourceArguments⟩
  exact ⟨
    hleftGroup.sourceRel.fieldName.symm.trans
      (hsourceField.trans hrightGroup.sourceRel.fieldName),
    by
      simpa [← hleftGroup.sourceRel.arguments,
        ← hrightGroup.sourceRel.arguments] using hsourceArguments⟩

theorem normalizedFieldGroupSources_outputType_eq_of_sourcePair
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : leftField
        ∈ FieldMerge.collectFields schema parentType
            (normalizeSelectionSet schema parentType leftSet)
      -> rightField
          ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType rightSet)
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> (leftField.parentType = rightField.parentType
          ∨ ¬ schema.objectType leftField.parentType
          ∨ ¬ schema.objectType rightField.parentType)
      -> leftField.outputType = rightField.outputType := by
  intro hleftMem hrightMem hsourcePair hresponse hparents
  have hidentity :=
    normalizedFieldGroupSources_identity_of_sourcePair schema
      variableDefinitions parentType hleftGroup hrightGroup hsourcePair
      hresponse hparents
  have hleftParent :
      leftField.parentType = parentType :=
    GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
      parentType (normalizeSelectionSet schema parentType leftSet)
      leftField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType leftSet)
      hleftMem
  have hrightParent :
      rightField.parentType = parentType :=
    GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
      parentType (normalizeSelectionSet schema parentType rightSet)
      rightField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType rightSet)
      hrightMem
  exact
    fieldMerge_collectFields_outputType_eq_of_same_parent_field schema
      hleftMem hrightMem (hleftParent.trans hrightParent.symm)
      hidentity.1

theorem fieldsForNameCanMerge_of_normalizedFieldGroupSources
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> ((leftField.parentType = rightField.parentType
            ∨ ¬ schema.objectType leftField.parentType
            ∨ ¬ schema.objectType rightField.parentType)
          -> ∀ objectType,
              FieldMerge.fieldsInSetCanMerge schema objectType
                (leftField.selectionSet ++ rightField.selectionSet))
      -> FieldMerge.fieldsForNameCanMerge schema leftField rightField := by
  intro hsourcePair hresponse hsubfields
  have hsourceResponse :
      hleftGroup.source.responseName = hrightGroup.source.responseName :=
    hleftGroup.sourceRel.responseName.trans
      (hresponse.trans hrightGroup.sourceRel.responseName.symm)
  have hleftSourceMem :
      hleftGroup.source ∈ FieldMerge.collectFields schema parentType
        (leftSet ++ rightSet) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_left
      (FieldMerge.collectFields schema parentType rightSet)
      hleftGroup.sourceMem
  have hrightSourceMem :
      hrightGroup.source ∈ FieldMerge.collectFields schema parentType
        (leftSet ++ rightSet) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_right
      (FieldMerge.collectFields schema parentType leftSet)
      hrightGroup.sourceMem
  have hsourceMerge :
      FieldMerge.fieldsForNameCanMerge schema hleftGroup.source
        hrightGroup.source :=
    FieldMerge.fieldsInSetCanMerge_pair hsourcePair hleftSourceMem
      hrightSourceMem hsourceResponse
  exact
    GroundTypeNormalization.fieldsForNameCanMerge_of_normalizedFieldSources
      hleftGroup.sourceRel hrightGroup.sourceRel hresponse hsourceMerge
      hsubfields

theorem fieldsForNameCanMerge_of_normalizedFieldGroupSources_childSources
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> ((leftField.parentType = rightField.parentType
            ∨ ¬ schema.objectType leftField.parentType
            ∨ ¬ schema.objectType rightField.parentType)
          -> ∀ objectType,
              FieldMerge.fieldsInSetCanMerge schema objectType
                ((if objectTypeNameBool schema leftField.outputType.namedType then
                    normalizeSelectionSet schema leftField.outputType.namedType
                      hleftGroup.childSource
                  else
                    GroundTypeNormalization.possibleTypeNormalizations schema
                      (schema.getPossibleTypes leftField.outputType.namedType)
                      hleftGroup.childSource)
                  ++ (if objectTypeNameBool schema rightField.outputType.namedType then
                        normalizeSelectionSet schema rightField.outputType.namedType
                          hrightGroup.childSource
                      else
                        GroundTypeNormalization.possibleTypeNormalizations schema
                          (schema.getPossibleTypes rightField.outputType.namedType)
                          hrightGroup.childSource)))
      -> FieldMerge.fieldsForNameCanMerge schema leftField rightField := by
  intro hsourcePair hresponse hchildPairs
  apply fieldsForNameCanMerge_of_normalizedFieldGroupSources
      schema variableDefinitions parentType hleftGroup hrightGroup
      hsourcePair hresponse
  intro hparents objectType
  have hchild := hchildPairs hparents objectType
  simpa [hleftGroup.normalizedSelectionSet,
    hrightGroup.normalizedSelectionSet] using hchild

theorem normalizedFields_fieldsForNameCanMerge_of_childPairs
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType : Name)
    (leftSet rightSet : List Selection)
    (leftField rightField : FieldMerge.ScopedField)
    : schema.objectType parentType
      -> selectionSetSemanticsReady schema parentType leftSet
      -> selectionSetSemanticsReady schema parentType rightSet
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType leftSet
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType rightSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType leftSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType rightSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> selectionSetDirectiveFree leftSet
      -> selectionSetDirectiveFree rightSet
      -> selectionSetTypeConditionFeasible schema parentType [parentType]
          .allFields leftSet
      -> selectionSetTypeConditionFeasible schema parentType [parentType]
          .allFields rightSet
      -> leftField
          ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType leftSet)
      -> rightField
          ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType rightSet)
      -> leftField.responseName = rightField.responseName
      -> (∀ leftGroup : NormalizedFieldGroupSource schema variableDefinitions parentType
                          leftSet leftField,
          ∀ rightGroup : NormalizedFieldGroupSource schema variableDefinitions
                          parentType rightSet rightField,
            (leftField.parentType = rightField.parentType
              ∨ ¬ schema.objectType leftField.parentType
              ∨ ¬ schema.objectType rightField.parentType)
            -> ∀ objectType,
                FieldMerge.fieldsInSetCanMerge schema objectType
                  ((if objectTypeNameBool schema leftField.outputType.namedType then
                      normalizeSelectionSet schema leftField.outputType.namedType
                        leftGroup.childSource
                    else
                      GroundTypeNormalization.possibleTypeNormalizations schema
                        (schema.getPossibleTypes leftField.outputType.namedType)
                        leftGroup.childSource)
                    ++ (if objectTypeNameBool schema rightField.outputType.namedType then
                          normalizeSelectionSet schema rightField.outputType.namedType
                            rightGroup.childSource
                        else
                          GroundTypeNormalization.possibleTypeNormalizations schema
                            (schema.getPossibleTypes rightField.outputType.namedType)
                            rightGroup.childSource)))
      -> FieldMerge.fieldsForNameCanMerge schema leftField rightField := by
  intro hobject hleftReady hrightReady hleftImplementation
    hrightImplementation hleftMerge hrightMerge hsourcePair hleftFree
    hrightFree hleftFeasible hrightFeasible hleftField hrightField
    hresponse hchildPairs
  let leftGroup :=
    collectFields_normalizeSelectionSet_mem_groupSource schema
      variableDefinitions hschema parentType leftSet leftField hobject
      hleftReady
      (selectionSetLookupValid_of_selectionSetSemanticsReady leftSet
        hleftReady)
      hleftImplementation hleftMerge hleftFree hleftFeasible hleftField
  let rightGroup :=
    collectFields_normalizeSelectionSet_mem_groupSource schema
      variableDefinitions hschema parentType rightSet rightField hobject
      hrightReady
      (selectionSetLookupValid_of_selectionSetSemanticsReady rightSet
        hrightReady)
      hrightImplementation hrightMerge hrightFree hrightFeasible hrightField
  exact fieldsForNameCanMerge_of_normalizedFieldGroupSources_childSources
    schema variableDefinitions parentType leftGroup rightGroup hsourcePair
    hresponse (hchildPairs leftGroup rightGroup)

theorem normalizedFields_fieldsForNameCanMerge_of_childPairs_anyParent
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType mergeParent : Name)
    (leftSet rightSet : List Selection)
    (leftField rightField : FieldMerge.ScopedField)
    : schema.objectType parentType
      -> selectionSetSemanticsReady schema parentType leftSet
      -> selectionSetSemanticsReady schema parentType rightSet
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType leftSet
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType rightSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType leftSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType rightSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> selectionSetDirectiveFree leftSet
      -> selectionSetDirectiveFree rightSet
      -> selectionSetTypeConditionFeasible schema parentType [parentType]
          .allFields leftSet
      -> selectionSetTypeConditionFeasible schema parentType [parentType]
          .allFields rightSet
      -> leftField
          ∈ FieldMerge.collectFields schema mergeParent
              (normalizeSelectionSet schema parentType leftSet)
      -> rightField
          ∈ FieldMerge.collectFields schema mergeParent
              (normalizeSelectionSet schema parentType rightSet)
      -> leftField.responseName = rightField.responseName
      -> (∀ leftParentField,
            leftParentField
              ∈ FieldMerge.collectFields schema parentType
                  (normalizeSelectionSet schema parentType leftSet)
            -> ∀ rightParentField,
                rightParentField
                  ∈ FieldMerge.collectFields schema parentType
                      (normalizeSelectionSet schema parentType rightSet)
                -> leftParentField.responseName = rightParentField.responseName
                -> ∀ leftGroup : NormalizedFieldGroupSource schema variableDefinitions
                                  parentType leftSet leftParentField,
                    ∀ rightGroup : NormalizedFieldGroupSource schema variableDefinitions
                                    parentType rightSet rightParentField,
                      (leftParentField.parentType = rightParentField.parentType
                        ∨ ¬ schema.objectType leftParentField.parentType
                        ∨ ¬ schema.objectType rightParentField.parentType)
                      -> ∀ objectType,
                          FieldMerge.fieldsInSetCanMerge schema objectType
                            ((if objectTypeNameBool schema
                                  leftParentField.outputType.namedType then
                                normalizeSelectionSet schema
                                  leftParentField.outputType.namedType
                                  leftGroup.childSource
                              else
                                GroundTypeNormalization.possibleTypeNormalizations
                                  schema
                                  (schema.getPossibleTypes
                                    leftParentField.outputType.namedType)
                                  leftGroup.childSource)
                              ++ (if objectTypeNameBool schema
                                      rightParentField.outputType.namedType then
                                    normalizeSelectionSet schema
                                      rightParentField.outputType.namedType
                                      rightGroup.childSource
                                  else
                                    GroundTypeNormalization.possibleTypeNormalizations
                                      schema
                                      (schema.getPossibleTypes
                                        rightParentField.outputType.namedType)
                                      rightGroup.childSource)))
      -> FieldMerge.fieldsForNameCanMerge schema leftField rightField := by
  intro hobject hleftReady hrightReady hleftImplementation
    hrightImplementation hleftMerge hrightMerge hsourcePair hleftFree
    hrightFree hleftFeasible hrightFeasible hleftField hrightField
    hresponse hchildPairs
  have hstack :
      GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
        parentType [parentType] :=
    GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hobject
  have hleftValid :
      GroundTypeNormalization.NormalizedSelectionSetValid schema
        variableDefinitions parentType
        (normalizeSelectionSet schema parentType leftSet) :=
    GroundTypeNormalization.normalizeSelectionSet_normalizedValid_of_typeConditionFeasible
      schema variableDefinitions hschema parentType leftSet [parentType]
      hobject hstack
      hleftReady hleftImplementation hleftMerge hleftFree
      hleftFeasible
  have hrightValid :
      GroundTypeNormalization.NormalizedSelectionSetValid schema
        variableDefinitions parentType
        (normalizeSelectionSet schema parentType rightSet) :=
    GroundTypeNormalization.normalizeSelectionSet_normalizedValid_of_typeConditionFeasible
      schema variableDefinitions hschema parentType rightSet [parentType]
      hobject hstack
      hrightReady hrightImplementation hrightMerge hrightFree
      hrightFeasible
  rcases
    fieldMerge_collectFields_allFields_lookupParent_sameSelection schema
      parentType mergeParent
      (normalizeSelectionSet schema parentType leftSet) leftField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType leftSet)
      (selectionSetLookupValid_of_selectionSetValid
        (normalizeSelectionSet schema parentType leftSet)
        hleftValid.selectionSetValid)
      hleftField with
    ⟨leftParentField, hleftParentField, hleftSame⟩
  rcases
    fieldMerge_collectFields_allFields_lookupParent_sameSelection schema
      parentType mergeParent
      (normalizeSelectionSet schema parentType rightSet) rightField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType rightSet)
      (selectionSetLookupValid_of_selectionSetValid
        (normalizeSelectionSet schema parentType rightSet)
        hrightValid.selectionSetValid)
      hrightField with
    ⟨rightParentField, hrightParentField, hrightSame⟩
  have hparentResponse :
      leftParentField.responseName = rightParentField.responseName :=
    hleftSame.1.symm.trans (hresponse.trans hrightSame.1)
  have hparentMerge :
      FieldMerge.fieldsForNameCanMerge schema leftParentField
        rightParentField :=
    normalizedFields_fieldsForNameCanMerge_of_childPairs schema
      variableDefinitions hschema parentType leftSet rightSet
      leftParentField rightParentField hobject hleftReady hrightReady
      hleftImplementation hrightImplementation hleftMerge hrightMerge
      hsourcePair hleftFree hrightFree hleftFeasible hrightFeasible
      hleftParentField hrightParentField
      hparentResponse
      (hchildPairs leftParentField hleftParentField rightParentField
        hrightParentField hparentResponse)
  have hleftTargetParent :
      leftField.parentType = mergeParent :=
    GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
      mergeParent (normalizeSelectionSet schema parentType leftSet)
      leftField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType leftSet)
      hleftField
  have hrightTargetParent :
      rightField.parentType = mergeParent :=
    GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
      mergeParent (normalizeSelectionSet schema parentType rightSet)
      rightField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType rightSet)
      hrightField
  have hleftParentEq :
      leftParentField.parentType = parentType :=
    GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
      parentType (normalizeSelectionSet schema parentType leftSet)
      leftParentField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType leftSet)
      hleftParentField
  have hrightParentEq :
      rightParentField.parentType = parentType :=
    GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
      parentType (normalizeSelectionSet schema parentType rightSet)
      rightParentField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType rightSet)
      hrightParentField
  have htargetParents :
      leftField.parentType = rightField.parentType :=
    hleftTargetParent.trans hrightTargetParent.symm
  have hsourceParents :
      leftParentField.parentType = rightParentField.parentType
        ∨ ¬ schema.objectType leftParentField.parentType
        ∨ ¬ schema.objectType rightParentField.parentType :=
    Or.inl (hleftParentEq.trans hrightParentEq.symm)
  have hsubfields :
      ∀ objectType,
        FieldMerge.fieldsInSetCanMerge schema objectType
          (leftField.selectionSet ++ rightField.selectionSet) := by
    intro objectType
    have hparentSubfields :=
      FieldMerge.fieldsForNameCanMerge_subfields hparentMerge
        hsourceParents objectType
    simpa [hleftSame.2.2.2, hrightSame.2.2.2] using
      hparentSubfields
  exact
    fieldsForNameCanMerge_of_sameParent_sameSelection_source schema hschema
      hleftField hrightField hleftSame hrightSame htargetParents
      hparentResponse hsourceParents hparentMerge hsubfields

theorem normalizedFieldGroupSources_objectReturn_childPairs
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType returnType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : schema.objectType parentType
      -> objectTypeNameBool schema returnType = true
      -> FieldMerge.fieldsInSetCanMerge schema parentType leftSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType rightSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> leftField.outputType.namedType = returnType
      -> rightField.outputType.namedType = returnType
      -> (∀ leftChildField,
            leftChildField
              ∈ FieldMerge.collectFields schema returnType
                  (normalizeSelectionSet schema returnType hleftGroup.childSource)
            -> ∀ rightChildField,
                rightChildField
                  ∈ FieldMerge.collectFields schema returnType
                      (normalizeSelectionSet schema returnType hrightGroup.childSource)
                -> leftChildField.responseName = rightChildField.responseName
                -> ∀ leftChildGroup : NormalizedFieldGroupSource schema
                                        variableDefinitions returnType
                                        hleftGroup.childSource leftChildField,
                    ∀ rightChildGroup : NormalizedFieldGroupSource schema
                                          variableDefinitions returnType
                                          hrightGroup.childSource rightChildField,
                      (leftChildField.parentType = rightChildField.parentType
                        ∨ ¬ schema.objectType leftChildField.parentType
                        ∨ ¬ schema.objectType rightChildField.parentType)
                      -> ∀ objectType,
                          FieldMerge.fieldsInSetCanMerge schema objectType
                            ((if objectTypeNameBool schema
                                  leftChildField.outputType.namedType then
                                normalizeSelectionSet schema
                                  leftChildField.outputType.namedType
                                  leftChildGroup.childSource
                              else
                                GroundTypeNormalization.possibleTypeNormalizations
                                  schema
                                  (schema.getPossibleTypes
                                    leftChildField.outputType.namedType)
                                  leftChildGroup.childSource)
                              ++ (if objectTypeNameBool schema
                                      rightChildField.outputType.namedType then
                                    normalizeSelectionSet schema
                                      rightChildField.outputType.namedType
                                      rightChildGroup.childSource
                                  else
                                    GroundTypeNormalization.possibleTypeNormalizations
                                      schema
                                      (schema.getPossibleTypes
                                        rightChildField.outputType.namedType)
                                      rightChildGroup.childSource)))
      -> ∀ mergeParent,
          FieldMerge.fieldsInSetCanMerge schema mergeParent
            (normalizeSelectionSet schema returnType hleftGroup.childSource
              ++ normalizeSelectionSet schema returnType hrightGroup.childSource) := by
  intro hobject hreturnObject hleftMerge hrightMerge hsourcePair
    hresponse hleftReturn hrightReturn hchildPairs mergeParent
  have hreturnObjectProp : schema.objectType returnType :=
    objectType_of_objectTypeNameBool_eq_true schema hreturnObject
  have hreturnPossible :
      returnType ∈ schema.getPossibleTypes returnType :=
    List.contains_iff_mem.mp
      (object_typeIncludesObjectBool_self schema hreturnObjectProp)
  have hleftReady :
      selectionSetSemanticsReady schema returnType hleftGroup.childSource :=
    hleftGroup.childReady returnType
      (by simpa [← hleftReturn] using hreturnPossible)
  have hrightReady :
      selectionSetSemanticsReady schema returnType hrightGroup.childSource :=
    hrightGroup.childReady returnType
      (by simpa [← hrightReturn] using hreturnPossible)
  have hleftImplementation :
      Validation.selectionSetValidInPossibleTypes schema
        variableDefinitions returnType hleftGroup.childSource :=
    hleftGroup.childImplementation returnType
      (by simpa [← hleftReturn] using hreturnPossible)
  have hrightImplementation :
      Validation.selectionSetValidInPossibleTypes schema
        variableDefinitions returnType hrightGroup.childSource :=
    hrightGroup.childImplementation returnType
      (by simpa [← hrightReturn] using hreturnPossible)
  have hleftFeasible :
      selectionSetTypeConditionFeasible schema returnType [returnType]
        .allFields hleftGroup.childSource :=
    hleftGroup.childFeasible returnType
      (by simpa [← hleftReturn] using hreturnPossible)
  have hrightFeasible :
      selectionSetTypeConditionFeasible schema returnType [returnType]
        .allFields hrightGroup.childSource :=
    hrightGroup.childFeasible returnType
      (by simpa [← hrightReturn] using hreturnPossible)
  have hchildSourcePair :
      FieldMerge.fieldsInSetCanMerge schema returnType
        (hleftGroup.childSource ++ hrightGroup.childSource) :=
    fieldsInSetCanMerge_groupSources_rawChildSource_pair schema
      variableDefinitions parentType returnType hleftGroup hrightGroup
      hobject hsourcePair hresponse
  have hleftChildMerge :
      FieldMerge.fieldsInSetCanMerge schema returnType
        hleftGroup.childSource :=
    fieldsInSetCanMerge_append_left schema returnType
      hleftGroup.childSource hrightGroup.childSource hchildSourcePair
  have hrightChildMerge :
      FieldMerge.fieldsInSetCanMerge schema returnType
        hrightGroup.childSource :=
    fieldsInSetCanMerge_append_right schema returnType
      hleftGroup.childSource hrightGroup.childSource hchildSourcePair
  have hstack :
      GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
        returnType [returnType] :=
    GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hreturnObjectProp
  have hleftValid :
      GroundTypeNormalization.NormalizedSelectionSetValid schema
        variableDefinitions returnType
        (normalizeSelectionSet schema returnType hleftGroup.childSource) :=
    GroundTypeNormalization.normalizeSelectionSet_normalizedValid_of_typeConditionFeasible
      schema variableDefinitions hschema returnType hleftGroup.childSource
      [returnType] hreturnObjectProp hstack hleftReady
      hleftImplementation hleftChildMerge hleftGroup.childDirectiveFree
      hleftFeasible
  have hrightValid :
      GroundTypeNormalization.NormalizedSelectionSetValid schema
        variableDefinitions returnType
        (normalizeSelectionSet schema returnType hrightGroup.childSource) :=
    GroundTypeNormalization.normalizeSelectionSet_normalizedValid_of_typeConditionFeasible
      schema variableDefinitions hschema returnType hrightGroup.childSource
      [returnType] hreturnObjectProp hstack hrightReady
      hrightImplementation hrightChildMerge hrightGroup.childDirectiveFree
      hrightFeasible
  apply fieldsInSetCanMerge_append_of_pairwise
      schema mergeParent
      (normalizeSelectionSet schema returnType hleftGroup.childSource)
      (normalizeSelectionSet schema returnType hrightGroup.childSource)
  · exact normalizedSelectionSetFieldsCanMerge_anyParent hleftValid
  · exact normalizedSelectionSetFieldsCanMerge_anyParent hrightValid
  · intro leftChildField hleftChildField rightChildField
      hrightChildField hchildResponse
    exact
      normalizedFields_fieldsForNameCanMerge_of_childPairs_anyParent schema
        variableDefinitions hschema returnType mergeParent
        hleftGroup.childSource hrightGroup.childSource leftChildField
        rightChildField hreturnObjectProp hleftReady hrightReady
        hleftImplementation hrightImplementation hleftChildMerge
        hrightChildMerge hchildSourcePair hleftGroup.childDirectiveFree
        hrightGroup.childDirectiveFree hleftFeasible hrightFeasible
        hleftChildField hrightChildField hchildResponse hchildPairs

end CompleteNormalization

end NormalForm

end GraphQL
