import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.Sources.ChildPairs

/-!
Abstract-branch merge assembly facts for complete-normalization branch validity.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem possibleTypeNormalizations_fieldsInSetCanMerge_pair_any
    (schema : Schema) (mergeParent : Name)
    (leftPossibleTypes rightPossibleTypes : List Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    : (∀ leftType,
        leftType ∈ leftPossibleTypes
        -> ∀ rightType,
            rightType ∈ leftPossibleTypes
            -> ∀ leftField,
                leftField
                  ∈ FieldMerge.collectFields schema leftType
                      (normalizeSelectionSet schema leftType leftSelectionSet)
                -> ∀ rightField,
                    rightField
                      ∈ FieldMerge.collectFields schema rightType
                          (normalizeSelectionSet schema rightType leftSelectionSet)
                    -> leftField.responseName = rightField.responseName
                    -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
      -> (∀ leftType,
            leftType ∈ rightPossibleTypes
            -> ∀ rightType,
                rightType ∈ rightPossibleTypes
                -> ∀ leftField,
                    leftField
                      ∈ FieldMerge.collectFields schema leftType
                          (normalizeSelectionSet schema leftType rightSelectionSet)
                    -> ∀ rightField,
                        rightField
                          ∈ FieldMerge.collectFields schema rightType
                              (normalizeSelectionSet schema rightType rightSelectionSet)
                        -> leftField.responseName = rightField.responseName
                        -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
      -> (∀ leftType,
            leftType ∈ leftPossibleTypes
            -> ∀ rightType,
                rightType ∈ rightPossibleTypes
                -> ∀ leftField,
                    leftField
                      ∈ FieldMerge.collectFields schema leftType
                          (normalizeSelectionSet schema leftType leftSelectionSet)
                    -> ∀ rightField,
                        rightField
                          ∈ FieldMerge.collectFields schema rightType
                              (normalizeSelectionSet schema rightType rightSelectionSet)
                        -> leftField.responseName = rightField.responseName
                        -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
      -> FieldMerge.fieldsInSetCanMerge schema mergeParent
          (GroundTypeNormalization.possibleTypeNormalizations schema
              leftPossibleTypes leftSelectionSet
            ++ GroundTypeNormalization.possibleTypeNormalizations schema
                rightPossibleTypes rightSelectionSet) := by
  intro hleftPairwise hrightPairwise hcross
  apply fieldsInSetCanMerge_append_of_pairwise
  · exact GroundTypeNormalization.possibleTypeNormalizations_fieldsInSetCanMerge
      schema mergeParent leftPossibleTypes leftSelectionSet hleftPairwise
  · exact GroundTypeNormalization.possibleTypeNormalizations_fieldsInSetCanMerge
      schema mergeParent rightPossibleTypes rightSelectionSet
      hrightPairwise
  · intro leftField hleftField rightField hrightField hresponse
    rcases
      GroundTypeNormalization.collectFields_possibleTypeNormalizations_mem
        schema mergeParent leftPossibleTypes leftSelectionSet leftField
        hleftField with
    ⟨leftType, hleftType, hleftBranchField⟩
    rcases
      GroundTypeNormalization.collectFields_possibleTypeNormalizations_mem
        schema mergeParent rightPossibleTypes rightSelectionSet rightField
        hrightField with
    ⟨rightType, hrightType, hrightBranchField⟩
    exact hcross leftType hleftType rightType hrightType leftField
      hleftBranchField rightField hrightBranchField hresponse

theorem normalizedDistinctBranchesPairwiseMerge_of_abstractMerge_pair
    (schema : Schema) (_variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (returnType : Name)
    (leftPossibleTypes rightPossibleTypes : List Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    : (∀ objectType, objectType ∈ leftPossibleTypes -> schema.objectType objectType)
      -> (∀ objectType,
            objectType ∈ leftPossibleTypes
            -> objectType ∈ schema.getPossibleTypes returnType)
      -> (∀ objectType, objectType ∈ rightPossibleTypes -> schema.objectType objectType)
      -> (∀ objectType,
            objectType ∈ rightPossibleTypes
            -> objectType ∈ schema.getPossibleTypes returnType)
      -> selectionSetLookupValid schema returnType leftSelectionSet
      -> selectionSetLookupValid schema returnType rightSelectionSet
      -> (∀ objectType,
            objectType ∈ leftPossibleTypes
            -> selectionSetSemanticsReady schema objectType leftSelectionSet)
      -> (∀ objectType,
            objectType ∈ rightPossibleTypes
            -> selectionSetSemanticsReady schema objectType rightSelectionSet)
      -> FieldMerge.fieldsInSetCanMerge schema returnType
          (leftSelectionSet ++ rightSelectionSet)
      -> ∀ leftType,
          leftType ∈ leftPossibleTypes
          -> ∀ rightType,
              rightType ∈ rightPossibleTypes
              -> leftType ≠ rightType
              -> ∀ leftField,
                  leftField
                    ∈ FieldMerge.collectFields schema leftType
                        (normalizeSelectionSet schema leftType leftSelectionSet)
                  -> ∀ rightField,
                      rightField
                        ∈ FieldMerge.collectFields schema rightType
                            (normalizeSelectionSet schema rightType rightSelectionSet)
                      -> leftField.responseName = rightField.responseName
                      -> FieldMerge.fieldsForNameCanMerge schema leftField
                          rightField := by
  intro hleftObjects hleftPossible hrightObjects hrightPossible
    hleftLookupReturn hrightLookupReturn hleftReadyBranches
    hrightReadyBranches hmergeReturn leftType hleftType rightType
    hrightType hdistinct leftField hleftField rightField hrightField
    hresponse
  have hleftObject : schema.objectType leftType :=
    hleftObjects leftType hleftType
  have hrightObject : schema.objectType rightType :=
    hrightObjects rightType hrightType
  have hleftLookup :
      selectionSetLookupValid schema leftType leftSelectionSet :=
    selectionSetLookupValid_of_selectionSetSemanticsReady leftSelectionSet
      (hleftReadyBranches leftType hleftType)
  have hrightLookup :
      selectionSetLookupValid schema rightType rightSelectionSet :=
    selectionSetLookupValid_of_selectionSetSemanticsReady rightSelectionSet
      (hrightReadyBranches rightType hrightType)
  rcases GroundTypeNormalization.collectFields_normalizeSelectionSet_mem_source
      schema hschema leftType leftSelectionSet leftField hleftObject
      (hleftReadyBranches leftType hleftType) hleftField with
    ⟨leftSource, hleftSourceMem, hleftSource⟩
  rcases GroundTypeNormalization.collectFields_normalizeSelectionSet_mem_source
      schema hschema rightType rightSelectionSet rightField hrightObject
      (hrightReadyBranches rightType hrightType) hrightField with
    ⟨rightSource, hrightSourceMem, hrightSource⟩
  rcases
    fieldMerge_collectFields_objectParent_possibleParent schema leftType
      returnType leftSelectionSet leftSource hschema hleftObject
      (hleftPossible leftType hleftType) hleftLookup hleftLookupReturn
      hleftSourceMem with
    ⟨leftAbstract, hleftAbstractMem, hleftSame, hleftShape,
      hleftParent⟩
  rcases
    fieldMerge_collectFields_objectParent_possibleParent schema rightType
      returnType rightSelectionSet rightSource hschema hrightObject
      (hrightPossible rightType hrightType) hrightLookup
      hrightLookupReturn hrightSourceMem with
    ⟨rightAbstract, hrightAbstractMem, hrightSame, hrightShape,
      hrightParent⟩
  have hleftAbstractMemPair :
      leftAbstract ∈ FieldMerge.collectFields schema returnType
        (leftSelectionSet ++ rightSelectionSet) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_left
      (FieldMerge.collectFields schema returnType rightSelectionSet)
      hleftAbstractMem
  have hrightAbstractMemPair :
      rightAbstract ∈ FieldMerge.collectFields schema returnType
        (leftSelectionSet ++ rightSelectionSet) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_right
      (FieldMerge.collectFields schema returnType leftSelectionSet)
      hrightAbstractMem
  have hleftAbstractSource :
      GroundTypeNormalization.NormalizedFieldSource schema leftAbstract
        leftField :=
    GroundTypeNormalization.normalizedFieldSource_of_scopedFieldSameSelection
      hleftSame hleftShape hleftParent hleftSource
  have hrightAbstractSource :
      GroundTypeNormalization.NormalizedFieldSource schema rightAbstract
        rightField :=
    GroundTypeNormalization.normalizedFieldSource_of_scopedFieldSameSelection
      hrightSame hrightShape hrightParent hrightSource
  have habstractResponse :
      leftAbstract.responseName = rightAbstract.responseName :=
    hleftAbstractSource.responseName.trans
      (hresponse.trans hrightAbstractSource.responseName.symm)
  have habstractMerge :
      FieldMerge.fieldsForNameCanMerge schema leftAbstract rightAbstract :=
    FieldMerge.fieldsInSetCanMerge_pair hmergeReturn
      hleftAbstractMemPair hrightAbstractMemPair habstractResponse
  have hleftParentEq :
      leftField.parentType = leftType :=
    GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
      leftType (normalizeSelectionSet schema leftType leftSelectionSet)
      leftField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        leftType leftSelectionSet)
      hleftField
  have hrightParentEq :
      rightField.parentType = rightType :=
    GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
      rightType (normalizeSelectionSet schema rightType rightSelectionSet)
      rightField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        rightType rightSelectionSet)
      hrightField
  apply GroundTypeNormalization.fieldsForNameCanMerge_of_normalizedFieldSources
      hleftAbstractSource hrightAbstractSource hresponse habstractMerge
  intro hparents objectType
  rcases hparents with hparentEq | hnotObject
  · exact False.elim (hdistinct
      (hleftParentEq.symm.trans (hparentEq.trans hrightParentEq)))
  · rcases hnotObject with hleftNotObject | hrightNotObject
    · exact False.elim
        (hleftNotObject (by simpa [hleftParentEq] using hleftObject))
    · exact False.elim
        (hrightNotObject (by simpa [hrightParentEq] using hrightObject))

theorem normalizedDistinctBranchesPairwiseMerge_of_groupSources
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
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> leftField.outputType.namedType = returnType
      -> rightField.outputType.namedType = returnType
      -> ∀ leftType,
          leftType ∈ schema.getPossibleTypes returnType
          -> ∀ rightType,
              rightType ∈ schema.getPossibleTypes returnType
              -> leftType ≠ rightType
              -> ∀ leftBranchField,
                  leftBranchField
                    ∈ FieldMerge.collectFields schema leftType
                        (normalizeSelectionSet schema leftType hleftGroup.childSource)
                  -> ∀ rightBranchField,
                      rightBranchField
                        ∈ FieldMerge.collectFields schema rightType
                            (normalizeSelectionSet schema rightType
                              hrightGroup.childSource)
                      -> leftBranchField.responseName = rightBranchField.responseName
                      -> FieldMerge.fieldsForNameCanMerge schema leftBranchField
                          rightBranchField := by
  intro hobject hsourcePair hresponse hleftReturn hrightReturn
  have hmergeReturn :
      FieldMerge.fieldsInSetCanMerge schema returnType
        (hleftGroup.childSource ++ hrightGroup.childSource) :=
    fieldsInSetCanMerge_groupSources_rawChildSource_pair schema
      variableDefinitions parentType returnType hleftGroup hrightGroup
      hobject hsourcePair hresponse
  have hleftLookup :
      selectionSetLookupValid schema returnType hleftGroup.childSource := by
    simpa [← hleftReturn] using hleftGroup.childLookup
  have hrightLookup :
      selectionSetLookupValid schema returnType hrightGroup.childSource := by
    simpa [← hrightReturn] using hrightGroup.childLookup
  have hleftReady :
      ∀ objectType, objectType ∈ schema.getPossibleTypes returnType ->
        selectionSetSemanticsReady schema objectType
          hleftGroup.childSource := by
    intro objectType hpossible
    exact hleftGroup.childReady objectType (by simpa [hleftReturn] using hpossible)
  have hrightReady :
      ∀ objectType, objectType ∈ schema.getPossibleTypes returnType ->
        selectionSetSemanticsReady schema objectType
          hrightGroup.childSource := by
    intro objectType hpossible
    exact hrightGroup.childReady objectType (by simpa [hrightReturn] using hpossible)
  exact normalizedDistinctBranchesPairwiseMerge_of_abstractMerge_pair
    schema variableDefinitions hschema returnType
    (schema.getPossibleTypes returnType) (schema.getPossibleTypes returnType)
    hleftGroup.childSource hrightGroup.childSource
    (by
      intro objectType hpossible
      exact
        SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
          hschema returnType objectType hpossible)
    (by
      intro objectType hpossible
      exact hpossible)
    (by
      intro objectType hpossible
      exact
        SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
          hschema returnType objectType hpossible)
    (by
      intro objectType hpossible
      exact hpossible)
    hleftLookup hrightLookup hleftReady hrightReady hmergeReturn

theorem possibleTypeNormalizations_fieldsInSetCanMerge_pair_of_groupSources
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType mergeParent returnType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : schema.objectType parentType
      -> FieldMerge.fieldsInSetCanMerge schema parentType leftSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType rightSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> leftField.outputType.namedType = returnType
      -> rightField.outputType.namedType = returnType
      -> (∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType
            -> FieldMerge.fieldsInSetCanMerge schema objectType
                (normalizeSelectionSet schema objectType hleftGroup.childSource
                  ++ normalizeSelectionSet schema objectType hrightGroup.childSource))
      -> FieldMerge.fieldsInSetCanMerge schema mergeParent
          (GroundTypeNormalization.possibleTypeNormalizations schema
              (schema.getPossibleTypes returnType) hleftGroup.childSource
            ++ GroundTypeNormalization.possibleTypeNormalizations schema
                (schema.getPossibleTypes returnType) hrightGroup.childSource) := by
  intro hobject hleftMerge hrightMerge hsourcePair hresponse hleftReturn
    hrightReturn hsamePairs
  apply possibleTypeNormalizations_fieldsInSetCanMerge_pair_any
  · intro leftType hleftType rightType hrightType leftBranchField
      hleftBranchField rightBranchField hrightBranchField hbranchResponse
    by_cases hsame : leftType = rightType
    · subst rightType
      have hleftValid :=
        normalizedFieldGroup_childBranchNormalizedValid schema
          variableDefinitions hschema parentType hleftGroup
          hobject hleftMerge leftType (by simpa [← hleftReturn] using hleftType)
      exact
        GroundTypeNormalization.normalizedBranchFieldsCanMerge_of_normalizedValid
          hleftValid hleftBranchField hrightBranchField hbranchResponse
    · exact
        normalizedDistinctBranchesPairwiseMerge_of_groupSources schema
          variableDefinitions hschema parentType returnType hleftGroup
          hleftGroup hobject
          (GroundTypeNormalization.fieldsInSetCanMerge_self schema
            parentType leftSet hleftMerge)
          rfl hleftReturn hleftReturn leftType hleftType rightType
          hrightType hsame leftBranchField hleftBranchField
          rightBranchField hrightBranchField hbranchResponse
  · intro leftType hleftType rightType hrightType leftBranchField
      hleftBranchField rightBranchField hrightBranchField hbranchResponse
    by_cases hsame : leftType = rightType
    · subst rightType
      have hrightValid :=
        normalizedFieldGroup_childBranchNormalizedValid schema
          variableDefinitions hschema parentType hrightGroup
          hobject hrightMerge leftType
          (by simpa [← hrightReturn] using hleftType)
      exact
        GroundTypeNormalization.normalizedBranchFieldsCanMerge_of_normalizedValid
          hrightValid hleftBranchField hrightBranchField hbranchResponse
    · exact
        normalizedDistinctBranchesPairwiseMerge_of_groupSources schema
          variableDefinitions hschema parentType returnType hrightGroup
          hrightGroup hobject
          (GroundTypeNormalization.fieldsInSetCanMerge_self schema
            parentType rightSet hrightMerge)
          rfl hrightReturn hrightReturn leftType hleftType rightType
          hrightType hsame leftBranchField hleftBranchField
          rightBranchField hrightBranchField hbranchResponse
  · intro leftType hleftType rightType hrightType leftBranchField
      hleftBranchField rightBranchField hrightBranchField hbranchResponse
    by_cases hsame : leftType = rightType
    · subst rightType
      exact FieldMerge.fieldsInSetCanMerge_pair
        (hsamePairs leftType hleftType)
        (by
          rw [FieldMerge.collectFields_append]
          exact List.mem_append_left
            (FieldMerge.collectFields schema leftType
              (normalizeSelectionSet schema leftType
                hrightGroup.childSource))
            hleftBranchField)
        (by
          rw [FieldMerge.collectFields_append]
          exact List.mem_append_right
            (FieldMerge.collectFields schema leftType
              (normalizeSelectionSet schema leftType
                hleftGroup.childSource))
            hrightBranchField)
        hbranchResponse
    · exact
        normalizedDistinctBranchesPairwiseMerge_of_groupSources schema
          variableDefinitions hschema parentType returnType hleftGroup
          hrightGroup hobject hsourcePair hresponse hleftReturn hrightReturn
          leftType hleftType rightType hrightType hsame leftBranchField
          hleftBranchField rightBranchField hrightBranchField hbranchResponse

theorem normalizedFieldGroupSources_childPairs_of_sameReturn
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType returnType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : NormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : leftField.outputType.namedType = returnType
      -> rightField.outputType.namedType = returnType
      -> (objectTypeNameBool schema returnType = true
          -> ∀ mergeParent,
              FieldMerge.fieldsInSetCanMerge schema mergeParent
                (normalizeSelectionSet schema returnType hleftGroup.childSource
                  ++ normalizeSelectionSet schema returnType hrightGroup.childSource))
      -> (objectTypeNameBool schema returnType = false
          -> ∀ mergeParent,
              FieldMerge.fieldsInSetCanMerge schema mergeParent
                (GroundTypeNormalization.possibleTypeNormalizations schema
                    (schema.getPossibleTypes returnType) hleftGroup.childSource
                  ++ GroundTypeNormalization.possibleTypeNormalizations schema
                      (schema.getPossibleTypes returnType)
                      hrightGroup.childSource))
      -> (leftField.parentType = rightField.parentType
          ∨ ¬ schema.objectType leftField.parentType
          ∨ ¬ schema.objectType rightField.parentType)
      -> ∀ mergeParent,
          FieldMerge.fieldsInSetCanMerge schema mergeParent
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
                      hrightGroup.childSource)) := by
  intro hleftReturn hrightReturn hobjectCase habstractCase _hparents
    mergeParent
  by_cases hobjectReturn : objectTypeNameBool schema returnType = true
  · simpa [hleftReturn, hrightReturn, hobjectReturn] using
      hobjectCase hobjectReturn mergeParent
  · have hfalse : objectTypeNameBool schema returnType = false := by
      cases hmatch : objectTypeNameBool schema returnType
      · rfl
      · exact False.elim (hobjectReturn hmatch)
    simpa [hleftReturn, hrightReturn, hfalse] using
      habstractCase hfalse mergeParent

theorem normalizedFieldGroupSources_childPairs_of_sameReturn_and_branches
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
      -> FieldMerge.fieldsInSetCanMerge schema parentType leftSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType rightSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> leftField.outputType.namedType = returnType
      -> rightField.outputType.namedType = returnType
      -> (objectTypeNameBool schema returnType = true
          -> ∀ mergeParent,
              FieldMerge.fieldsInSetCanMerge schema mergeParent
                (normalizeSelectionSet schema returnType hleftGroup.childSource
                  ++ normalizeSelectionSet schema returnType hrightGroup.childSource))
      -> (objectTypeNameBool schema returnType = false
          -> ∀ objectType,
              objectType ∈ schema.getPossibleTypes returnType
              -> FieldMerge.fieldsInSetCanMerge schema objectType
                  (normalizeSelectionSet schema objectType hleftGroup.childSource
                    ++ normalizeSelectionSet schema objectType hrightGroup.childSource))
      -> (leftField.parentType = rightField.parentType
          ∨ ¬ schema.objectType leftField.parentType
          ∨ ¬ schema.objectType rightField.parentType)
      -> ∀ mergeParent,
          FieldMerge.fieldsInSetCanMerge schema mergeParent
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
                      hrightGroup.childSource)) := by
  intro hobject hleftMerge hrightMerge hsourcePair hresponse
    hleftReturn hrightReturn hobjectCase habstractBranches hparents
    mergeParent
  apply normalizedFieldGroupSources_childPairs_of_sameReturn
      schema variableDefinitions parentType returnType hleftGroup hrightGroup
      hleftReturn hrightReturn
  · exact hobjectCase
  · intro habstractReturn mergeParent
    exact
      possibleTypeNormalizations_fieldsInSetCanMerge_pair_of_groupSources
        schema variableDefinitions hschema parentType
        mergeParent returnType hleftGroup hrightGroup hobject hleftMerge
        hrightMerge hsourcePair hresponse hleftReturn hrightReturn
        (habstractBranches habstractReturn)
  · exact hparents

theorem normalizeSelectionSets_fieldsInSetCanMerge_anyParent
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType leftSet rightSet,
        schema.objectType parentType
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
        -> ∀ mergeParent,
            FieldMerge.fieldsInSetCanMerge schema mergeParent
              (normalizeSelectionSet schema parentType leftSet
                ++ normalizeSelectionSet schema parentType rightSet) := by
  intro parentType leftSet rightSet hobject hleftReady hrightReady
    hleftImplementation hrightImplementation hleftMerge hrightMerge
    hsourcePair hleftFree hrightFree hleftFeasible hrightFeasible
    mergeParent
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
  apply fieldsInSetCanMerge_append_of_pairwise
      schema mergeParent
      (normalizeSelectionSet schema parentType leftSet)
      (normalizeSelectionSet schema parentType rightSet)
  · exact normalizedSelectionSetFieldsCanMerge_anyParent hleftValid
  · exact normalizedSelectionSetFieldsCanMerge_anyParent hrightValid
  · intro leftField hleftField rightField hrightField hresponse
    apply normalizedFields_fieldsForNameCanMerge_of_childPairs_anyParent
        schema variableDefinitions hschema parentType
        mergeParent leftSet rightSet leftField rightField hobject
        hleftReady hrightReady hleftImplementation hrightImplementation
        hleftMerge hrightMerge hsourcePair hleftFree hrightFree
        hleftFeasible hrightFeasible
        hleftField hrightField hresponse
    intro leftParentField hleftParentField rightParentField
      hrightParentField hparentResponse leftGroup rightGroup hparents
      childMergeParent
    let returnType := leftParentField.outputType.namedType
    have houtputEq :
        leftParentField.outputType = rightParentField.outputType :=
      normalizedFieldGroupSources_outputType_eq_of_sourcePair schema
        variableDefinitions parentType leftGroup rightGroup hleftParentField
        hrightParentField hsourcePair hparentResponse hparents
    have hrightReturn :
        rightParentField.outputType.namedType = returnType := by
      dsimp [returnType]
      exact (congrArg TypeRef.namedType houtputEq).symm
    by_cases hreturnObject : objectTypeNameBool schema returnType = true
    · have hreturnObjectProp : schema.objectType returnType :=
        objectType_of_objectTypeNameBool_eq_true schema hreturnObject
      have hreturnPossible :
          returnType ∈ schema.getPossibleTypes returnType :=
        List.contains_iff_mem.mp
          (object_typeIncludesObjectBool_self schema hreturnObjectProp)
      have hleftChildReady :
          selectionSetSemanticsReady schema returnType leftGroup.childSource :=
        leftGroup.childReady returnType
          (by
            dsimp [returnType] at hreturnPossible
            exact hreturnPossible)
      have hrightChildReady :
          selectionSetSemanticsReady schema returnType rightGroup.childSource :=
        rightGroup.childReady returnType
          (by simpa [← hrightReturn] using hreturnPossible)
      have hleftChildImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions returnType leftGroup.childSource :=
        leftGroup.childImplementation returnType
          (by
            dsimp [returnType] at hreturnPossible
            exact hreturnPossible)
      have hrightChildImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions returnType rightGroup.childSource :=
        rightGroup.childImplementation returnType
          (by simpa [← hrightReturn] using hreturnPossible)
      have hleftChildFeasible :
          selectionSetTypeConditionFeasible schema returnType [returnType]
            .allFields leftGroup.childSource :=
        leftGroup.childFeasible returnType
          (by
            dsimp [returnType] at hreturnPossible
            exact hreturnPossible)
      have hrightChildFeasible :
          selectionSetTypeConditionFeasible schema returnType [returnType]
            .allFields rightGroup.childSource :=
        rightGroup.childFeasible returnType
          (by simpa [← hrightReturn] using hreturnPossible)
      have hchildSourcePair :
          FieldMerge.fieldsInSetCanMerge schema returnType
            (leftGroup.childSource ++ rightGroup.childSource) :=
        fieldsInSetCanMerge_groupSources_rawChildSource_pair schema
          variableDefinitions parentType returnType leftGroup rightGroup
          hobject hsourcePair hparentResponse
      have hleftChildMerge :
          FieldMerge.fieldsInSetCanMerge schema returnType
            leftGroup.childSource :=
        fieldsInSetCanMerge_append_left schema returnType
          leftGroup.childSource rightGroup.childSource hchildSourcePair
      have hrightChildMerge :
          FieldMerge.fieldsInSetCanMerge schema returnType
            rightGroup.childSource :=
        fieldsInSetCanMerge_append_right schema returnType
          leftGroup.childSource rightGroup.childSource hchildSourcePair
      have hrecursive :=
        normalizeSelectionSets_fieldsInSetCanMerge_anyParent schema
          variableDefinitions hschema returnType
          leftGroup.childSource rightGroup.childSource hreturnObjectProp
          hleftChildReady hrightChildReady hleftChildImplementation
          hrightChildImplementation hleftChildMerge hrightChildMerge
          hchildSourcePair leftGroup.childDirectiveFree
          rightGroup.childDirectiveFree hleftChildFeasible
          hrightChildFeasible childMergeParent
      simpa [returnType, hreturnObject, hrightReturn] using hrecursive
    · have hreturnObjectFalse :
          objectTypeNameBool schema returnType = false := by
        cases hmatch : objectTypeNameBool schema returnType
        · rfl
        · exact False.elim (hreturnObject hmatch)
      have habstract :=
        possibleTypeNormalizations_fieldsInSetCanMerge_pair_of_groupSources
          schema variableDefinitions hschema parentType
          childMergeParent returnType leftGroup rightGroup hobject
          hleftMerge hrightMerge hsourcePair hparentResponse rfl
          hrightReturn
      have hsamePairs :
          ∀ objectType, objectType ∈ schema.getPossibleTypes returnType ->
            FieldMerge.fieldsInSetCanMerge schema objectType
              (normalizeSelectionSet schema objectType leftGroup.childSource
                ++ normalizeSelectionSet schema objectType
                  rightGroup.childSource) := by
        intro objectType hpossible
        have hobjectType :
            schema.objectType objectType :=
          SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema returnType objectType hpossible
        have hleftChildReady :
            selectionSetSemanticsReady schema objectType
              leftGroup.childSource :=
          leftGroup.childReady objectType
            (by
              dsimp [returnType] at hpossible
              exact hpossible)
        have hrightChildReady :
            selectionSetSemanticsReady schema objectType
              rightGroup.childSource :=
          rightGroup.childReady objectType
            (by simpa [← hrightReturn] using hpossible)
        have hleftChildImplementation :
            Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions objectType leftGroup.childSource :=
          leftGroup.childImplementation objectType
            (by
              dsimp [returnType] at hpossible
              exact hpossible)
        have hrightChildImplementation :
            Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions objectType rightGroup.childSource :=
          rightGroup.childImplementation objectType
            (by simpa [← hrightReturn] using hpossible)
        have hleftChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType]
              .allFields leftGroup.childSource :=
          leftGroup.childFeasible objectType
            (by
              dsimp [returnType] at hpossible
              exact hpossible)
        have hrightChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType]
              .allFields rightGroup.childSource :=
          rightGroup.childFeasible objectType
            (by simpa [← hrightReturn] using hpossible)
        have hchildSourcePair :
            FieldMerge.fieldsInSetCanMerge schema objectType
              (leftGroup.childSource ++ rightGroup.childSource) :=
          fieldsInSetCanMerge_groupSources_rawChildSource_pair schema
            variableDefinitions parentType objectType leftGroup rightGroup
            hobject hsourcePair hparentResponse
        have hleftChildMerge :
            FieldMerge.fieldsInSetCanMerge schema objectType
              leftGroup.childSource :=
          fieldsInSetCanMerge_append_left schema objectType
            leftGroup.childSource rightGroup.childSource hchildSourcePair
        have hrightChildMerge :
            FieldMerge.fieldsInSetCanMerge schema objectType
              rightGroup.childSource :=
          fieldsInSetCanMerge_append_right schema objectType
            leftGroup.childSource rightGroup.childSource hchildSourcePair
        exact
          normalizeSelectionSets_fieldsInSetCanMerge_anyParent schema
            variableDefinitions hschema objectType
            leftGroup.childSource rightGroup.childSource hobjectType
            hleftChildReady hrightChildReady hleftChildImplementation
            hrightChildImplementation hleftChildMerge hrightChildMerge
            hchildSourcePair leftGroup.childDirectiveFree
            rightGroup.childDirectiveFree hleftChildFeasible
            hrightChildFeasible objectType
      simpa [returnType, hreturnObjectFalse, hrightReturn] using
        habstract hsamePairs
termination_by _parentType leftSet rightSet =>
  SelectionSet.size leftSet + SelectionSet.size rightSet
decreasing_by
  all_goals
    have hleftLt := leftGroup.childSource_size_lt
    have hrightLt := rightGroup.childSource_size_lt
    omega

theorem possibleTypeNormalizations_fieldsInSetCanMerge_pair_of_same_or_distinct
    (schema : Schema) (mergeParent : Name)
    (leftPossibleTypes rightPossibleTypes : List Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    : (∀ leftType,
        leftType ∈ leftPossibleTypes
        -> ∀ rightType,
            rightType ∈ leftPossibleTypes
            -> ∀ leftField,
                leftField
                  ∈ FieldMerge.collectFields schema leftType
                      (normalizeSelectionSet schema leftType leftSelectionSet)
                -> ∀ rightField,
                    rightField
                      ∈ FieldMerge.collectFields schema rightType
                          (normalizeSelectionSet schema rightType leftSelectionSet)
                    -> leftField.responseName = rightField.responseName
                    -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
      -> (∀ leftType,
            leftType ∈ rightPossibleTypes
            -> ∀ rightType,
                rightType ∈ rightPossibleTypes
                -> ∀ leftField,
                    leftField
                      ∈ FieldMerge.collectFields schema leftType
                          (normalizeSelectionSet schema leftType rightSelectionSet)
                    -> ∀ rightField,
                        rightField
                          ∈ FieldMerge.collectFields schema rightType
                              (normalizeSelectionSet schema rightType rightSelectionSet)
                        -> leftField.responseName = rightField.responseName
                        -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
      -> (∀ objectType,
            objectType ∈ leftPossibleTypes
            -> objectType ∈ rightPossibleTypes
            -> ∀ leftField,
                leftField
                  ∈ FieldMerge.collectFields schema objectType
                      (normalizeSelectionSet schema objectType leftSelectionSet)
                -> ∀ rightField,
                    rightField
                      ∈ FieldMerge.collectFields schema objectType
                          (normalizeSelectionSet schema objectType rightSelectionSet)
                    -> leftField.responseName = rightField.responseName
                    -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
      -> (∀ leftType,
            leftType ∈ leftPossibleTypes
            -> ∀ rightType,
                rightType ∈ rightPossibleTypes
                -> leftType ≠ rightType
                -> ∀ leftField,
                    leftField
                      ∈ FieldMerge.collectFields schema leftType
                          (normalizeSelectionSet schema leftType leftSelectionSet)
                    -> ∀ rightField,
                        rightField
                          ∈ FieldMerge.collectFields schema rightType
                              (normalizeSelectionSet schema rightType rightSelectionSet)
                        -> leftField.responseName = rightField.responseName
                        -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
      -> FieldMerge.fieldsInSetCanMerge schema mergeParent
          (GroundTypeNormalization.possibleTypeNormalizations schema
              leftPossibleTypes leftSelectionSet
            ++ GroundTypeNormalization.possibleTypeNormalizations schema
                rightPossibleTypes rightSelectionSet) := by
  intro hleftPairwise hrightPairwise hsame hdistinct
  apply possibleTypeNormalizations_fieldsInSetCanMerge_pair_any
  · exact hleftPairwise
  · exact hrightPairwise
  · intro leftType hleftType rightType hrightType leftField hleftField
      rightField hrightField hresponse
    by_cases heq : leftType = rightType
    · subst rightType
      exact hsame leftType hleftType hrightType leftField hleftField
        rightField hrightField hresponse
    · exact hdistinct leftType hleftType rightType hrightType heq
        leftField hleftField rightField hrightField hresponse

end CompleteNormalization

end NormalForm

end GraphQL
