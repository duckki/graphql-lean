import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Support.Sources

/-!
Possible-type branch validity facts for ground-type normalization.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem fieldsInSetCanMerge_nil (schema : Schema) (parentType : Name)
    : FieldMerge.fieldsInSetCanMerge schema parentType [] := by
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType [] ?_
  simp [FieldMerge.collectFields]

theorem fieldsInSetCanMerge_self
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (selectionSet ++ selectionSet) := by
  intro hmerge
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (selectionSet ++ selectionSet) ?_
  dsimp
  intro left hleft right hright hresponse
  rw [FieldMerge.collectFields_append] at hleft hright
  rcases List.mem_append.mp hleft with hleft | hleft
  · rcases List.mem_append.mp hright with hright | hright
    · exact FieldMerge.fieldsInSetCanMerge_pair hmerge hleft hright
        hresponse
    · exact FieldMerge.fieldsInSetCanMerge_pair hmerge hleft hright
        hresponse
  · rcases List.mem_append.mp hright with hright | hright
    · exact FieldMerge.fieldsInSetCanMerge_pair hmerge hleft hright
        hresponse
    · exact FieldMerge.fieldsInSetCanMerge_pair hmerge hleft hright
        hresponse

theorem normalizedSelectionSetValid_nil
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    : NormalizedSelectionSetValid schema variableDefinitions parentType [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Validation.selectionSetValid]
  · exact selectionSetValidInPossibleTypes_nil schema variableDefinitions
      parentType
  · exact fieldsInSetCanMerge_nil schema parentType
  · intro mergeParent
    exact fieldsInSetCanMerge_nil schema mergeParent

theorem possibleTypeNormalizations_selectionSetValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (returnType : Name)
    : ∀ possibleTypes selectionSet,
        (∀ objectType, objectType ∈ possibleTypes -> schema.objectType objectType)
        -> (∀ objectType,
              objectType ∈ possibleTypes
              -> objectType ∈ schema.getPossibleTypes returnType)
        -> (∀ objectType,
              objectType ∈ possibleTypes
              -> NormalizedSelectionSetValid schema variableDefinitions objectType
                  (normalizeSelectionSet schema objectType selectionSet))
        -> Validation.selectionSetValid schema variableDefinitions returnType
            (possibleTypeNormalizations schema possibleTypes selectionSet)
  | [], selectionSet, _hobjects, _hpossible, _hbranches => by
      simp [possibleTypeNormalizations, Validation.selectionSetValid]
  | objectType :: rest, selectionSet, hobjects, hpossible, hbranches => by
      cases hnormalized :
          normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simp [possibleTypeNormalizations, hnormalized]
          exact possibleTypeNormalizations_selectionSetValid schema
            variableDefinitions returnType rest selectionSet
            (fun candidate hcandidate =>
              hobjects candidate (List.mem_cons_of_mem objectType hcandidate))
            (fun candidate hcandidate =>
              hpossible candidate
                (List.mem_cons_of_mem objectType hcandidate))
            (fun candidate hcandidate =>
              hbranches candidate
                (List.mem_cons_of_mem objectType hcandidate))
      | cons selection normalizedRest =>
          have hbranch :
              NormalizedSelectionSetValid schema variableDefinitions
                objectType (selection :: normalizedRest) := by
            simpa [hnormalized] using
              hbranches objectType (by simp)
          have htail :
              Validation.selectionSetValid schema variableDefinitions
                returnType
                (possibleTypeNormalizations schema rest selectionSet) :=
            possibleTypeNormalizations_selectionSetValid schema
              variableDefinitions returnType rest selectionSet
              (fun candidate hcandidate =>
                hobjects candidate
                  (List.mem_cons_of_mem objectType hcandidate))
              (fun candidate hcandidate =>
                hpossible candidate
                  (List.mem_cons_of_mem objectType hcandidate))
              (fun candidate hcandidate =>
                hbranches candidate
                  (List.mem_cons_of_mem objectType hcandidate))
          have htailValid :
              ∀ candidate,
                candidate ∈
                    possibleTypeNormalizations schema rest selectionSet ->
                  Validation.selectionValid schema variableDefinitions
                    returnType candidate := by
            simpa [Validation.selectionSetValid] using htail
          unfold Validation.selectionSetValid
          intro candidate hcandidate
          simp [possibleTypeNormalizations, hnormalized] at hcandidate
          rcases hcandidate with hcandidate | hcandidate
          · subst candidate
            have hcomposite :
                schema.isCompositeType objectType :=
              objectType_isCompositeType (schema := schema)
                (hobjects objectType (by simp))
            have hoverlap :
                schema.typesOverlap returnType objectType :=
              typesOverlap_possible_object schema
                (hpossible objectType (by simp))
                (hobjects objectType (by simp))
            simpa [Validation.selectionValid, Validation.directivesValid,
              hcomposite, hoverlap] using hbranch.selectionSetValid
          · exact htailValid candidate
              (by simpa [possibleTypeNormalizations] using hcandidate)

theorem possibleTypeNormalizations_validInPossibleTypes
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    : ∀ possibleTypes selectionSet,
        (∀ objectType, objectType ∈ possibleTypes -> schema.objectType objectType)
        -> (∀ objectType,
              objectType ∈ possibleTypes
              -> NormalizedSelectionSetValid schema variableDefinitions objectType
                  (normalizeSelectionSet schema objectType selectionSet))
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (possibleTypeNormalizations schema possibleTypes selectionSet)
  | [], selectionSet, _hobjects, _hbranches => by
      simp [possibleTypeNormalizations,
        Validation.selectionSetValidInPossibleTypes]
  | objectType :: rest, selectionSet, hobjects, hbranches => by
      cases hnormalized :
          normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simp [possibleTypeNormalizations, hnormalized]
          exact possibleTypeNormalizations_validInPossibleTypes schema
            variableDefinitions parentType rest selectionSet
            (fun candidate hcandidate =>
              hobjects candidate (List.mem_cons_of_mem objectType hcandidate))
            (fun candidate hcandidate =>
              hbranches candidate
                (List.mem_cons_of_mem objectType hcandidate))
      | cons selection normalizedRest =>
          have hbranch :
              NormalizedSelectionSetValid schema variableDefinitions
                objectType (selection :: normalizedRest) := by
            simpa [hnormalized] using
              hbranches objectType (by simp)
          have htail :
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions parentType
                (possibleTypeNormalizations schema rest selectionSet) :=
            possibleTypeNormalizations_validInPossibleTypes schema
              variableDefinitions parentType rest selectionSet
              (fun candidate hcandidate =>
                hobjects candidate
                  (List.mem_cons_of_mem objectType hcandidate))
              (fun candidate hcandidate =>
                hbranches candidate
                  (List.mem_cons_of_mem objectType hcandidate))
          simp [possibleTypeNormalizations, hnormalized,
            Validation.selectionSetValidInPossibleTypes,
            Validation.selectionValidInPossibleTypes]
          exact ⟨
            (fun _hoverlap childType hchildType => by
              have hchildEq : childType = objectType :=
                object_typeIncludesObjectBool_eq_self schema
                  (hobjects objectType (by simp))
                  (List.contains_iff_mem.mpr hchildType)
              simpa [hchildEq] using hbranch.validInPossibleTypes),
            htail⟩

theorem collectFields_possibleTypeNormalizations_mem
    (schema : Schema) (mergeParent : Name)
    : ∀ possibleTypes selectionSet scopedField,
        scopedField
          ∈ FieldMerge.collectFields schema mergeParent
              (possibleTypeNormalizations schema possibleTypes selectionSet)
        -> ∃ objectType,
            objectType ∈ possibleTypes
            ∧ scopedField
              ∈ FieldMerge.collectFields schema objectType
                  (normalizeSelectionSet schema objectType selectionSet)
  | [], selectionSet, scopedField, hfield => by
      simp [possibleTypeNormalizations, FieldMerge.collectFields] at hfield
  | objectType :: rest, selectionSet, scopedField, hfield => by
      cases hnormalized :
          normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simp [possibleTypeNormalizations, hnormalized] at hfield
          rcases collectFields_possibleTypeNormalizations_mem schema
              mergeParent rest selectionSet scopedField hfield with
            ⟨branchType, hbranchMem, hbranchField⟩
          exact ⟨branchType, List.mem_cons_of_mem objectType hbranchMem,
            hbranchField⟩
      | cons selection normalizedRest =>
          simp [possibleTypeNormalizations, hnormalized,
            FieldMerge.collectFields] at hfield
          rcases hfield with hhead | htail
          · exact ⟨objectType, by simp, by simpa [hnormalized] using hhead⟩
          · rcases collectFields_possibleTypeNormalizations_mem schema
                mergeParent rest selectionSet scopedField htail with
              ⟨branchType, hbranchMem, hbranchField⟩
            exact ⟨branchType, List.mem_cons_of_mem objectType hbranchMem,
              hbranchField⟩

theorem possibleTypeNormalizations_fieldsInSetCanMerge
    (schema : Schema) (mergeParent : Name)
    : ∀ possibleTypes selectionSet,
        (∀ leftType,
          leftType ∈ possibleTypes
          -> ∀ rightType,
              rightType ∈ possibleTypes
              -> ∀ leftField,
                  leftField
                    ∈ FieldMerge.collectFields schema leftType
                        (normalizeSelectionSet schema leftType selectionSet)
                  -> ∀ rightField,
                      rightField
                        ∈ FieldMerge.collectFields schema rightType
                            (normalizeSelectionSet schema rightType selectionSet)
                      -> leftField.responseName = rightField.responseName
                      -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
        -> FieldMerge.fieldsInSetCanMerge schema mergeParent
            (possibleTypeNormalizations schema possibleTypes selectionSet)
  | possibleTypes, selectionSet, hpairwise => by
      unfold FieldMerge.fieldsInSetCanMerge
      refine FieldMerge.FieldsInSetCanMerge.intro mergeParent
        (possibleTypeNormalizations schema possibleTypes selectionSet) ?_
      dsimp
      intro left hleft right hright hresponse
      rcases collectFields_possibleTypeNormalizations_mem schema
          mergeParent possibleTypes selectionSet left hleft with
        ⟨leftType, hleftType, hleftField⟩
      rcases collectFields_possibleTypeNormalizations_mem schema
          mergeParent possibleTypes selectionSet right hright with
        ⟨rightType, hrightType, hrightField⟩
      exact hpairwise leftType hleftType rightType hrightType left
        hleftField right hrightField hresponse

theorem possibleTypeNormalizations_fieldsInSetCanMerge_self
    (schema : Schema) (mergeParent : Name)
    : ∀ possibleTypes selectionSet,
        (∀ leftType,
          leftType ∈ possibleTypes
          -> ∀ rightType,
              rightType ∈ possibleTypes
              -> ∀ leftField,
                  leftField
                    ∈ FieldMerge.collectFields schema leftType
                        (normalizeSelectionSet schema leftType selectionSet)
                  -> ∀ rightField,
                      rightField
                        ∈ FieldMerge.collectFields schema rightType
                            (normalizeSelectionSet schema rightType selectionSet)
                      -> leftField.responseName = rightField.responseName
                      -> FieldMerge.fieldsForNameCanMerge schema leftField rightField)
        -> FieldMerge.fieldsInSetCanMerge schema mergeParent
            (possibleTypeNormalizations schema possibleTypes selectionSet
              ++ possibleTypeNormalizations schema possibleTypes selectionSet)
  | possibleTypes, selectionSet, hpairwise => by
      unfold FieldMerge.fieldsInSetCanMerge
      refine FieldMerge.FieldsInSetCanMerge.intro mergeParent
        (possibleTypeNormalizations schema possibleTypes selectionSet
          ++ possibleTypeNormalizations schema possibleTypes selectionSet) ?_
      dsimp
      intro left hleft right hright hresponse
      rw [FieldMerge.collectFields_append] at hleft hright
      rcases List.mem_append.mp hleft with hleft | hleft
      · rcases collectFields_possibleTypeNormalizations_mem schema
            mergeParent possibleTypes selectionSet left hleft with
          ⟨leftType, hleftType, hleftField⟩
        rcases List.mem_append.mp hright with hright | hright
        · rcases collectFields_possibleTypeNormalizations_mem schema
              mergeParent possibleTypes selectionSet right hright with
            ⟨rightType, hrightType, hrightField⟩
          exact hpairwise leftType hleftType rightType hrightType left
            hleftField right hrightField hresponse
        · rcases collectFields_possibleTypeNormalizations_mem schema
              mergeParent possibleTypes selectionSet right hright with
            ⟨rightType, hrightType, hrightField⟩
          exact hpairwise leftType hleftType rightType hrightType left
            hleftField right hrightField hresponse
      · rcases collectFields_possibleTypeNormalizations_mem schema
            mergeParent possibleTypes selectionSet left hleft with
          ⟨leftType, hleftType, hleftField⟩
        rcases List.mem_append.mp hright with hright | hright
        · rcases collectFields_possibleTypeNormalizations_mem schema
              mergeParent possibleTypes selectionSet right hright with
            ⟨rightType, hrightType, hrightField⟩
          exact hpairwise leftType hleftType rightType hrightType left
            hleftField right hrightField hresponse
        · rcases collectFields_possibleTypeNormalizations_mem schema
              mergeParent possibleTypes selectionSet right hright with
            ⟨rightType, hrightType, hrightField⟩
          exact hpairwise leftType hleftType rightType hrightType left
            hleftField right hrightField hresponse

theorem possibleTypeNormalizations_fieldsInSetCanMerge_pair
    (schema : Schema) (mergeParent : Name)
    : ∀ possibleTypes leftSelectionSet rightSelectionSet,
        FieldMerge.fieldsInSetCanMerge schema mergeParent
          (possibleTypeNormalizations schema possibleTypes leftSelectionSet)
        -> FieldMerge.fieldsInSetCanMerge schema mergeParent
            (possibleTypeNormalizations schema possibleTypes rightSelectionSet)
        -> (∀ leftType,
              leftType ∈ possibleTypes
              -> ∀ rightType,
                  rightType ∈ possibleTypes
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
            (possibleTypeNormalizations schema possibleTypes leftSelectionSet
              ++ possibleTypeNormalizations schema possibleTypes rightSelectionSet)
  | possibleTypes, leftSelectionSet, rightSelectionSet, hleftMerge,
      hrightMerge, hpairwise => by
      unfold FieldMerge.fieldsInSetCanMerge
      refine FieldMerge.FieldsInSetCanMerge.intro mergeParent
        (possibleTypeNormalizations schema possibleTypes leftSelectionSet
          ++ possibleTypeNormalizations schema possibleTypes
            rightSelectionSet) ?_
      dsimp
      intro left hleft right hright hresponse
      rw [FieldMerge.collectFields_append] at hleft hright
      rcases List.mem_append.mp hleft with hleft | hleft
      · rcases collectFields_possibleTypeNormalizations_mem schema
            mergeParent possibleTypes leftSelectionSet left hleft with
          ⟨leftType, hleftType, hleftField⟩
        rcases List.mem_append.mp hright with hright | hright
        · exact FieldMerge.fieldsInSetCanMerge_pair hleftMerge hleft hright
            hresponse
        · rcases collectFields_possibleTypeNormalizations_mem schema
              mergeParent possibleTypes rightSelectionSet right hright with
            ⟨rightType, hrightType, hrightField⟩
          exact hpairwise leftType hleftType rightType hrightType left
            hleftField right hrightField hresponse
      · rcases collectFields_possibleTypeNormalizations_mem schema
            mergeParent possibleTypes rightSelectionSet left hleft with
          ⟨leftType, hleftType, hleftField⟩
        rcases List.mem_append.mp hright with hright | hright
        · rcases collectFields_possibleTypeNormalizations_mem schema
              mergeParent possibleTypes leftSelectionSet right hright with
            ⟨rightType, hrightType, hrightField⟩
          exact FieldMerge.fieldsForNameCanMerge_symm
            (hpairwise rightType hrightType leftType hleftType right
              hrightField left hleftField hresponse.symm)
        · exact FieldMerge.fieldsInSetCanMerge_pair hrightMerge hleft hright
            hresponse

theorem possibleTypeNormalizations_normalizedValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (returnType : Name) (possibleTypeNames : List Name)
    (selectionSet : List Selection)
    : (∀ objectType, objectType ∈ possibleTypeNames -> schema.objectType objectType)
      -> (∀ objectType,
            objectType ∈ possibleTypeNames
            -> objectType ∈ schema.getPossibleTypes returnType)
      -> (∀ objectType,
            objectType ∈ possibleTypeNames
            -> NormalizedSelectionSetValid schema variableDefinitions objectType
                (normalizeSelectionSet schema objectType selectionSet))
      -> normalizedDistinctBranchesPairwiseMerge schema possibleTypeNames selectionSet
      -> NormalizedSelectionSetValid schema variableDefinitions returnType
          (possibleTypeNormalizations schema possibleTypeNames selectionSet) := by
  intro hobjects hpossible hbranches hdistinct
  have hpairwise :
      normalizedBranchesPairwiseMerge schema possibleTypeNames
        selectionSet :=
    normalizedBranchesPairwiseMerge_of_distinct
      (variableDefinitions := variableDefinitions) hbranches hdistinct
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact possibleTypeNormalizations_selectionSetValid schema
      variableDefinitions returnType possibleTypeNames selectionSet
      hobjects hpossible hbranches
  · exact possibleTypeNormalizations_validInPossibleTypes schema
      variableDefinitions returnType possibleTypeNames selectionSet
      hobjects hbranches
  · exact possibleTypeNormalizations_fieldsInSetCanMerge schema returnType
      possibleTypeNames selectionSet hpairwise
  · intro mergeParent
    exact possibleTypeNormalizations_fieldsInSetCanMerge_self schema
      mergeParent possibleTypeNames selectionSet hpairwise

theorem possibleTypeNormalizations_fieldsInSetCanMerge_pair_of_normalizedValid
    (schema : Schema) (mergeParent : Name) (possibleTypeNames : List Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    : (∀ leftType,
        leftType ∈ possibleTypeNames
        -> ∀ rightType,
            rightType ∈ possibleTypeNames
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
            leftType ∈ possibleTypeNames
            -> ∀ rightType,
                rightType ∈ possibleTypeNames
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
            leftType ∈ possibleTypeNames
            -> ∀ rightType,
                rightType ∈ possibleTypeNames
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
          (possibleTypeNormalizations schema possibleTypeNames leftSelectionSet
            ++ possibleTypeNormalizations schema possibleTypeNames
                rightSelectionSet) := by
  intro hleftPairwise hrightPairwise hcross
  apply possibleTypeNormalizations_fieldsInSetCanMerge_pair
  · exact possibleTypeNormalizations_fieldsInSetCanMerge schema mergeParent
      possibleTypeNames leftSelectionSet hleftPairwise
  · exact possibleTypeNormalizations_fieldsInSetCanMerge schema mergeParent
      possibleTypeNames rightSelectionSet hrightPairwise
  · exact hcross

theorem fieldSelectionSetValid_normalized_of_source
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fieldDefinition : FieldDefinition}
    {sourceSubselections normalizedSubselections : List Selection}
    : Validation.fieldSelectionSetValid schema variableDefinitions
        fieldDefinition sourceSubselections
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType normalizedSubselections
      -> (schema.isCompositeType fieldDefinition.outputType.namedType
          -> normalizedSubselections ≠ [])
      -> (leafTypeNameBool schema fieldDefinition.outputType.namedType = true
          -> normalizedSubselections = [])
      -> Validation.fieldSelectionSetValid schema variableDefinitions
          fieldDefinition normalizedSubselections := by
  intro hsource hnormalizedValid hnormalizedNonempty hnilIfLeaf
  have houtput :
      fieldDefinition.outputType.isOutputType schema :=
    Validation.fieldSelectionSetValid_outputType hsource
  simp [Validation.fieldSelectionSetValid]
  constructor
  · exact houtput
  · simp [Validation.fieldSelectionSetValid] at hsource
    rcases hsource.2 with hsourceLeaf | hsourceComposite
    · have hleafBool :
          leafTypeNameBool schema fieldDefinition.outputType.namedType =
            true :=
        leafTypeNameBool_eq_true_of_isLeafType schema hsourceLeaf.1
      exact Or.inl
        ⟨hsourceLeaf.1, hnilIfLeaf hleafBool⟩
    · exact Or.inr
        ⟨hsourceComposite.1, hnormalizedNonempty hsourceComposite.1,
          hnormalizedValid⟩

theorem normalizedField_selectionValidInPossibleTypes
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {sourceSubselections normalizedSubselections : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionValidInPossibleTypes schema variableDefinitions
        parentType
        (Selection.field responseName fieldName arguments [] sourceSubselections)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType normalizedSubselections
      -> (schema.isCompositeType fieldDefinition.outputType.namedType
          -> normalizedSubselections ≠ [])
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          fieldDefinition.outputType.namedType normalizedSubselections
      -> (∀ objectType,
            objectType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
            -> Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions objectType normalizedSubselections)
      -> (leafTypeNameBool schema fieldDefinition.outputType.namedType = true
          -> normalizedSubselections = [])
      -> Validation.selectionValidInPossibleTypes schema variableDefinitions
          parentType
          (Selection.field responseName fieldName arguments []
            normalizedSubselections) := by
  intro hsourceImplementation hlookup hnormalizedValid hnormalizedNonempty
    hnormalizedImplementation hnormalizedPossible hnilIfLeaf
  have hsourceSelection :
      Validation.selectionValid schema variableDefinitions parentType
        (Selection.field responseName fieldName arguments []
          sourceSubselections) := by
    simpa [Validation.selectionValidInPossibleTypes, hlookup] using
      hsourceImplementation.1
  rcases Validation.selectionValid_field_lookup hsourceSelection with
    ⟨sourceDefinition, hsourceLookup, harguments, hsourceChild⟩
  have hdefinitionEq : sourceDefinition = fieldDefinition := by
    rw [hlookup] at hsourceLookup
    cases hsourceLookup
    rfl
  subst sourceDefinition
  simp [Validation.selectionValidInPossibleTypes, hlookup]
  constructor
  · simp [Validation.selectionValid, Validation.directivesValid, hlookup]
    exact ⟨harguments,
      fieldSelectionSetValid_normalized_of_source
        hsourceChild hnormalizedValid hnormalizedNonempty hnilIfLeaf⟩
  · exact hnormalizedPossible

end GroundTypeNormalization

end NormalForm

end GraphQL
