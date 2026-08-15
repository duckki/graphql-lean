import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedObservableSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedObjectChildLift
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedPairedPathRootSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedContextualSeparation

/-!
Valid-normal semantic separation for focused diff traces.

This module closes the observable-trace case split used by the public
uniqueness theorem. Composite field-head differences use paired selected paths;
recursive child differences use finite-support contextual witnesses.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_observable_trace
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {supportSelectionSets : List (List Selection)} {minFuel : Nat}
    {responsePath : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> (∀ supportSelectionSet,
            supportSelectionSet ∈ supportSelectionSets
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  supportSelectionSet
                ∧ selectionSetDirectiveFree supportSelectionSet
                ∧ selectionSetNormal schema parentType supportSelectionSet)
      -> NormalSelectionSetDiffObservableTrace schema parentType left right responsePath
      -> ∃ runtimeType,
          selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
            parentType runtimeType left right
            (fun selectionSet => selectionSet ∈ supportSelectionSets)
            minFuel := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hsupportValid htrace
  revert hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hsupportValid
  revert leftVariableDefinitions rightVariableDefinitions supportSelectionSets
    minFuel
  induction htrace with
  | objectLeftResponseName hobject hleftMem hrightNoResponseName =>
      rename_i parentType left right responseName fieldName arguments
        directives childSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      exact ⟨
        parentType,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_left_responseName_diff_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (minFuel := minFuel) hschema
          hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal hobject
          hsupportValid hleftMem hrightNoResponseName
      ⟩
  | objectRightResponseName hobject hrightMem hleftNoResponseName =>
      rename_i parentType left right responseName fieldName arguments
        directives childSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      exact ⟨
        parentType,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_right_responseName_diff_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (minFuel := minFuel) hschema
          hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal hobject
          hsupportValid hrightMem hleftNoResponseName
      ⟩
  | objectFieldNameLeaf hobject hleftMem hrightMem hleftLookup
      hrightLookup hleftLeaf hrightLeaf hfieldDiff =>
      rename_i parentType left right responseName leftFieldName rightFieldName
        leftArguments rightArguments leftDirectives rightDirectives
        leftChildSelectionSet rightChildSelectionSet leftFieldDefinition
        rightFieldDefinition
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      exact ⟨
        parentType,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_fieldName_diff_leaf_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (minFuel := minFuel) hschema
          hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal hobject
          hsupportValid hleftMem hrightMem hleftLookup hrightLookup hleftLeaf hrightLeaf
          hfieldDiff
      ⟩
  | objectFieldNameCompositeLeft hobject hleftMem hrightMem hleftLookup
      hrightLookup hleftComposite _hobservable hfieldDiff =>
      rename_i parentType left right responseName leftFieldName rightFieldName
        leftArguments rightArguments leftDirectives rightDirectives
        leftChildSelectionSet rightChildSelectionSet leftFieldDefinition
        rightFieldDefinition childPath
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      by_cases hrightLeaf :
          (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
            schema = false
      · have hwitness :
            selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
              parentType parentType right left
              (fun selectionSet => selectionSet ∈ supportSelectionSets)
              minFuel :=
          selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_fieldName_diff_left_leaf_right_composite_finiteSupport
            (schema := schema)
            (leftVariableDefinitions := rightVariableDefinitions)
            (rightVariableDefinitions := leftVariableDefinitions)
            (parentType := parentType) (left := right) (right := left)
            (supportSelectionSets := supportSelectionSets)
            (responseName := responseName)
            (leftFieldName := rightFieldName)
            (rightFieldName := leftFieldName)
            (leftArguments := rightArguments)
            (rightArguments := leftArguments)
            (leftDirectives := rightDirectives)
            (rightDirectives := leftDirectives)
            (leftChildSelectionSet := rightChildSelectionSet)
            (rightChildSelectionSet := leftChildSelectionSet)
            (leftFieldDefinition := rightFieldDefinition)
            (rightFieldDefinition := leftFieldDefinition)
            (minFuel := minFuel)
            hschema hrightValid hleftValid hrightFree hleftFree
            hrightNormal hleftNormal hobject hsupportValid hrightMem
            hleftMem hrightLookup hleftLookup hrightLeaf hleftComposite
            (by
              intro hsame
              exact hfieldDiff hsame.symm)
        exact ⟨
          parentType,
          selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_symm hwitness
        ⟩
      · have hrightComposite :
            (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
              schema = true := by
          cases h :
              (TypeRef.named
                rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema <;>
            simp [h] at hrightLeaf ⊢
        have hrightNotLeft :
            ∀ arguments,
              Argument.argumentsEquivalent arguments rightArguments ->
                ¬ fieldProbeTarget parentType leftFieldName leftArguments
                  parentType rightFieldName arguments := by
          intro arguments _hrightArgs hleftTarget
          exact hfieldDiff hleftTarget.2.1.symm
        exact ⟨
          parentType,
          selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_field_head_diff_composite_pairedPath_finiteSupport
            (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
            (rightVariableDefinitions := rightVariableDefinitions)
            (parentType := parentType) (left := left) (right := right)
            (supportSelectionSets := supportSelectionSets) (minFuel := minFuel) hschema
            hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal hobject
            hsupportValid hleftMem hrightMem hleftLookup hrightLookup hleftComposite
            hrightComposite hrightNotLeft
        ⟩
  | objectFieldNameCompositeRight hobject hleftMem hrightMem hleftLookup
      hrightLookup hrightComposite _hobservable hfieldDiff =>
      rename_i parentType left right responseName leftFieldName rightFieldName
        leftArguments rightArguments leftDirectives rightDirectives
        leftChildSelectionSet rightChildSelectionSet leftFieldDefinition
        rightFieldDefinition childPath
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      by_cases hleftLeaf :
          (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
            schema = false
      · exact ⟨
          parentType,
          selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_fieldName_diff_left_leaf_right_composite_finiteSupport
            (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
            (rightVariableDefinitions := rightVariableDefinitions)
            (parentType := parentType) (left := left) (right := right)
            (supportSelectionSets := supportSelectionSets) (minFuel := minFuel) hschema
            hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal hobject
            hsupportValid hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
            hrightComposite hfieldDiff
        ⟩
      · have hleftComposite :
            (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
              schema = true := by
          cases h :
              (TypeRef.named
                leftFieldDefinition.outputType.namedType).isCompositeBool
                  schema <;>
            simp [h] at hleftLeaf ⊢
        have hrightNotLeft :
            ∀ arguments,
              Argument.argumentsEquivalent arguments rightArguments ->
                ¬ fieldProbeTarget parentType leftFieldName leftArguments
                  parentType rightFieldName arguments := by
          intro arguments _hrightArgs hleftTarget
          exact hfieldDiff hleftTarget.2.1.symm
        exact ⟨
          parentType,
          selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_field_head_diff_composite_pairedPath_finiteSupport
            (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
            (rightVariableDefinitions := rightVariableDefinitions)
            (parentType := parentType) (left := left) (right := right)
            (supportSelectionSets := supportSelectionSets) (minFuel := minFuel) hschema
            hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal hobject
            hsupportValid hleftMem hrightMem hleftLookup hrightLookup hleftComposite
            hrightComposite hrightNotLeft
        ⟩
  | objectArgumentsLeaf hobject hleftMem hrightMem hlookup hleaf
      hargumentsDiff =>
      rename_i parentType left right responseName fieldName leftArguments
        rightArguments leftDirectives rightDirectives leftChildSelectionSet
        rightChildSelectionSet fieldDefinition
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      exact ⟨
        parentType,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_arguments_diff_leaf_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (minFuel := minFuel) hschema
          hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal hobject
          hsupportValid hleftMem hrightMem hlookup hleaf hargumentsDiff
      ⟩
  | objectArgumentsCompositeLeft hobject hleftMem hrightMem hlookup
      hcomposite _hobservable hargumentsDiff =>
      rename_i parentType left right responseName fieldName leftArguments
        rightArguments leftDirectives rightDirectives leftChildSelectionSet
        rightChildSelectionSet fieldDefinition childPath
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      have hrightNotLeft :
          ∀ arguments,
            Argument.argumentsEquivalent arguments rightArguments ->
              ¬ fieldProbeTarget parentType fieldName leftArguments
                parentType fieldName arguments := by
        intro arguments hrightArgs hleftTarget
        rcases hleftTarget with ⟨_hparent, _hfield, hleftArgs⟩
        exact hargumentsDiff
          (argumentsEquivalent_trans
            (FieldMerge.argumentsEquivalent_symm hleftArgs) hrightArgs)
      exact ⟨
        parentType,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_field_head_diff_composite_pairedPath_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (responseName := responseName)
          (leftFieldName := fieldName) (rightFieldName := fieldName)
          (leftArguments := leftArguments) (rightArguments := rightArguments)
          (leftDirectives := leftDirectives) (rightDirectives := rightDirectives)
          (leftChildSelectionSet := leftChildSelectionSet)
          (rightChildSelectionSet := rightChildSelectionSet)
          (leftFieldDefinition := fieldDefinition)
          (rightFieldDefinition := fieldDefinition) (minFuel := minFuel) hschema
          hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal hobject
          hsupportValid hleftMem hrightMem hlookup hlookup hcomposite hcomposite
          hrightNotLeft
      ⟩
  | objectChild hobject hreturnType hleftMem hrightMem harguments
      hchildTrace ih =>
      rename_i parentType returnType left right responseName fieldName
        leftArguments rightArguments leftDirectives rightDirectives
        leftChildSelectionSet rightChildSelectionSet childPath
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
        ⟨fieldDefinition, hlookup, _hleftArguments, hleftFieldValid⟩
      have hnamedType :
          fieldDefinition.outputType.namedType = returnType :=
        fieldDefinition_namedType_eq_of_fieldReturnType? hlookup
          hreturnType
      have hrightLookupSame :
          ∃ rightFieldDefinition,
            schema.lookupField parentType fieldName = some rightFieldDefinition
              ∧ Validation.fieldSelectionSetValid schema
                rightVariableDefinitions rightFieldDefinition
                rightChildSelectionSet := by
        rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
          ⟨rightFieldDefinition, hrightLookup, _hrightArguments,
            hrightFieldValid⟩
        exact ⟨rightFieldDefinition, hrightLookup, hrightFieldValid⟩
      rcases hrightLookupSame with
        ⟨rightFieldDefinition, hrightLookup, hrightFieldValid⟩
      have hrightFieldDefinitionEq :
          rightFieldDefinition = fieldDefinition := by
        rw [hlookup] at hrightLookup
        exact Option.some.inj hrightLookup.symm
      subst rightFieldDefinition
      have hnonempty :=
        normalSelectionSetDiffObservableTrace_left_or_right_nonempty
          hchildTrace
      have hcomposite :
          schema.isCompositeType fieldDefinition.outputType.namedType := by
        rcases hnonempty with hleftNonempty | hrightNonempty
        · exact (fieldSelectionSetValid_child_of_nonempty hleftFieldValid hleftNonempty).1
        · exact (fieldSelectionSetValid_child_of_nonempty hrightFieldValid
                  hrightNonempty).1
      rcases fieldSelectionSetValid_child_of_composite hleftFieldValid
          hcomposite with
        ⟨_hleftChildNonempty, hleftChildValidRaw⟩
      rcases fieldSelectionSetValid_child_of_composite hrightFieldValid
          hcomposite with
        ⟨_hrightChildNonempty, hrightChildValidRaw⟩
      have hleftChildValid :
          Validation.selectionSetValid schema leftVariableDefinitions
            returnType leftChildSelectionSet := by
        simpa [hnamedType] using hleftChildValidRaw
      have hrightChildValid :
          Validation.selectionSetValid schema rightVariableDefinitions
            returnType rightChildSelectionSet := by
        simpa [hnamedType] using hrightChildValidRaw
      have hleftDirectivesNil : leftDirectives = [] :=
        selectionSetDirectiveFree_field_directives_nil_of_mem hleftFree
          hleftMem
      have hrightDirectivesNil : rightDirectives = [] :=
        selectionSetDirectiveFree_field_directives_nil_of_mem hrightFree
          hrightMem
      subst leftDirectives
      subst rightDirectives
      have hleftChildFree :
          selectionSetDirectiveFree leftChildSelectionSet :=
        selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
      have hrightChildFree :
          selectionSetDirectiveFree rightChildSelectionSet :=
        selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
      have hleftChildNormal :
          selectionSetNormal schema returnType leftChildSelectionSet := by
        rcases
            selectionSetNormal_field_child_of_mem_with_returnType hleftNormal
              hleftMem with
          ⟨candidateReturnType, hcandidateReturnType, hchildNormal⟩
        have hcandidateEq : candidateReturnType = returnType := by
          rw [hreturnType] at hcandidateReturnType
          exact Option.some.inj hcandidateReturnType.symm
        subst candidateReturnType
        exact hchildNormal
      have hrightChildNormal :
          selectionSetNormal schema returnType rightChildSelectionSet := by
        rcases
            selectionSetNormal_field_child_of_mem_with_returnType hrightNormal
              hrightMem with
          ⟨candidateReturnType, hcandidateReturnType, hchildNormal⟩
        have hcandidateEq : candidateReturnType = returnType := by
          rw [hreturnType] at hcandidateReturnType
          exact Option.some.inj hcandidateReturnType.symm
        subst candidateReturnType
        exact hchildNormal
      rcases List.mem_iff_append.mp hleftMem with
        ⟨leftPref, leftSuffix, hleftEq⟩
      rcases List.mem_iff_append.mp hrightMem with
        ⟨rightPref, rightSuffix, hrightEq⟩
      subst left
      subst right
      have hchildSupportValid :
          ∀ supportSelectionSet,
            supportSelectionSet ∈
              focusedObjectChildSupportSelectionSets fieldName leftArguments
                rightArguments leftPref rightPref leftSuffix rightSuffix
                supportSelectionSets ->
              ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions
                  returnType supportSelectionSet
                ∧ selectionSetDirectiveFree supportSelectionSet
                ∧ selectionSetNormal schema returnType supportSelectionSet := by
        intro supportSelectionSet hsupport
        exact
          focusedObjectChildSupportSelectionSets_child_exists_valid_free_normal
            (schema := schema)
            (leftVariableDefinitions := leftVariableDefinitions)
            (rightVariableDefinitions := rightVariableDefinitions)
            (parentType := parentType) (returnType := returnType)
            (responseName := responseName) (fieldName := fieldName)
            (leftArguments := leftArguments) (rightArguments := rightArguments)
            (leftChildSelectionSet := leftChildSelectionSet)
            (rightChildSelectionSet := rightChildSelectionSet)
            (leftPref := leftPref) (rightPref := rightPref)
            (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
            (supportSelectionSets := supportSelectionSets)
            (childSelectionSet := supportSelectionSet)
            (fieldDefinition := fieldDefinition)
            hleftValid hrightValid hleftFree hrightFree hleftNormal
            hrightNormal hsupportValid hlookup hnamedType hcomposite hsupport
      rcases
          ih hleftChildValid hrightChildValid hleftChildFree
            hrightChildFree hleftChildNormal hrightChildNormal
            hchildSupportValid
            (supportSelectionSets :=
              focusedObjectChildSupportSelectionSets fieldName leftArguments
                rightArguments leftPref rightPref leftSuffix rightSuffix
                supportSelectionSets)
            (minFuel :=
              max
                (selectionSetDeepProbeFuel schema parentType
                  (List.flatten
                    ((leftPref ++
                        Selection.field responseName fieldName
                          leftArguments [] leftChildSelectionSet ::
                          leftSuffix)
                      :: (rightPref ++
                        Selection.field responseName fieldName
                          rightArguments [] rightChildSelectionSet ::
                          rightSuffix)
                      :: supportSelectionSets))
                  - leafProbeFuel fieldDefinition.outputType)
                (minFuel - leafProbeFuel fieldDefinition.outputType - 1)) with
        ⟨childRuntimeType, hchildWitness⟩
      exact ⟨
        parentType,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_child_contextualRuntimeDiff_split_focusedFiniteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (returnType := returnType)
          (responseName := responseName) (fieldName := fieldName)
          (runtimeType := childRuntimeType) (leftArguments := leftArguments)
          (rightArguments := rightArguments)
          (leftChildSelectionSet := leftChildSelectionSet)
          (rightChildSelectionSet := rightChildSelectionSet) (leftPref := leftPref)
          (rightPref := rightPref) (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
          (supportSelectionSets := supportSelectionSets)
          (fieldDefinition := fieldDefinition) (minFuel := minFuel) hschema hleftValid
          hrightValid hlookup hnamedType hleftFree hrightFree hleftNormal hrightNormal
          hobject hsupportValid hchildWitness
      ⟩
  | abstractLeftTypeCondition hnonObject hleftMem hrightNoTypeCondition
      _hobservable =>
      rename_i parentType left right typeCondition directives childSelectionSet
        childPath
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      exact ⟨
        typeCondition,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_abstract_left_typeCondition_diff_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (typeCondition := typeCondition)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (minFuel := minFuel) hschema hleftValid hrightValid hleftFree hrightFree
          hleftNormal hrightNormal hnonObject hsupportValid hleftMem hrightNoTypeCondition
      ⟩
  | abstractRightTypeCondition hnonObject hrightMem hleftNoTypeCondition
      _hobservable =>
      rename_i parentType left right typeCondition directives childSelectionSet
        childPath
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      exact ⟨
        typeCondition,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_abstract_right_typeCondition_diff_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (typeCondition := typeCondition)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (minFuel := minFuel) hschema hleftValid hrightValid hleftFree hrightFree
          hleftNormal hrightNormal hnonObject hsupportValid hrightMem hleftNoTypeCondition
      ⟩
  | abstractChild hnonObject hleftMem hrightMem hchildTrace ih =>
      rename_i parentType typeCondition left right leftDirectives
        rightDirectives leftChildSelectionSet rightChildSelectionSet childPath
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      have hleftDirectivesNil : leftDirectives = [] :=
        selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
          hleftFree hleftMem
      have hrightDirectivesNil : rightDirectives = [] :=
        selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
          hrightFree hrightMem
      subst leftDirectives
      subst rightDirectives
      have hleftChildValid :
          Validation.selectionSetValid schema leftVariableDefinitions
            typeCondition leftChildSelectionSet :=
        selectionSetValid_inlineFragment_some_child_of_mem hleftValid
          hleftMem
      have hrightChildValid :
          Validation.selectionSetValid schema rightVariableDefinitions
            typeCondition rightChildSelectionSet :=
        selectionSetValid_inlineFragment_some_child_of_mem hrightValid
          hrightMem
      have hleftChildFree :
          selectionSetDirectiveFree leftChildSelectionSet :=
        selectionSetDirectiveFree_inlineFragment_child_of_mem hleftFree
          hleftMem
      have hrightChildFree :
          selectionSetDirectiveFree rightChildSelectionSet :=
        selectionSetDirectiveFree_inlineFragment_child_of_mem hrightFree
          hrightMem
      have hleftChildNormal :
          selectionSetNormal schema typeCondition leftChildSelectionSet :=
        (selectionSetNormal_inlineFragment_child_of_mem hleftNormal
          hleftMem).2
      have hrightChildNormal :
          selectionSetNormal schema typeCondition rightChildSelectionSet :=
        (selectionSetNormal_inlineFragment_child_of_mem hrightNormal
          hrightMem).2
      rcases List.mem_iff_append.mp hleftMem with
        ⟨leftPref, leftSuffix, hleftEq⟩
      rcases List.mem_iff_append.mp hrightMem with
        ⟨rightPref, rightSuffix, hrightEq⟩
      subst left
      subst right
      have hchildSupportValid :
          ∀ supportSelectionSet,
            supportSelectionSet ∈
              abstractChildSupportSelectionSets typeCondition leftPref
                rightPref leftSuffix rightSuffix supportSelectionSets ->
              ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition supportSelectionSet
                ∧ selectionSetDirectiveFree supportSelectionSet
                ∧ selectionSetNormal schema typeCondition
                  supportSelectionSet := by
        intro supportSelectionSet hsupport
        simp [abstractChildSupportSelectionSets] at hsupport
        rcases hsupport with hsplit | hsupportTarget
        · exact
            splitTargetInlineFragmentSelectionSets_child_exists_valid_free_normal
              (schema := schema)
              (leftVariableDefinitions := leftVariableDefinitions)
              (rightVariableDefinitions := rightVariableDefinitions)
              (parentType := parentType)
              (typeCondition := typeCondition)
              (leftChildSelectionSet := leftChildSelectionSet)
              (rightChildSelectionSet := rightChildSelectionSet)
              (leftPref := leftPref) (rightPref := rightPref)
              (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
              (childSelectionSet := supportSelectionSet)
              hleftValid hrightValid hleftFree hrightFree hleftNormal
              hrightNormal hsplit
        · exact
            supportTargetInlineFragmentSelectionSets_child_exists_valid_free_normal
              (schema := schema) (parentType := parentType)
              (typeCondition := typeCondition)
              (supportSelectionSets := supportSelectionSets)
              (childSelectionSet := supportSelectionSet)
              hsupportValid hsupportTarget
      rcases
          ih hleftChildValid hrightChildValid hleftChildFree
            hrightChildFree hleftChildNormal hrightChildNormal
            hchildSupportValid
            (supportSelectionSets :=
              abstractChildSupportSelectionSets typeCondition leftPref
                rightPref leftSuffix rightSuffix supportSelectionSets)
            (minFuel := minFuel) with
        ⟨childRuntimeType, hchildWitness⟩
      exact ⟨
        childRuntimeType,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_abstract_child_contextualRuntimeDiff_split_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (typeCondition := typeCondition)
          (runtimeType := childRuntimeType)
          (leftChildSelectionSet := leftChildSelectionSet)
          (rightChildSelectionSet := rightChildSelectionSet) (leftPref := leftPref)
          (rightPref := rightPref) (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
          (supportSelectionSets := supportSelectionSets) (minFuel := minFuel) hleftValid
          hrightValid hleftFree hrightFree hleftNormal hrightNormal hnonObject
          hsupportValid hchildWitness
      ⟩

theorem
    not_selectionSetsDataEquivalent_of_valid_normal_object_child_observable_trace_split_focused
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType returnType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection}
    {fieldDefinition : FieldDefinition} {childPath : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = true
      -> Argument.argumentsEquivalent leftArguments rightArguments
      -> Validation.selectionSetValid schema leftVariableDefinitions returnType
          leftChildSelectionSet
      -> Validation.selectionSetValid schema rightVariableDefinitions returnType
          rightChildSelectionSet
      -> selectionSetDirectiveFree leftChildSelectionSet
      -> selectionSetDirectiveFree rightChildSelectionSet
      -> selectionSetNormal schema returnType leftChildSelectionSet
      -> selectionSetNormal schema returnType rightChildSelectionSet
      -> NormalSelectionSetDiffObservableTrace schema returnType
          leftChildSelectionSet rightChildSelectionSet childPath
      -> ¬ selectionSetsDataEquivalent schema parentType
            (leftPref
              ++ Selection.field responseName fieldName leftArguments []
                    leftChildSelectionSet
                  :: leftSuffix)
            (rightPref
              ++ Selection.field responseName fieldName rightArguments []
                    rightChildSelectionSet
                  :: rightSuffix) := by
  intro hschema hleftValid hrightValid hlookup hreturnType hleftFree
    hrightFree hleftNormal hrightNormal hparentObject _harguments
    hleftChildValid hrightChildValid hleftChildFree hrightChildFree
    hleftChildNormal hrightChildNormal hchildTrace
  let leftSelectionSet :=
    leftPref ++ Selection.field responseName fieldName leftArguments []
      leftChildSelectionSet :: leftSuffix
  let rightSelectionSet :=
    rightPref ++ Selection.field responseName fieldName rightArguments []
      rightChildSelectionSet :: rightSuffix
  have hleftFieldMem :
      Selection.field responseName fieldName leftArguments []
        leftChildSelectionSet ∈ leftSelectionSet := by
    exact List.mem_append_right leftPref (by simp)
  have hrightFieldMem :
      Selection.field responseName fieldName rightArguments []
        rightChildSelectionSet ∈ rightSelectionSet := by
    exact List.mem_append_right rightPref (by simp)
  have hcomposite :
      schema.isCompositeType fieldDefinition.outputType.namedType := by
    have hnonempty :=
      normalSelectionSetDiffObservableTrace_left_or_right_nonempty
        hchildTrace
    rcases hnonempty with hleftNonempty | hrightNonempty
    · rcases
        selectionSetValid_field_lookup_of_mem
          (by simpa [leftSelectionSet] using hleftValid)
          hleftFieldMem with
        ⟨candidateFieldDefinition, hcandidateLookup, _harguments,
          hfieldValid⟩
      have hcandidateEq :
          candidateFieldDefinition = fieldDefinition := by
        rw [hlookup] at hcandidateLookup
        exact Option.some.inj hcandidateLookup.symm
      subst candidateFieldDefinition
      exact (fieldSelectionSetValid_child_of_nonempty hfieldValid hleftNonempty).1
    · rcases
        selectionSetValid_field_lookup_of_mem
          (by simpa [rightSelectionSet] using hrightValid)
          hrightFieldMem with
        ⟨candidateFieldDefinition, hcandidateLookup, _harguments,
          hfieldValid⟩
      have hcandidateEq :
          candidateFieldDefinition = fieldDefinition := by
        rw [hlookup] at hcandidateLookup
        exact Option.some.inj hcandidateLookup.symm
      subst candidateFieldDefinition
      exact (fieldSelectionSetValid_child_of_nonempty hfieldValid hrightNonempty).1
  have hsupportValid :
      ∀ supportSelectionSet,
        supportSelectionSet ∈
          focusedSplitTargetChildSelectionSets fieldName leftArguments
            rightArguments leftPref rightPref leftSuffix rightSuffix ->
          ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions returnType
              supportSelectionSet
            ∧ selectionSetDirectiveFree supportSelectionSet
            ∧ selectionSetNormal schema returnType supportSelectionSet := by
    intro supportSelectionSet hsupport
    exact
      focusedSplitTargetChildSelectionSets_child_exists_valid_free_normal
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (returnType := returnType)
        (responseName := responseName) (fieldName := fieldName)
        (leftArguments := leftArguments) (rightArguments := rightArguments)
        (leftChildSelectionSet := leftChildSelectionSet)
        (rightChildSelectionSet := rightChildSelectionSet)
        (leftPref := leftPref) (rightPref := rightPref)
        (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
        (childSelectionSet := supportSelectionSet)
        (fieldDefinition := fieldDefinition)
        (by simpa [leftSelectionSet] using hleftValid)
        (by simpa [rightSelectionSet] using hrightValid)
        (by simpa [leftSelectionSet] using hleftFree)
        (by simpa [rightSelectionSet] using hrightFree)
        (by simpa [leftSelectionSet] using hleftNormal)
        (by simpa [rightSelectionSet] using hrightNormal)
        hlookup hreturnType hcomposite hsupport
  rcases
      selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_observable_trace
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (parentType := returnType) (left := leftChildSelectionSet)
        (right := rightChildSelectionSet)
        (supportSelectionSets :=
          focusedSplitTargetChildSelectionSets fieldName leftArguments
            rightArguments leftPref rightPref leftSuffix rightSuffix)
        (minFuel :=
          selectionSetDeepProbeFuel schema parentType
            (leftSelectionSet ++ rightSelectionSet)
          - leafProbeFuel fieldDefinition.outputType)
        hschema hleftChildValid hrightChildValid hleftChildFree
        hrightChildFree hleftChildNormal hrightChildNormal hsupportValid
        hchildTrace with
    ⟨runtimeType, hwitness⟩
  exact
    not_selectionSetsDataEquivalent_of_valid_normal_object_child_contextualRuntimeDiff_split_targetSupport_focused
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      (parentType := parentType) (returnType := returnType)
      (responseName := responseName) (fieldName := fieldName)
      (runtimeType := runtimeType) (leftArguments := leftArguments)
      (rightArguments := rightArguments)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      (leftPref := leftPref) (rightPref := rightPref)
      (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
      (fieldDefinition := fieldDefinition)
      hschema
      (by simpa [leftSelectionSet] using hleftValid)
      (by simpa [rightSelectionSet] using hrightValid)
      hlookup hreturnType
      (by simpa [leftSelectionSet] using hleftFree)
      (by simpa [rightSelectionSet] using hrightFree)
      (by simpa [leftSelectionSet] using hleftNormal)
      (by simpa [rightSelectionSet] using hrightNormal)
      hparentObject
      (by simpa [leftSelectionSet, rightSelectionSet] using hwitness)

theorem
    not_selectionSetsDataEquivalent_of_valid_normal_object_fieldName_diff_left_leaf_right_composite
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> leftFieldName ≠ rightFieldName
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightMem hleftLookup hrightLookup
    hleftLeaf hrightComposite hfieldDiff
  have hwitness :
      selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
        parentType parentType left right
        (fun selectionSet => selectionSet ∈ ([] : List (List Selection)))
        0 :=
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_fieldName_diff_left_leaf_right_composite_finiteSupport
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      (parentType := parentType) (left := left) (right := right)
      (supportSelectionSets := []) (responseName := responseName)
      (leftFieldName := leftFieldName) (rightFieldName := rightFieldName)
      (leftArguments := leftArguments) (rightArguments := rightArguments)
      (leftDirectives := leftDirectives)
      (rightDirectives := rightDirectives)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      (leftFieldDefinition := leftFieldDefinition)
      (rightFieldDefinition := rightFieldDefinition) (minFuel := 0)
      hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
      hrightNormal hobject (by
        intro supportSelectionSet hsupport
        simp at hsupport)
      hleftMem hrightMem hleftLookup hrightLookup hleftLeaf
      hrightComposite hfieldDiff
  exact
    not_selectionSetsDataEquivalent_of_contextualRuntimeDataDiffWitnessWithFuelGe
      hobject hwitness

theorem
    not_selectionSetsDataEquivalent_of_valid_normal_object_fieldName_diff_left_composite_right_leaf
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> leftFieldName ≠ rightFieldName
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightMem hleftLookup hrightLookup
    hleftComposite hrightLeaf hfieldDiff
  have hswapped :
      selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
        parentType parentType right left
        (fun selectionSet => selectionSet ∈ ([] : List (List Selection)))
        0 :=
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_fieldName_diff_left_leaf_right_composite_finiteSupport
      (schema := schema)
      (leftVariableDefinitions := rightVariableDefinitions)
      (rightVariableDefinitions := leftVariableDefinitions)
      (parentType := parentType) (left := right) (right := left)
      (supportSelectionSets := []) (responseName := responseName)
      (leftFieldName := rightFieldName) (rightFieldName := leftFieldName)
      (leftArguments := rightArguments) (rightArguments := leftArguments)
      (leftDirectives := rightDirectives)
      (rightDirectives := leftDirectives)
      (leftChildSelectionSet := rightChildSelectionSet)
      (rightChildSelectionSet := leftChildSelectionSet)
      (leftFieldDefinition := rightFieldDefinition)
      (rightFieldDefinition := leftFieldDefinition) (minFuel := 0)
      hschema hrightValid hleftValid hrightFree hleftFree hrightNormal
      hleftNormal hobject (by
        intro supportSelectionSet hsupport
        simp at hsupport)
      hrightMem hleftMem hrightLookup hleftLookup hrightLeaf
      hleftComposite (by
        intro hsame
        exact hfieldDiff hsame.symm)
  have hwitness :
      selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
        parentType parentType left right
        (fun selectionSet => selectionSet ∈ ([] : List (List Selection)))
        0 :=
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_symm hswapped
  exact
    not_selectionSetsDataEquivalent_of_contextualRuntimeDataDiffWitnessWithFuelGe
      hobject hwitness

theorem
    not_selectionSetsDataEquivalent_of_valid_normal_object_diff_observable_trace_pairedPath
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection} {responsePath : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> NormalSelectionSetDiffObservableTrace schema parentType left right responsePath
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject htrace
  apply
    not_selectionSetsDataEquivalent_of_valid_normal_object_diff_observable_trace_of_split_child_separators
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      (parentType := parentType) (left := left) (right := right)
      (responsePath := responsePath)
  · intro responseName leftFieldName rightFieldName leftArguments
      rightArguments leftDirectives rightDirectives leftChildSelectionSet
      rightChildSelectionSet leftFieldDefinition rightFieldDefinition
      _childPath hleftMem hrightMem hleftLookup hrightLookup hleftComposite
      _hobservable hfieldDiff
    by_cases hrightComposite :
        (TypeRef.named
            rightFieldDefinition.outputType.namedType).isCompositeBool
          schema = true
    · exact
        not_selectionSetsDataEquivalent_of_valid_normal_object_fieldName_diff_composite_pairedPath
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hobject hleftMem hrightMem hleftLookup hrightLookup
          hleftComposite hrightComposite hfieldDiff
    · have hrightLeaf :
          (TypeRef.named
              rightFieldDefinition.outputType.namedType).isCompositeBool
            schema = false := by
        cases h :
            (TypeRef.named
                rightFieldDefinition.outputType.namedType).isCompositeBool
              schema <;>
          simp [h] at hrightComposite ⊢
      exact
        not_selectionSetsDataEquivalent_of_valid_normal_object_fieldName_diff_left_composite_right_leaf
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hobject hleftMem hrightMem hleftLookup hrightLookup
          hleftComposite hrightLeaf hfieldDiff
  · intro responseName leftFieldName rightFieldName leftArguments
      rightArguments leftDirectives rightDirectives leftChildSelectionSet
      rightChildSelectionSet leftFieldDefinition rightFieldDefinition
      _childPath hleftMem hrightMem hleftLookup hrightLookup hrightComposite
      _hobservable hfieldDiff
    by_cases hleftComposite :
        (TypeRef.named
            leftFieldDefinition.outputType.namedType).isCompositeBool
          schema = true
    · exact
        not_selectionSetsDataEquivalent_of_valid_normal_object_fieldName_diff_composite_pairedPath
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hobject hleftMem hrightMem hleftLookup hrightLookup
          hleftComposite hrightComposite hfieldDiff
    · have hleftLeaf :
          (TypeRef.named
              leftFieldDefinition.outputType.namedType).isCompositeBool
            schema = false := by
        cases h :
            (TypeRef.named
                leftFieldDefinition.outputType.namedType).isCompositeBool
              schema <;>
          simp [h] at hleftComposite ⊢
      exact
        not_selectionSetsDataEquivalent_of_valid_normal_object_fieldName_diff_left_leaf_right_composite
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hobject hleftMem hrightMem hleftLookup hrightLookup
          hleftLeaf hrightComposite hfieldDiff
  · intro responseName fieldName leftArguments rightArguments
      leftDirectives rightDirectives leftChildSelectionSet
      rightChildSelectionSet fieldDefinition _childPath hleftMem hrightMem
      hlookup hcomposite _hobservable hargumentsDiff
    exact
      not_selectionSetsDataEquivalent_of_valid_normal_object_arguments_diff_composite_pairedPath
        hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hobject hleftMem hrightMem hlookup hcomposite
        hargumentsDiff
  · intro returnType responseName fieldName leftArguments rightArguments
      leftChildSelectionSet rightChildSelectionSet leftPref rightPref
      leftSuffix rightSuffix fieldDefinition childPath hlookup hreturnType
      hleftEq hrightEq harguments hleftChildValid hrightChildValid
      hleftChildFree hrightChildFree hleftChildNormal hrightChildNormal
      hchildTrace
    subst left
    subst right
    exact
      not_selectionSetsDataEquivalent_of_valid_normal_object_child_observable_trace_split_focused
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (returnType := returnType)
        (responseName := responseName) (fieldName := fieldName)
        (leftArguments := leftArguments)
        (rightArguments := rightArguments)
        (leftChildSelectionSet := leftChildSelectionSet)
        (rightChildSelectionSet := rightChildSelectionSet)
        (leftPref := leftPref) (rightPref := rightPref)
        (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
        (fieldDefinition := fieldDefinition) (childPath := childPath)
        hschema hleftValid hrightValid hlookup hreturnType hleftFree
        hrightFree hleftNormal hrightNormal hobject harguments
        hleftChildValid hrightChildValid hleftChildFree hrightChildFree
        hleftChildNormal hrightChildNormal hchildTrace
  · exact hschema
  · exact hleftValid
  · exact hrightValid
  · exact hleftFree
  · exact hrightFree
  · exact hleftNormal
  · exact hrightNormal
  · exact hobject
  · exact htrace

end GroundTypeNormalization

end NormalForm

end GraphQL
