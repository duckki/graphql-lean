import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.CoercionDiff
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

private theorem supportSelectionSetsArgumentsCoercible_of_inPossibleTypes_of_object
    {schema : Schema} {variableValues : Execution.VariableValues}
    {parentType : Name} {supportSelectionSets : List (List Selection)}
    (hobject : objectTypeNameBool schema parentType = true)
    (hsupport
      : ∀ supportSelectionSet,
          supportSelectionSet ∈ supportSelectionSets
          -> ∃ variableDefinitions,
              Validation.selectionSetValid schema variableDefinitions parentType
                supportSelectionSet
              ∧ selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
                  parentType supportSelectionSet
              ∧ selectionSetDirectiveFree supportSelectionSet
              ∧ selectionSetNormal schema parentType supportSelectionSet)
    : ∀ supportSelectionSet,
        supportSelectionSet ∈ supportSelectionSets
        -> ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions parentType
              supportSelectionSet
            ∧ selectionSetArgumentsCoercible schema variableValues parentType
                supportSelectionSet
            ∧ selectionSetDirectiveFree supportSelectionSet
            ∧ selectionSetNormal schema parentType supportSelectionSet := by
  intro supportSelectionSet hmem
  rcases hsupport supportSelectionSet hmem with
    ⟨variableDefinitions, hvalid, hcoercion, hfree, hnormal⟩
  exact ⟨variableDefinitions, hvalid,
    selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
      hobject hcoercion,
    hfree, hnormal⟩

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_coercion_diff
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {supportSelectionSets : List (List Selection)} {minFuel : Nat}
    {variableValues : Execution.VariableValues}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
          parentType left
      -> selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
          parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> (∀ supportSelectionSet,
            supportSelectionSet ∈ supportSelectionSets
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  supportSelectionSet
                ∧ selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
                    parentType supportSelectionSet
                ∧ selectionSetDirectiveFree supportSelectionSet
                ∧ selectionSetNormal schema parentType supportSelectionSet)
      -> NormalSelectionSetResolverDiff schema variableValues parentType left right
      -> ∃ runtimeType,
          selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
            parentType runtimeType left right
            (variableValues := variableValues)
            (fun selectionSet => selectionSet ∈ supportSelectionSets)
            minFuel := by
  intro hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hsupportValid hdiff
  revert hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree hleftNormal
    hrightNormal hsupportValid
  revert leftVariableDefinitions rightVariableDefinitions supportSelectionSets
    minFuel
  induction hdiff with
  | objectLeftResponseName hobject hleftMem hrightNoResponseName =>
      rename_i parentType left right responseName fieldName arguments
        directives childSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftCoercion hrightCoercion
        hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      have hleftObjectCoercion :=
        selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hleftCoercion
      have hrightObjectCoercion :=
        selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hrightCoercion
      have hsupportObjectValid :=
        supportSelectionSetsArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hsupportValid
      exact ⟨
        parentType,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_left_responseName_diff_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (minFuel := minFuel) hschema
          hleftValid hrightValid hleftObjectCoercion hrightObjectCoercion
          hleftFree hrightFree hleftNormal hrightNormal hobject
          hsupportObjectValid hleftMem hrightNoResponseName
      ⟩
  | objectRightResponseName hobject hrightMem hleftNoResponseName =>
      rename_i parentType left right responseName fieldName arguments
        directives childSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftCoercion hrightCoercion
        hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      have hleftObjectCoercion :=
        selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hleftCoercion
      have hrightObjectCoercion :=
        selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hrightCoercion
      have hsupportObjectValid :=
        supportSelectionSetsArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hsupportValid
      exact ⟨
        parentType,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_right_responseName_diff_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (minFuel := minFuel) hschema
          hleftValid hrightValid hleftObjectCoercion hrightObjectCoercion
          hleftFree hrightFree hleftNormal hrightNormal hobject
          hsupportObjectValid hrightMem hleftNoResponseName
      ⟩
  | objectFieldName hobject hleftMem hrightMem hfieldDiff =>
      rename_i parentType left right responseName leftFieldName rightFieldName
        leftArguments rightArguments leftDirectives rightDirectives
        leftChildSelectionSet rightChildSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftCoercion hrightCoercion
        hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      have hleftObjectCoercion :=
        selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hleftCoercion
      have hrightObjectCoercion :=
        selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hrightCoercion
      have hsupportObjectValid :=
        supportSelectionSetsArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hsupportValid
      rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
        ⟨leftFieldDefinition, hleftLookup, _hleftArguments, _hleftFieldValid⟩
      rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
        ⟨rightFieldDefinition, hrightLookup, _hrightArguments, _hrightFieldValid⟩
      by_cases hleftLeaf :
          (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
            schema = false
      · by_cases hrightLeaf :
            (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
              schema = false
        · exact ⟨
            parentType,
            selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_fieldName_diff_leaf_finiteSupport
              (variableValues := variableValues) hschema hleftValid hrightValid
              hleftObjectCoercion hrightObjectCoercion hleftFree
              hrightFree hleftNormal hrightNormal hobject hsupportObjectValid hleftMem hrightMem
              hleftLookup hrightLookup hleftLeaf hrightLeaf hfieldDiff
          ⟩
        · have hrightComposite :
              (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                schema = true := by
            cases h : (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema <;>
              simp [h] at hrightLeaf ⊢
          exact ⟨
            parentType,
            selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_fieldName_diff_left_leaf_right_composite_finiteSupport
              (variableValues := variableValues) hschema hleftValid hrightValid
              hleftObjectCoercion hrightObjectCoercion hleftFree
              hrightFree hleftNormal hrightNormal hobject hsupportObjectValid hleftMem hrightMem
              hleftLookup hrightLookup hleftLeaf hrightComposite hfieldDiff
          ⟩
      · have hleftComposite :
            (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool
              schema = true := by
          cases h : (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema <;>
            simp [h] at hleftLeaf ⊢
        by_cases hrightLeaf :
            (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
              schema = false
        · have hwitness :=
            selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_fieldName_diff_left_leaf_right_composite_finiteSupport
              (schema := schema)
              (leftVariableDefinitions := rightVariableDefinitions)
              (rightVariableDefinitions := leftVariableDefinitions)
              (parentType := parentType) (left := right) (right := left)
              (supportSelectionSets := supportSelectionSets)
              (responseName := responseName)
              (leftFieldName := rightFieldName) (rightFieldName := leftFieldName)
              (leftArguments := rightArguments) (rightArguments := leftArguments)
              (leftDirectives := rightDirectives) (rightDirectives := leftDirectives)
              (leftChildSelectionSet := rightChildSelectionSet)
              (rightChildSelectionSet := leftChildSelectionSet)
              (leftFieldDefinition := rightFieldDefinition)
              (rightFieldDefinition := leftFieldDefinition)
              (minFuel := minFuel) (variableValues := variableValues)
              hschema hrightValid hleftValid hrightObjectCoercion
              hleftObjectCoercion
              hrightFree hleftFree hrightNormal
              hleftNormal hobject hsupportObjectValid hrightMem hleftMem hrightLookup
              hleftLookup hrightLeaf hleftComposite (by
                intro hsame
                exact hfieldDiff hsame.symm)
          exact ⟨parentType,
            selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_symm hwitness⟩
        · have hrightComposite :
              (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                schema = true := by
            cases h : (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema <;>
              simp [h] at hrightLeaf ⊢
          have hrightNotLeft :
              ∀ arguments,
                Execution.CoercedArgument.argumentsEquivalent
                    (Execution.coercedArgumentsForField schema variableValues
                      parentType rightFieldName arguments)
                    (Execution.coercedArgumentsForField schema variableValues
                      parentType rightFieldName rightArguments) ->
                  ¬ fieldProbeTarget parentType leftFieldName
                    (Execution.coercedArgumentsForField schema variableValues
                      parentType leftFieldName leftArguments)
                    parentType rightFieldName
                    (Execution.coercedArgumentsForField schema variableValues
                      parentType rightFieldName arguments) := by
            intro arguments _hrightArgs hleftTarget
            exact hfieldDiff hleftTarget.2.1.symm
          exact ⟨
            parentType,
            selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_field_head_diff_composite_pairedPath_finiteSupport
              (variableValues := variableValues) hschema hleftValid hrightValid
              hleftObjectCoercion hrightObjectCoercion hleftFree
              hrightFree hleftNormal hrightNormal hobject hsupportObjectValid hleftMem hrightMem
              hleftLookup hrightLookup hleftComposite hrightComposite hrightNotLeft
          ⟩
  | objectArguments fieldDefinition hobject hleftMem hrightMem hlookup
      hargumentsDiff =>
      rename_i parentType left right responseName fieldName leftArguments
        rightArguments leftDirectives rightDirectives leftChildSelectionSet
        rightChildSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftCoercion hrightCoercion
        hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      have hleftObjectCoercion :=
        selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hleftCoercion
      have hrightObjectCoercion :=
        selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hrightCoercion
      have hsupportObjectValid :=
        supportSelectionSetsArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hsupportValid
      let leftTargetArguments :=
        Execution.coercedArgumentsForField schema variableValues parentType
          fieldName leftArguments
      let rightTargetArguments :=
        Execution.coercedArgumentsForField schema variableValues parentType
          fieldName rightArguments
      have hleftSuccess :=
        (selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
          hleftObjectCoercion hleftFree)
          responseName fieldName leftArguments leftDirectives
          leftChildSelectionSet hleftMem fieldDefinition hlookup
      have hrightSuccess :=
        (selectionSetArgumentCoercionSucceeds_of_argumentsCoercible
          hrightObjectCoercion hrightFree)
          responseName fieldName rightArguments rightDirectives
          rightChildSelectionSet hrightMem fieldDefinition hlookup
      have htargetArgumentsDiff :
          ¬ Execution.CoercedArgument.argumentsEquivalent leftTargetArguments
            rightTargetArguments := by
        intro htargetEquivalent
        apply hargumentsDiff
        cases hleftResult
              : Execution.coerceArgumentValues schema variableValues
                  fieldDefinition.arguments leftArguments with
        | error => simp [hleftResult] at hleftSuccess
        | success leftCoercedArguments =>
            cases hrightResult
                  : Execution.coerceArgumentValues schema variableValues
                      fieldDefinition.arguments rightArguments with
            | error => simp [hrightResult] at hrightSuccess
            | success rightCoercedArguments =>
                simpa [Execution.ArgumentCoercionResult.equivalent,
                  hleftResult, hrightResult, leftTargetArguments,
                  rightTargetArguments, Execution.coercedArgumentsForField,
                  hlookup] using htargetEquivalent
      by_cases hleaf :
          (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
            = false
      · exact ⟨
          parentType,
          selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_arguments_diff_leaf_finiteSupport
            (variableValues := variableValues) hschema hleftValid hrightValid
            hleftObjectCoercion hrightObjectCoercion hleftFree
            hrightFree hleftNormal hrightNormal hobject hsupportObjectValid hleftMem hrightMem
            hlookup hleaf htargetArgumentsDiff
        ⟩
      · have hcomposite :
            (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = true := by
          cases h : (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema <;>
            simp [h] at hleaf ⊢
        have hrightNotLeft :
            ∀ arguments,
              Execution.CoercedArgument.argumentsEquivalent
                  (Execution.coercedArgumentsForField schema variableValues
                    parentType fieldName arguments)
                  rightTargetArguments ->
                ¬ fieldProbeTarget parentType fieldName leftTargetArguments
                  parentType fieldName
                    (Execution.coercedArgumentsForField schema variableValues
                      parentType fieldName arguments) := by
          intro arguments hrightArgs hleftTarget
          rcases hleftTarget with ⟨_hparent, _hfield, hleftArgs⟩
          exact htargetArgumentsDiff
            (Execution.CoercedArgument.argumentsEquivalent_trans
              (Execution.CoercedArgument.argumentsEquivalent_symm hleftArgs)
              hrightArgs)
        exact ⟨
          parentType,
          selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_field_head_diff_composite_pairedPath_finiteSupport
            (variableValues := variableValues) hschema hleftValid hrightValid
            hleftObjectCoercion hrightObjectCoercion hleftFree
            hrightFree hleftNormal hrightNormal hobject hsupportObjectValid hleftMem hrightMem
            hlookup hlookup hcomposite hcomposite hrightNotLeft
        ⟩
  | objectChild fieldDefinition hobject hleftMem hrightMem hlookup harguments
      _hsuccess hchildDiff ih =>
      rename_i parentType left right responseName fieldName
        leftArguments rightArguments leftDirectives rightDirectives
        leftChildSelectionSet rightChildSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftCoercion hrightCoercion
        hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      have hleftObjectCoercion :=
        selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hleftCoercion
      have hrightObjectCoercion :=
        selectionSetArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hrightCoercion
      have hsupportObjectValid :=
        supportSelectionSetsArgumentsCoercible_of_inPossibleTypes_of_object
          hobject hsupportValid
      let returnType := fieldDefinition.outputType.namedType
      rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
        ⟨leftFieldDefinition, hleftLookup, _hleftArguments, hleftFieldValid⟩
      have hleftFieldDefinitionEq : leftFieldDefinition = fieldDefinition := by
        rw [hlookup] at hleftLookup
        exact Option.some.inj hleftLookup.symm
      subst leftFieldDefinition
      have hnamedType : fieldDefinition.outputType.namedType = returnType := rfl
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
        normalSelectionSetResolverDiff_left_or_right_nonempty hchildDiff
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
        simpa [returnType] using
          selectionSetNormal_field_child_of_mem_lookup hleftNormal hleftMem hlookup
      have hrightChildNormal :
          selectionSetNormal schema returnType rightChildSelectionSet := by
        simpa [returnType] using
          selectionSetNormal_field_child_of_mem_lookup hrightNormal hrightMem hlookup
      rcases List.mem_iff_append.mp hleftMem with
        ⟨leftPref, leftSuffix, hleftEq⟩
      rcases List.mem_iff_append.mp hrightMem with
        ⟨rightPref, rightSuffix, hrightEq⟩
      subst left
      subst right
      have hleftChildCoercion :
          selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
            returnType leftChildSelectionSet := by
        simpa [returnType] using
          selectionSetArgumentsCoercible_field_children_of_directiveFree
            hleftObjectCoercion hleftFree hleftMem hlookup
      have hrightChildCoercion :
          selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
            returnType rightChildSelectionSet := by
        simpa [returnType] using
          selectionSetArgumentsCoercible_field_children_of_directiveFree
            hrightObjectCoercion hrightFree hrightMem hlookup
      have hchildSupportValid :
          ∀ supportSelectionSet,
            supportSelectionSet ∈
              focusedObjectChildSupportSelectionSets fieldName leftArguments
                rightArguments leftPref rightPref leftSuffix rightSuffix
                supportSelectionSets ->
              ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions
                  returnType supportSelectionSet
                ∧ selectionSetArgumentsCoercibleInPossibleTypes schema
                    variableValues returnType supportSelectionSet
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
            hleftValid hrightValid hleftObjectCoercion hrightObjectCoercion
            hleftFree hrightFree hleftNormal
            hrightNormal hsupportObjectValid hlookup hnamedType hcomposite hsupport
      rcases
          ih hleftChildValid hrightChildValid hleftChildCoercion
            hrightChildCoercion
            hleftChildFree
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
          hrightValid hleftObjectCoercion hrightObjectCoercion hlookup hnamedType
          hleftFree hrightFree hleftNormal hrightNormal
          hobject hsupportObjectValid hchildWitness
      ⟩
  | abstractLeftTypeCondition hnonObject hleftMem hrightNoTypeCondition =>
      rename_i parentType left right typeCondition directives childSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftCoercion hrightCoercion
        hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      exact ⟨
        typeCondition,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_abstract_left_typeCondition_diff_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (typeCondition := typeCondition)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (minFuel := minFuel) hschema hleftValid hrightValid
          hleftCoercion hrightCoercion hleftFree hrightFree
          hleftNormal hrightNormal hnonObject hsupportValid hleftMem hrightNoTypeCondition
      ⟩
  | abstractRightTypeCondition hnonObject hrightMem hleftNoTypeCondition =>
      rename_i parentType left right typeCondition directives childSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftCoercion hrightCoercion
        hleftFree hrightFree hleftNormal
        hrightNormal hsupportValid
      exact ⟨
        typeCondition,
        selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_abstract_right_typeCondition_diff_finiteSupport
          (schema := schema) (leftVariableDefinitions := leftVariableDefinitions)
          (rightVariableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (left := left) (right := right)
          (supportSelectionSets := supportSelectionSets) (typeCondition := typeCondition)
          (directives := directives) (childSelectionSet := childSelectionSet)
          (minFuel := minFuel) hschema hleftValid hrightValid
          hleftCoercion hrightCoercion hleftFree hrightFree
          hleftNormal hrightNormal hnonObject hsupportValid hrightMem hleftNoTypeCondition
      ⟩
  | abstractChild hnonObject hleftMem hrightMem hchildDiff ih =>
      rename_i parentType typeCondition left right leftDirectives
        rightDirectives leftChildSelectionSet rightChildSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions supportSelectionSets
        minFuel hleftValid hrightValid hleftCoercion hrightCoercion
        hleftFree hrightFree hleftNormal
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
      have htypeObject :=
        (selectionSetNormal_inlineFragment_child_of_mem hleftNormal
          hleftMem).1
      have htypeObjectBool :
          objectTypeNameBool schema typeCondition = true :=
        objectTypeNameBool_eq_true_of_objectType_forNormality schema
          htypeObject
      have hoverlap : schema.typesOverlap parentType typeCondition :=
        selectionSetValid_inlineFragment_some_typesOverlap_of_mem hleftValid
          hleftMem
      have hinclude :
          schema.typeIncludesObjectBool parentType typeCondition = true :=
        typeIncludesObjectBool_of_typesOverlap_object schema hoverlap
          htypeObject
      have hleftChildCoercion :
          selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
            typeCondition leftChildSelectionSet :=
        selectionSetArgumentsCoercibleInPossibleTypes_of_object
          htypeObjectBool
          (selectionSetArgumentsCoercible_inlineFragment_child_of_directiveFree
            (hleftCoercion typeCondition hinclude) hleftFree hleftMem
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              htypeObjectBool))
      have hrightChildCoercion :
          selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
            typeCondition rightChildSelectionSet :=
        selectionSetArgumentsCoercibleInPossibleTypes_of_object
          htypeObjectBool
          (selectionSetArgumentsCoercible_inlineFragment_child_of_directiveFree
            (hrightCoercion typeCondition hinclude) hrightFree hrightMem
            (typeIncludesObjectBool_self_of_objectTypeNameBool schema
              htypeObjectBool))
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
                ∧ selectionSetArgumentsCoercibleInPossibleTypes schema
                    variableValues typeCondition supportSelectionSet
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
              hleftValid hrightValid hleftCoercion hrightCoercion
              hleftFree hrightFree hleftNormal
              hrightNormal hsplit
        · exact
            supportTargetInlineFragmentSelectionSets_child_exists_valid_free_normal
              (schema := schema) (parentType := parentType)
              (typeCondition := typeCondition)
              (supportSelectionSets := supportSelectionSets)
              (childSelectionSet := supportSelectionSet)
              hsupportValid hsupportTarget
      rcases
          ih hleftChildValid hrightChildValid hleftChildCoercion
            hrightChildCoercion
            hleftChildFree
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
          hrightValid hleftCoercion hrightCoercion hleftFree hrightFree
          hleftNormal hrightNormal hnonObject
          hsupportValid hchildWitness
      ⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
