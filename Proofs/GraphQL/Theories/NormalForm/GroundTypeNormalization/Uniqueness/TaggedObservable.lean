import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DataSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.TaggedDiscrimination

/-!
Concrete tagged response witnesses for normal-form uniqueness.

This module packages the invariant used by the semantic-difference induction: a
selection set is separated by running the same tagged resolver environment with a
left and right tag at one concrete runtime object.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def taggedSelectionSetResponseDiffWitness
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType selectionRuntimeType targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (selectionSet : List Selection)
    : Prop :=
  schema.typeIncludesObjectBool parentType selectionRuntimeType = true
  ∧ ∃ leftFields leftErrors rightFields rightErrors,
      Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues fuel selectionRuntimeType
          (.object selectionRuntimeType (some FieldPairProbeTag.left))
          selectionSet
        = ({ data := Execution.ResponseValue.object leftFields, errors := leftErrors }
            : Execution.Response)
      ∧ Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues fuel selectionRuntimeType
          (.object selectionRuntimeType (some FieldPairProbeTag.right))
          selectionSet
        = ({ data := Execution.ResponseValue.object rightFields, errors := rightErrors }
            : Execution.Response)
      ∧ ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftFields)
            (Execution.ResponseValue.object rightFields)

theorem responseData_not_semanticEquivalent_of_taggedSelectionSetResponseDiffWitness
    {schema : Schema} {rootSelectionSet : List Selection}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {parentType selectionRuntimeType targetParent leftField rightField : Name}
    {leftArguments rightArguments : List Argument}
    {selectionSet : List Selection}
    : taggedSelectionSetResponseDiffWitness schema rootSelectionSet
        variableValues fuel parentType selectionRuntimeType targetParent
        leftField rightField leftArguments rightArguments selectionSet
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues fuel selectionRuntimeType
              (.object selectionRuntimeType (some FieldPairProbeTag.left))
              selectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues fuel selectionRuntimeType
              (.object selectionRuntimeType (some FieldPairProbeTag.right))
              selectionSet).data := by
  intro hwitness hsemantic
  rcases hwitness with
    ⟨_hinclude, leftFields, leftErrors, rightFields, rightErrors,
      hleft, hright, hnot⟩
  exact hnot (by simpa [hleft, hright] using hsemantic)

theorem
    taggedSelectionSetResponseDiffWitness_of_object_leaf_field_valid_normal_promoted_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField parentType selectionSet
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              parentType selectionSet
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
              = false
          -> taggedSelectionSetResponseDiffWitness schema rootSelectionSet
              variableValues (fuel + 1) parentType parentType targetParent
              leftField rightField leftArguments rightArguments selectionSet := by
  intro hschema parentType variableDefinitions selectionSet fuel targetParent
    leftField rightField leftArguments rightArguments responseName fieldName
    arguments directives childSelectionSet fieldDefinition hvalid hfree
    hnormal hobject hpromote hheadPromote hfuel hmem hlookup hleaf
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  rcases
      executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
        schema rootSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.left (by omega) hfuel hvalid hfree hnormal
        hinclude hpromote hheadPromote with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
        schema rootSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right (by omega) hfuel hvalid hfree hnormal
        hinclude hpromote hheadPromote with
    ⟨rightFields, rightErrors, hrightResponse⟩
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) parentType
          (.object parentType (some FieldPairProbeTag.left))
          selectionSet).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) parentType
          (.object parentType (some FieldPairProbeTag.right))
          selectionSet).data :=
    responseData_not_semanticEquivalent_of_tagged_object_leaf_field_of_valid_normal_promoted_fuel_ge
      schema rootSelectionSet variableValues hschema parentType
      variableDefinitions selectionSet fuel parentType targetParent
      leftField rightField leftArguments rightArguments hvalid hfree
      hnormal hobject hinclude hpromote hheadPromote hfuel hmem hlookup
      hleaf
  refine ⟨hinclude, leftFields, leftErrors, rightFields, rightErrors,
    hleftResponse, hrightResponse, ?_⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

theorem
    taggedSelectionSetResponseDiffWitness_of_object_child_field_valid_normal_promoted_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ parentType variableDefinitions (selectionSet : List Selection)
            fuel targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            {responseName fieldName : Name} {arguments : List Argument}
            {directives : List DirectiveApplication}
            {childSelectionSet : List Selection}
            {fieldDefinition : FieldDefinition} {runtimeType : Name},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema parentType selectionSet
          -> objectTypeNameBool schema parentType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField parentType selectionSet
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              parentType selectionSet
          -> selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel
          -> Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
          -> schema.lookupField parentType fieldName = some fieldDefinition
          -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ runtimeType = fieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                      arguments parentType rootSelectionSet
                    = some runtimeType))
          -> taggedSelectionSetResponseDiffWitness schema rootSelectionSet
              variableValues (fuel - leafProbeFuel fieldDefinition.outputType)
              fieldDefinition.outputType.namedType runtimeType targetParent
              leftField rightField leftArguments rightArguments childSelectionSet
          -> taggedSelectionSetResponseDiffWitness schema rootSelectionSet
              variableValues (fuel + 1) parentType parentType targetParent
              leftField rightField leftArguments rightArguments selectionSet := by
  intro hschema parentType variableDefinitions selectionSet fuel targetParent
    leftField rightField leftArguments rightArguments responseName fieldName
    arguments directives childSelectionSet fieldDefinition runtimeType
    hvalid hfree hnormal hobject hpromote hheadPromote hfuel hmem hlookup
    hruntime hchildWitness
  have hinclude :
      schema.typeIncludesObjectBool parentType parentType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
  have hleafFuel :
      leafProbeFuel fieldDefinition.outputType ≤ fuel := by
    have hlocal :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType (selectionSet := selectionSet)
        (responseName := responseName) (fieldName := fieldName)
        (arguments := arguments) (directives := directives)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition) hmem hlookup
    omega
  rcases hchildWitness with
    ⟨hfieldInclude, leftChildFields, leftChildErrors, rightChildFields,
      rightChildErrors, hleftChildResponse, hrightChildResponse,
      hchildNot⟩
  rcases
      executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
        schema rootSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.left (by omega) hfuel hvalid hfree hnormal
        hinclude hpromote hheadPromote with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
        schema rootSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right (by omega) hfuel hvalid hfree hnormal
        hinclude hpromote hheadPromote with
    ⟨rightFields, rightErrors, hrightResponse⟩
  have hleftFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1)
              (.object parentType (some FieldPairProbeTag.left))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.left hfuel hvalid hfree hnormal hobject hinclude
        hpromote hheadPromote
  have hrightFieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1)
              (.object parentType (some FieldPairProbeTag.right))
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    exact
      executeField_fieldPairProbe_tagged_object_field_ok_of_valid_normal_promoted_fuel_ge
        schema rootSelectionSet variableValues hschema parentType
        variableDefinitions selectionSet fuel parentType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right hfuel hvalid hfree hnormal hobject hinclude
        hpromote hheadPromote
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) parentType
          (.object parentType (some FieldPairProbeTag.left))
          selectionSet).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) parentType
          (.object parentType (some FieldPairProbeTag.right))
          selectionSet).data :=
    responseData_not_semanticEquivalent_of_tagged_object_child_field_of_field_ok
      schema rootSelectionSet variableValues fuel targetParent leftField
      rightField parentType parentType leftArguments rightArguments hfree
      hnormal hobject hmem hlookup hruntime hfieldInclude hleafFuel
      hleftChildResponse hrightChildResponse hchildNot hleftFieldOk
      hrightFieldOk
  refine ⟨hinclude, leftFields, leftErrors, rightFields, rightErrors,
    hleftResponse, hrightResponse, ?_⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

theorem taggedSelectionSetResponseDiffWitness_of_abstract_inlineFragment_body
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ∀ normalParentType variableDefinitions (selectionSet : List Selection)
            fuel runtimeType targetParent leftField rightField
            (leftArguments rightArguments : List Argument)
            {bodySelectionSet : List Selection},
          Validation.selectionSetValid schema variableDefinitions normalParentType
            selectionSet
          -> selectionSetDirectiveFree selectionSet
          -> selectionSetNormal schema normalParentType selectionSet
          -> objectTypeNameBool schema normalParentType = false
          -> objectTypeNameBool schema runtimeType = true
          -> schema.typeIncludesObjectBool normalParentType runtimeType = true
          -> (∀ abstractTargetParent abstractTargetField targetRuntimeType
                targetFieldDefinition,
                schema.lookupField abstractTargetParent abstractTargetField
                  = some targetFieldDefinition
                -> (TypeRef.named
                      targetFieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType
                    = false
                -> abstractRuntimeForFieldDeep? schema abstractTargetParent
                      abstractTargetField normalParentType selectionSet
                    = some targetRuntimeType
                -> ∃ runtimeType,
                    abstractRuntimeForFieldDeep? schema abstractTargetParent
                        abstractTargetField abstractTargetParent rootSelectionSet
                      = some runtimeType
                    ∧ schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType runtimeType
                      = true)
          -> selectionSetDeepHeadPromotionAvailable schema rootSelectionSet
              normalParentType selectionSet
          -> selectionSetDeepProbeFuel schema normalParentType selectionSet ≤ fuel
          -> Selection.inlineFragment (some runtimeType) [] bodySelectionSet
              ∈ selectionSet
          -> taggedSelectionSetResponseDiffWitness schema rootSelectionSet
              variableValues (fuel + 1) runtimeType runtimeType targetParent
              leftField rightField leftArguments rightArguments bodySelectionSet
          -> taggedSelectionSetResponseDiffWitness schema rootSelectionSet
              variableValues (fuel + 1) normalParentType runtimeType targetParent
              leftField rightField leftArguments rightArguments selectionSet := by
  intro hschema normalParentType variableDefinitions selectionSet fuel
    runtimeType targetParent leftField rightField leftArguments
    rightArguments bodySelectionSet hvalid hfree hnormal hnonObject
    hruntimeObject hinclude hpromote hheadPromote hfuel hinlineMem
    hbodyWitness
  rcases
      executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
        schema rootSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) normalParentType
        variableDefinitions selectionSet fuel runtimeType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.left (by omega) hfuel hvalid hfree hnormal
        hinclude hpromote hheadPromote with
    ⟨leftFields, leftErrors, hleftResponse⟩
  rcases
      executeSelectionSetAsResponse_fieldPairProbe_tagged_of_valid_normal_promoted_fuel_ge_size
        schema rootSelectionSet variableValues hschema
        (SelectionSet.size selectionSet + 1) normalParentType
        variableDefinitions selectionSet fuel runtimeType targetParent
        leftField rightField leftArguments rightArguments
        FieldPairProbeTag.right (by omega) hfuel hvalid hfree hnormal
        hinclude hpromote hheadPromote with
    ⟨rightFields, rightErrors, hrightResponse⟩
  rcases List.mem_iff_append.mp hinlineMem with
    ⟨pref, suffix, hselectionSet⟩
  subst selectionSet
  have hbodyNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) runtimeType
          (.object runtimeType (some FieldPairProbeTag.left))
          bodySelectionSet).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) runtimeType
          (.object runtimeType (some FieldPairProbeTag.right))
          bodySelectionSet).data :=
    responseData_not_semanticEquivalent_of_taggedSelectionSetResponseDiffWitness
      hbodyWitness
  have hdataNot :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) runtimeType
          (.object runtimeType (some FieldPairProbeTag.left))
          (pref ++ Selection.inlineFragment (some runtimeType) []
            bodySelectionSet :: suffix)).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues (fuel + 1) runtimeType
          (.object runtimeType (some FieldPairProbeTag.right))
          (pref ++ Selection.inlineFragment (some runtimeType) []
            bodySelectionSet :: suffix)).data :=
    responseData_not_semanticEquivalent_of_tagged_abstract_inlineFragment_body
      schema rootSelectionSet variableValues fuel targetParent leftField
      rightField normalParentType runtimeType leftArguments rightArguments
      hnonObject hruntimeObject hfree hnormal hbodyNot
  refine ⟨hinclude, leftFields, leftErrors, rightFields, rightErrors,
    hleftResponse, hrightResponse, ?_⟩
  intro hobjects
  exact hdataNot (by simpa [hleftResponse, hrightResponse] using hobjects)

end GroundTypeNormalization

end NormalForm

end GraphQL
