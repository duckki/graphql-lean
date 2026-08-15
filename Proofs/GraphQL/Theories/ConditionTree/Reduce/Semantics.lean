import Proofs.GraphQL.Theories.ConditionTree.Reduce.RuntimeBundles
import Proofs.GraphQL.Theories.ConditionTree.ExecutionEquivalence

/-! Recursive semantic equivalence for condition-tree reduction. -/

namespace GraphQL
namespace ConditionTree
open GraphQL.Execution
open NormalForm.GroundTypeNormalization
open NormalForm.GroundTypeNormalization.ReorderingSoundness
open ExecutionEquivalence
open RuntimeExtraction
open Execution.FieldGroups

-- Reduction is extracted in a static scope but executed at a concrete object scope.
-- The merge/scoping facts below may therefore come from the static validation parent,
-- while lookup and completion readiness belong to the concrete execution parent.
structure ReductionExecutionBoundary {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues) where
  extractionParentType : Name
  parentType : Name
  runtimeType : Name
  ref : ObjectRef
  selectionSet : List Selection
  allSpecGroups : List (Name × List ExecutableField)
  allSpecGroups_eq
    : allSpecGroups
      = collectFields schema variableValues parentType
          (.object runtimeType ref) selectionSet
  extractionPossible
    : (schema.getPossibleTypes extractionParentType).contains runtimeType = true
  parentObject : schema.objectType parentType
  parentRuntimeApplies
    : Algorithms.ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies
        schema runtimeType parentType
  semanticsReady : NormalForm.selectionSetSemanticsReady schema parentType selectionSet
  fieldsCanMerge : FieldMerge.fieldsInSetCanMerge schema extractionParentType selectionSet
  groupsFieldCompatible
    : Algorithms.ExecutionUngroupedUncached.Eager.CollectedGroupsFieldValidationMergeCompatible
        allSpecGroups
  argumentsNodup
    : Algorithms.ExecutionUngroupedUncached.Eager.CollectedGroupsArgumentsNodup
        allSpecGroups
  childrenArgumentsNodup
    : ∀ field,
        field
          ∈ Algorithms.ExecutionUngroupedUncached.Eager.collectedExecutableFields
              allSpecGroups
        -> Execution.selectionSetArgumentsNodup field.selectionSet
  groupRuntimeScoped
    : ∀ {responseName fields},
        (responseName, fields) ∈ allSpecGroups
        -> Algorithms.ExecutionUngroupedUncached.Eager.ExecutableFieldsRuntimeScopedBy
            schema runtimeType
            (FieldMerge.collectFields schema extractionParentType selectionSet) fields

theorem ReductionExecutionBoundary.groupsSameParent
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ReductionExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    : Algorithms.ExecutionUngroupedUncached.Eager.CollectedGroupsSameResponseParent
        boundary.allSpecGroups := by
  rw [boundary.allSpecGroups_eq]
  exact Algorithms.ExecutionUngroupedUncached.Eager.collectFields_sameResponseParent schema
    variableValues boundary.parentType
    (.object boundary.runtimeType boundary.ref) boundary.selectionSet

theorem ReductionExecutionBoundary.groupField_mem_collected
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ReductionExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    {responseName : Name} {fields : List ExecutableField}
    (hgroup : (responseName, fields) ∈ boundary.allSpecGroups)
    {field : ExecutableField} (hfield : field ∈ fields)
    : field
      ∈ Algorithms.ExecutionUngroupedUncached.Eager.collectedExecutableFields
          boundary.allSpecGroups := by
  rw [← RuntimeExtraction.flattenCollectedFields_eq_collectedExecutableFields]
  exact (mem_flattenCollectedFields_iff boundary.allSpecGroups field).mpr
    ⟨responseName, fields, hgroup, hfield⟩

theorem ReductionExecutionBoundary.fieldArgumentsNodup
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ReductionExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    {field : ExecutableField}
    (hfield
      : field
        ∈ Algorithms.ExecutionUngroupedUncached.Eager.collectedExecutableFields
            boundary.allSpecGroups)
    : (field.arguments.map Argument.name).Nodup := by
  rw [← RuntimeExtraction.flattenCollectedFields_eq_collectedExecutableFields] at hfield
  rcases (mem_flattenCollectedFields_iff boundary.allSpecGroups field).mp hfield with
    ⟨responseName, fields, hgroup, hfield⟩
  exact boundary.argumentsNodup responseName fields hgroup field hfield

theorem ReductionExecutionBoundary.fieldLookup
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ReductionExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    {responseName : Name} {fields : List ExecutableField}
    (hgroup : (responseName, fields) ∈ boundary.allSpecGroups)
    {field : ExecutableField} (hfield : field ∈ fields)
    : ∃ fieldDefinition,
        schema.lookupField field.parentType field.fieldName = some fieldDefinition := by
  have hlookup :=
    Algorithms.ExecutionUngroupedUncached.Eager.collectFields_lookupValid_of_selectionSetSemanticsReady_object schema
      variableValues boundary.parentType boundary.runtimeType boundary.ref
      boundary.selectionSet boundary.parentObject boundary.parentRuntimeApplies
      boundary.semanticsReady
  rw [← boundary.allSpecGroups_eq] at hlookup
  rw [← RuntimeExtraction.flattenCollectedFields_eq_collectedExecutableFields] at hlookup
  have hparent : field.parentType = boundary.parentType := by
    have hgroupsParent : Algorithms.ExecutionUngroupedUncached.Eager.CollectedGroupsParent
        boundary.parentType boundary.allSpecGroups := by
      rw [boundary.allSpecGroups_eq]
      exact Algorithms.ExecutionUngroupedUncached.Eager.collectFields_parent schema
        variableValues boundary.parentType
        (.object boundary.runtimeType boundary.ref) boundary.selectionSet
    exact hgroupsParent responseName fields hgroup field hfield
  rw [hparent]
  exact hlookup field
    ((mem_flattenCollectedFields_iff boundary.allSpecGroups field).mpr
      ⟨responseName, fields, hgroup, hfield⟩)

theorem ReductionExecutionBoundary.fieldChildSemanticsReady
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ReductionExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    {responseName : Name} {fields : List ExecutableField}
    (hgroup : (responseName, fields) ∈ boundary.allSpecGroups)
    {field : ExecutableField} (hfield : field ∈ fields)
    (fieldDefinition : FieldDefinition)
    (hlookup : schema.lookupField field.parentType field.fieldName = some fieldDefinition)
    (childRuntime : Name)
    (hinclude
      : schema.typeIncludesObjectBool fieldDefinition.outputType.namedType childRuntime
        = true)
    : NormalForm.selectionSetSemanticsReady schema childRuntime field.selectionSet := by
  have hready :=
    Algorithms.ExecutionUngroupedUncached.Eager.collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object schema
      variableValues boundary.parentType boundary.runtimeType boundary.ref
      boundary.selectionSet boundary.parentObject boundary.parentRuntimeApplies
      boundary.semanticsReady
  rw [← boundary.allSpecGroups_eq] at hready
  rw [← RuntimeExtraction.flattenCollectedFields_eq_collectedExecutableFields] at hready
  exact hready field
    ((mem_flattenCollectedFields_iff boundary.allSpecGroups field).mpr
      ⟨responseName, fields, hgroup, hfield⟩)
    fieldDefinition hlookup childRuntime hinclude

set_option maxRecDepth 10000 in
mutual
  theorem reductionUnits_execute_equivalent {ObjectRef : Type} (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
      (hschema : SchemaWellFormedness.schemaWellFormed schema) (fuel : Nat)
      (validationParentType runtimeType : Name) (ref : ObjectRef)
      (units : List ReductionUnit) (leftSelectionSet rightSelectionSet : List Selection)
      (hobject : schema.objectType runtimeType)
      (hvalidationPossible
        : (schema.getPossibleTypes validationParentType).contains runtimeType = true)
      (hrightReady
        : NormalForm.selectionSetSemanticsReady schema runtimeType rightSelectionSet)
      (hrightCompatible
        : Algorithms.ExecutionUngroupedUncached.Eager.CollectedGroupsFieldValidationMergeCompatible
            (collectFields schema variableValues runtimeType
              (.object runtimeType ref) rightSelectionSet))
      (hrightArgumentsNodup
        : Algorithms.ExecutionUngroupedUncached.Eager.CollectedGroupsArgumentsNodup
            (collectFields schema variableValues runtimeType
              (.object runtimeType ref) rightSelectionSet))
      (hrightChildrenArgumentsNodup
        : ∀ field,
            field
              ∈ Algorithms.ExecutionUngroupedUncached.Eager.collectedExecutableFields
                  (collectFields schema variableValues runtimeType
                    (.object runtimeType ref) rightSelectionSet)
            -> Execution.selectionSetArgumentsNodup field.selectionSet)
      (hrightRuntimeScoped
        : ∀ {responseName fields},
            (responseName, fields)
              ∈ collectFields schema variableValues runtimeType
                  (.object runtimeType ref) rightSelectionSet
            -> Algorithms.ExecutionUngroupedUncached.Eager.ExecutableFieldsRuntimeScopedBy
                schema runtimeType
                (FieldMerge.collectFields schema validationParentType rightSelectionSet)
                fields)
      (hrightMerge
        : FieldMerge.fieldsInSetCanMerge schema validationParentType rightSelectionSet)
      (happlicable
        : ReductionUnit.AllRuntimeApplicable schema variableValues runtimeType units)
      (hleft : (ReductionUnit.outputSelectionSet schema units).Perm leftSelectionSet)
      (hright : (ReductionUnit.inputSelectionSet units).Perm rightSelectionSet)
      : SelectionSetResultEquivalent
          (Execution.executeSelectionSet schema resolvers variableValues fuel runtimeType
            (.object runtimeType ref) leftSelectionSet)
          (Execution.executeSelectionSet schema resolvers variableValues fuel runtimeType
            (.object runtimeType ref) rightSelectionSet) := by
    let bundles := ReductionUnit.runtimeBundlesFor schema variableValues runtimeType
      runtimeType ref units
    let bundleGroups := groupRuntimeFieldBundles bundles
    let leftGroups := collectFields schema variableValues runtimeType
      (.object runtimeType ref) leftSelectionSet
    let rightGroups := collectFields schema variableValues runtimeType
      (.object runtimeType ref) rightSelectionSet
    have hself : schema.typeIncludesObjectBool runtimeType runtimeType = true :=
      NormalForm.object_typeIncludesObjectBool_self schema hobject
    let boundary : ReductionExecutionBoundary (ObjectRef := ObjectRef) schema
        variableValues :=
      {
        extractionParentType := validationParentType
        parentType := runtimeType
        runtimeType := runtimeType
        ref := ref
        selectionSet := rightSelectionSet
        allSpecGroups := rightGroups
        allSpecGroups_eq := rfl
        extractionPossible := hvalidationPossible
        parentObject := hobject
        parentRuntimeApplies := hself
        semanticsReady := hrightReady
        fieldsCanMerge := hrightMerge
        groupsFieldCompatible := hrightCompatible
        argumentsNodup := hrightArgumentsNodup
        childrenArgumentsNodup := hrightChildrenArgumentsNodup
        groupRuntimeScoped := hrightRuntimeScoped
      }
    have hleftEquivalent := ReductionUnit.reducedGroups_permutationEquivalent
      schema variableValues runtimeType runtimeType ref units leftSelectionSet
      happlicable hleft
    have hrightEquivalent := ReductionUnit.sourceGroups_permutationEquivalent
      schema variableValues runtimeType runtimeType ref units rightSelectionSet
      happlicable hright
    have hbundles : RuntimeFieldBundle.GroupsWellFormed schema bundleGroups := by
      apply RuntimeFieldBundle.groupsWellFormed_of_group
      exact ReductionUnit.runtimeBundlesFor_wellFormed schema variableValues
        runtimeType runtimeType ref units
    have hchildren : RuntimeFieldBundle.GroupsChildrenRuntimeApplicable schema
        variableValues runtimeType bundleGroups := by
      intro bundle hbundle runtimeFieldDefinition hlookup childRuntimeType hinclude
      have hbundle' : bundle ∈ bundles :=
        (flattenRuntimeFieldBundleGroups_group_perm bundles).mem_iff.mp hbundle
      exact ReductionUnit.runtimeBundlesFor_childrenRuntimeApplicable schema
        variableValues hschema runtimeType ref units happlicable bundle hbundle'
        runtimeFieldDefinition hlookup childRuntimeType hinclude
    change SelectionSetResultEquivalent
      (Execution.executeCollectedFields schema resolvers variableValues fuel
        (.object runtimeType ref) leftGroups)
      (Execution.executeCollectedFields schema resolvers variableValues fuel
        (.object runtimeType ref) rightGroups)
    exact executeBundleGroups_equivalent schema resolvers variableValues hschema
      boundary fuel bundleGroups leftGroups rightGroups hleftEquivalent
      hrightEquivalent (by intro group hgroup; exact hgroup) hbundles hchildren
  termination_by (fuel, 4, 0)
  decreasing_by
    apply Prod.Lex.right
    apply Prod.Lex.left
    omega

  theorem executeBundleGroups_equivalent
      {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boundary
        : ReductionExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
      (fuel : Nat)
      (bundleGroups : List (Name × List RuntimeFieldBundle))
      (leftGroups rightGroups : List (Name × List ExecutableField))
      (leftEquivalent
        : RuntimeGroupsPermutationEquivalent
            (reducedBundleGroups bundleGroups) leftGroups)
      (rightEquivalent
        : RuntimeGroupsPermutationEquivalent
            (sourceBundleGroups bundleGroups) rightGroups)
      (rightSubset : GroupsSubset rightGroups boundary.allSpecGroups)
      (hbundles : RuntimeFieldBundle.GroupsWellFormed schema bundleGroups)
      (hchildren
        : RuntimeFieldBundle.GroupsChildrenRuntimeApplicable schema
            variableValues boundary.runtimeType bundleGroups)
      : SelectionSetResultEquivalent
          (Execution.executeCollectedFields schema resolvers variableValues fuel
            (.object boundary.runtimeType boundary.ref) leftGroups)
          (Execution.executeCollectedFields schema resolvers variableValues fuel
            (.object boundary.runtimeType boundary.ref) rightGroups) := by
    cases hbundleGroups : bundleGroups with
    | nil =>
        subst bundleGroups
        have hleftNil : leftGroups = [] := by
          cases leftGroups with
          | nil => rfl
          | cons group rest =>
              have hnonempty := (leftEquivalent.rightWellFormed group (by simp)).1
              have hfield : ∃ field, field ∈ group.2 :=
                List.exists_mem_of_ne_nil group.2 hnonempty
              rcases hfield with ⟨field, hfield⟩
              have : field ∈ flattenCollectedFields ([] : List (Name × List ExecutableField)) :=
                leftEquivalent.fieldsPerm.mem_iff.mpr (by
                  simp [hfield])
              simp [flattenCollectedFields] at this
        have hrightNil : rightGroups = [] := by
          cases rightGroups with
          | nil => rfl
          | cons group rest =>
              have hnonempty := (rightEquivalent.rightWellFormed group (by simp)).1
              have hfield : ∃ field, field ∈ group.2 :=
                List.exists_mem_of_ne_nil group.2 hnonempty
              rcases hfield with ⟨field, hfield⟩
              have : field ∈ flattenCollectedFields ([] : List (Name × List ExecutableField)) :=
                rightEquivalent.fieldsPerm.mem_iff.mpr (by
                  simp [hfield])
              simp [flattenCollectedFields] at this
        subst leftGroups
        subst rightGroups
        exact selectionSetResultEquivalent_of_eq rfl
    | cons bundleGroup bundleTail =>
        subst bundleGroups
        rcases bundleGroup with ⟨responseName, bundles⟩
        obtain ⟨leftFields, leftTail, hleftPerm, leftAligned⟩ :=
          leftEquivalent.alignRightHead
        obtain ⟨rightFields, rightTail, hrightPerm, rightAligned⟩ :=
          rightEquivalent.alignRightHead
        have alignedSubset : GroupsSubset
            ((responseName, rightFields) :: rightTail) boundary.allSpecGroups :=
          rightSubset.of_perm hrightPerm
        have hrightGroup : (responseName, rightFields) ∈ boundary.allSpecGroups :=
          alignedSubset _ (by simp)
        have hbundleNonempty : bundles ≠ [] := by
          have := (leftAligned.leftWellFormed
            (responseName, bundles.map RuntimeFieldBundle.reducedField) (by simp)).1
          intro hempty
          subst bundles
          exact this rfl
        cases hbundlesList : bundles with
        | nil => contradiction
        | cons firstBundle restBundles =>
            subst bundles
            have hleftNonempty := (leftAligned.rightWellFormed
              (responseName, leftFields) (by simp)).1
            have hrightNonempty := (rightAligned.rightWellFormed
              (responseName, rightFields) (by simp)).1
            cases hleftFields : leftFields with
            | nil => contradiction
            | cons leftHead leftRest =>
                subst leftFields
                cases hrightFields : rightFields with
                | nil => contradiction
                | cons rightHead rightRest =>
                    subst rightFields
                    have hleftFieldsPerm := leftAligned.headFields
                    have hrightFieldsPerm := rightAligned.headFields
                    have hleftCanonical : leftHead ∈
                        (firstBundle :: restBundles).map
                          RuntimeFieldBundle.reducedField :=
                      hleftFieldsPerm.mem_iff.mpr (by simp)
                    rcases List.mem_map.mp hleftCanonical with
                      ⟨headBundle, hheadBundle, hleftHeadEq⟩
                    subst leftHead
                    have hheadBundleWF := hbundles headBundle (by
                      simp only [flattenRuntimeFieldBundleGroups]
                      exact List.mem_append.mpr (Or.inl hheadBundle))
                    rcases hheadBundleWF.representative with
                      ⟨representative, hrepresentative, hrepresentativeParent,
                        hrepresentativeField, hrepresentativeArguments⟩
                    have hrepresentativeCanonical : representative ∈
                        (firstBundle :: restBundles).flatMap
                          RuntimeFieldBundle.sourceFields :=
                      List.mem_flatMap.mpr
                        ⟨headBundle, hheadBundle, hrepresentative⟩
                    have hrepresentativeRight : representative ∈ rightHead :: rightRest :=
                      hrightFieldsPerm.mem_iff.mp hrepresentativeCanonical
                    have hrightWellFormed := rightAligned.rightWellFormed
                      (responseName, rightHead :: rightRest) (by simp)
                    have hrepresentativeResponse := hrightWellFormed.2 representative
                      hrepresentativeRight
                    have hrightResponse := hrightWellFormed.2 rightHead (by simp)
                    have hsameParent := boundary.groupsSameParent responseName
                      (rightHead :: rightRest) hrightGroup representative rightHead
                      hrepresentativeRight (by simp)
                      (hrepresentativeResponse.trans hrightResponse.symm)
                    have hcompatible := boundary.groupsFieldCompatible responseName
                      (rightHead :: rightRest) hrightGroup representative rightHead
                      hrepresentativeRight (by simp)
                      (hrepresentativeResponse.trans hrightResponse.symm)
                    have hparent : headBundle.reducedField.parentType = rightHead.parentType :=
                      hrepresentativeParent.symm.trans hsameParent
                    have hfieldName : headBundle.reducedField.fieldName = rightHead.fieldName :=
                      hrepresentativeField.symm.trans hcompatible.1
                    have harguments : Argument.argumentsEquivalent
                        headBundle.reducedField.arguments rightHead.arguments := by
                      rw [← hrepresentativeArguments]
                      exact hcompatible.2
                    obtain ⟨fieldDefinition, hrightLookup⟩ :=
                      boundary.fieldLookup (field := rightHead) hrightGroup (by simp)
                    have hleftLookup : schema.lookupField
                        headBundle.reducedField.parentType headBundle.reducedField.fieldName
                        = some fieldDefinition := by
                      rw [hparent, hfieldName]
                      exact hrightLookup
                    have hreducedArgumentsNodup :
                        (headBundle.reducedField.arguments.map Argument.name).Nodup := by
                      rw [← hrepresentativeArguments]
                      exact boundary.fieldArgumentsNodup
                        (boundary.groupField_mem_collected hrightGroup
                          hrepresentativeRight)
                    have hrightArgumentsNodup :
                        (rightHead.arguments.map Argument.name).Nodup :=
                      boundary.fieldArgumentsNodup
                        (boundary.groupField_mem_collected hrightGroup (by simp))
                    have hcoercedArguments : ArgumentCoercionResult.equivalent
                        (coerceArgumentValues schema variableValues
                          fieldDefinition.arguments headBundle.reducedField.arguments)
                        (coerceArgumentValues schema variableValues
                          fieldDefinition.arguments rightHead.arguments) :=
                      coerceArgumentValues_equivalent_of_equivalent schema variableValues
                        fieldDefinition.arguments hreducedArgumentsNodup
                        hrightArgumentsNodup harguments
                    have hresolveEq :
                        coerceAndResolveFieldValue schema resolvers variableValues fieldDefinition
                            headBundle.reducedField.parentType
                            headBundle.reducedField.fieldName
                            headBundle.reducedField.arguments
                            (.object boundary.runtimeType boundary.ref)
                          = coerceAndResolveFieldValue schema resolvers variableValues
                            fieldDefinition
                            rightHead.parentType rightHead.fieldName rightHead.arguments
                            (.object boundary.runtimeType boundary.ref) := by
                      unfold coerceAndResolveFieldValue
                      cases hleftCoerce : coerceArgumentValues schema variableValues
                              fieldDefinition.arguments
                              headBundle.reducedField.arguments <;>
                        cases hrightCoerce : coerceArgumentValues schema variableValues
                              fieldDefinition.arguments rightHead.arguments <;>
                        simp [hleftCoerce, hrightCoerce,
                          ArgumentCoercionResult.equivalent] at hcoercedArguments ⊢
                      rw [hparent, hfieldName]
                      exact resolvers.resolve_argumentsEquivalent _ _ _ _ _
                        hcoercedArguments
                    have hlookupAll : ∀ field,
                        field ∈ rightHead :: rightRest
                        -> schema.lookupField field.parentType field.fieldName
                          = some fieldDefinition := by
                      intro field hfield
                      have hfieldResponse := hrightWellFormed.2 field hfield
                      have hsameField := boundary.groupsFieldCompatible responseName
                        (rightHead :: rightRest) hrightGroup rightHead field (by simp)
                        hfield (hrightResponse.trans hfieldResponse.symm)
                      have hsameParent' := boundary.groupsSameParent responseName
                        (rightHead :: rightRest) hrightGroup rightHead field (by simp)
                        hfield (hrightResponse.trans hfieldResponse.symm)
                      rw [← hsameParent', ← hsameField.1]
                      exact hrightLookup
                    have hlookupBundles : ∀ bundle,
                        bundle ∈ firstBundle :: restBundles
                        -> schema.lookupField boundary.runtimeType
                            bundle.reducedField.fieldName = some fieldDefinition := by
                      intro bundle hbundle
                      have hbundleWF := hbundles bundle (by
                        simp only [flattenRuntimeFieldBundleGroups]
                        exact List.mem_append.mpr (Or.inl hbundle))
                      rcases hbundleWF.representative with
                        ⟨sourceField, hsourceField, hsourceParent, hsourceName,
                          _hsourceArguments⟩
                      have hsourceCanonical : sourceField ∈
                          (firstBundle :: restBundles).flatMap
                            RuntimeFieldBundle.sourceFields :=
                        List.mem_flatMap.mpr ⟨bundle, hbundle, hsourceField⟩
                      have hsourceRight : sourceField ∈ rightHead :: rightRest :=
                        hrightFieldsPerm.mem_iff.mp hsourceCanonical
                      have hsourceResponse := hrightWellFormed.2 sourceField hsourceRight
                      have hsameField := boundary.groupsFieldCompatible responseName
                        (rightHead :: rightRest) hrightGroup sourceField rightHead
                        hsourceRight (by simp)
                        (hsourceResponse.trans hrightResponse.symm)
                      have hsourceRuntimeParent : sourceField.parentType = boundary.runtimeType := by
                        have hgroupsParent :
                            Algorithms.ExecutionUngroupedUncached.Eager.CollectedGroupsParent
                              boundary.parentType
                            boundary.allSpecGroups := by
                          rw [boundary.allSpecGroups_eq]
                          exact Algorithms.ExecutionUngroupedUncached.Eager.collectFields_parent
                            schema variableValues boundary.parentType
                            (.object boundary.runtimeType boundary.ref)
                            boundary.selectionSet
                        have hparent' := hgroupsParent responseName
                          (rightHead :: rightRest) hrightGroup sourceField hsourceRight
                        have hruntimeParent : boundary.runtimeType = boundary.parentType := by
                          exact object_typeIncludesObjectBool_eq_self schema
                            boundary.parentObject boundary.parentRuntimeApplies
                        exact hparent'.trans hruntimeParent.symm
                      have hlookup := hlookupAll sourceField hsourceRight
                      rw [hsourceRuntimeParent, hsourceName] at hlookup
                      exact hlookup
                    have htail := executeBundleGroups_equivalent schema resolvers
                      variableValues hschema boundary fuel bundleTail leftTail rightTail
                      leftAligned.tails rightAligned.tails alignedSubset.tail
                      (by
                        intro bundle hbundle
                        exact hbundles bundle (by
                          simp only [flattenRuntimeFieldBundleGroups]
                          exact List.mem_append.mpr (Or.inr hbundle)))
                      (by
                        intro bundle hbundle fieldDefinition hlookup childRuntime hinclude
                        exact hchildren bundle (by
                          simp only [flattenRuntimeFieldBundleGroups]
                          exact List.mem_append.mpr (Or.inr hbundle))
                          fieldDefinition hlookup childRuntime hinclude)
                    cases fuel with
                    | zero =>
                        have hhead : ResponseValueResultEquivalent
                            (.error 1 : Result ResponseValue) (.error 1) := rfl
                        have hcombined :=
                          selectionSetResultEquivalent_combine_singleField_append
                            (responseName := responseName) hhead htail
                        have hcore : SelectionSetResultEquivalent
                            (Execution.executeCollectedFields schema resolvers variableValues 0
                              (.object boundary.runtimeType boundary.ref)
                              ((responseName, headBundle.reducedField :: leftRest) :: leftTail))
                            (Execution.executeCollectedFields schema resolvers variableValues 0
                              (.object boundary.runtimeType boundary.ref)
                              ((responseName, rightHead :: rightRest) :: rightTail)) := by
                          simpa [Execution.executeCollectedFields, Execution.executeField, outOfFuel,
                            singleFieldResult,
                            hleftLookup, hrightLookup] using hcombined
                        have hleftReorder := executeCollectedFields_equivalent_of_perm
                          schema resolvers variableValues 0
                          (.object boundary.runtimeType boundary.ref) hleftPerm
                          leftEquivalent.rightKeysNodup
                        have hrightReorder := executeCollectedFields_equivalent_of_perm
                          schema resolvers variableValues 0
                          (.object boundary.runtimeType boundary.ref) hrightPerm
                          rightEquivalent.rightKeysNodup
                        exact selectionSetResultEquivalent_trans hleftReorder
                          (selectionSetResultEquivalent_trans hcore
                            (selectionSetResultEquivalent_symm hrightReorder))
                    | succ completionFuel =>
                        cases hresolved
                              : coerceAndResolveFieldValue schema resolvers variableValues
                                  fieldDefinition rightHead.parentType
                                  rightHead.fieldName rightHead.arguments
                                  (.object boundary.runtimeType boundary.ref) with
                        | none =>
                            have hleftResolved : coerceAndResolveFieldValue schema resolvers
                                variableValues fieldDefinition
                                headBundle.reducedField.parentType
                                headBundle.reducedField.fieldName
                                headBundle.reducedField.arguments
                                (.object boundary.runtimeType boundary.ref) = none := by
                              rw [hresolveEq]
                              exact hresolved
                            have hhead := responseValueResultEquivalent_of_eq
                              (left := handleFieldError fieldDefinition.outputType)
                              (right := handleFieldError fieldDefinition.outputType) rfl
                            have hcombined :=
                              selectionSetResultEquivalent_combine_singleField_append
                                (responseName := responseName) hhead htail
                            have hcore : SelectionSetResultEquivalent
                                (Execution.executeCollectedFields schema resolvers variableValues
                                  (completionFuel + 1)
                                  (.object boundary.runtimeType boundary.ref)
                                  ((responseName, headBundle.reducedField :: leftRest) :: leftTail))
                                (Execution.executeCollectedFields schema resolvers variableValues
                                  (completionFuel + 1)
                                  (.object boundary.runtimeType boundary.ref)
                                  ((responseName, rightHead :: rightRest) :: rightTail)) := by
                              simpa [Execution.executeCollectedFields, Execution.executeField, hleftLookup,
                                hrightLookup, hleftResolved, hresolved] using hcombined
                            have hleftReorder := executeCollectedFields_equivalent_of_perm
                              schema resolvers variableValues (completionFuel + 1)
                              (.object boundary.runtimeType boundary.ref) hleftPerm
                              leftEquivalent.rightKeysNodup
                            have hrightReorder := executeCollectedFields_equivalent_of_perm
                              schema resolvers variableValues (completionFuel + 1)
                              (.object boundary.runtimeType boundary.ref) hrightPerm
                              rightEquivalent.rightKeysNodup
                            exact selectionSetResultEquivalent_trans hleftReorder
                              (selectionSetResultEquivalent_trans hcore
                                (selectionSetResultEquivalent_symm hrightReorder))
                        | some resolved =>
                            have hleftResolved : coerceAndResolveFieldValue schema resolvers
                                variableValues fieldDefinition
                                headBundle.reducedField.parentType
                                headBundle.reducedField.fieldName
                                headBundle.reducedField.arguments
                                (.object boundary.runtimeType boundary.ref) = some resolved := by
                              rw [hresolveEq]
                              exact hresolved
                            have hcompletion := completeValueBundles_equivalent schema
                              resolvers variableValues hschema boundary completionFuel
                              responseName (firstBundle :: restBundles)
                              (headBundle.reducedField :: leftRest)
                              (rightHead :: rightRest) fieldDefinition.outputType resolved
                              fieldDefinition hrightGroup hleftFieldsPerm hrightFieldsPerm
                              hlookupAll rfl
                              (by
                                intro bundle hbundle
                                exact hbundles bundle (by
                                  simp only [flattenRuntimeFieldBundleGroups]
                                  exact List.mem_append.mpr (Or.inl hbundle)))
                              (by
                                intro bundle hbundle fieldDefinition hlookup childRuntime hinclude
                                exact hchildren bundle (by
                                  simp only [flattenRuntimeFieldBundleGroups]
                                  exact List.mem_append.mpr (Or.inl hbundle))
                                  fieldDefinition hlookup childRuntime hinclude)
                              hlookupBundles
                            have hcombined :=
                              selectionSetResultEquivalent_combine_singleField_append
                                (responseName := responseName) hcompletion htail
                            have hcore : SelectionSetResultEquivalent
                                (Execution.executeCollectedFields schema resolvers variableValues
                                  (completionFuel + 1)
                                  (.object boundary.runtimeType boundary.ref)
                                  ((responseName, headBundle.reducedField :: leftRest) :: leftTail))
                                (Execution.executeCollectedFields schema resolvers variableValues
                                  (completionFuel + 1)
                                  (.object boundary.runtimeType boundary.ref)
                                  ((responseName, rightHead :: rightRest) :: rightTail)) := by
                              simpa [Execution.executeCollectedFields, Execution.executeField, hleftLookup,
                                hrightLookup, hleftResolved, hresolved] using hcombined
                            have hleftReorder := executeCollectedFields_equivalent_of_perm
                              schema resolvers variableValues (completionFuel + 1)
                              (.object boundary.runtimeType boundary.ref) hleftPerm
                              leftEquivalent.rightKeysNodup
                            have hrightReorder := executeCollectedFields_equivalent_of_perm
                              schema resolvers variableValues (completionFuel + 1)
                              (.object boundary.runtimeType boundary.ref) hrightPerm
                              rightEquivalent.rightKeysNodup
                            exact selectionSetResultEquivalent_trans hleftReorder
                              (selectionSetResultEquivalent_trans hcore
                                (selectionSetResultEquivalent_symm hrightReorder))
  termination_by (fuel, 3, sizeOf bundleGroups)
  decreasing_by
    all_goals
      first
      | apply Prod.Lex.right
        apply Prod.Lex.right
        simp_wf
        simp [hbundleGroups]
        omega
      | apply Prod.Lex.left
        omega

  theorem completeValueBundles_equivalent
      {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boundary
        : ReductionExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
      (fuel : Nat) (responseName : Name)
      (bundles : List RuntimeFieldBundle)
      (leftFields rightFields : List ExecutableField)
      (fieldType : TypeRef) (value : ResolverValue ObjectRef)
      (fieldDefinition : FieldDefinition)
      (hrightGroup : (responseName, rightFields) ∈ boundary.allSpecGroups)
      (hleftFields : (bundles.map RuntimeFieldBundle.reducedField).Perm leftFields)
      (hrightFields : (bundles.flatMap RuntimeFieldBundle.sourceFields).Perm rightFields)
      (hlookupAll
        : ∀ field,
            field ∈ rightFields
            -> schema.lookupField field.parentType field.fieldName = some fieldDefinition)
      (hnamed : fieldType.namedType = fieldDefinition.outputType.namedType)
      (hbundles : ∀ bundle, bundle ∈ bundles -> bundle.WellFormed schema)
      (hchildren
        : ∀ bundle,
            bundle ∈ bundles
            -> ∀ runtimeFieldDefinition,
                schema.lookupField boundary.runtimeType bundle.reducedField.fieldName
                  = some runtimeFieldDefinition
                -> ∀ childRuntimeType,
                    schema.typeIncludesObjectBool
                        runtimeFieldDefinition.outputType.namedType childRuntimeType
                      = true
                    -> bundle.ChildrenRuntimeApplicable schema variableValues
                        childRuntimeType)
      (hlookupBundles
        : ∀ bundle,
            bundle ∈ bundles
            -> schema.lookupField boundary.runtimeType bundle.reducedField.fieldName
                = some fieldDefinition)
      : ResponseValueResultEquivalent
          (Execution.completeValue schema resolvers variableValues fuel fieldType
            leftFields value)
          (Execution.completeValue schema resolvers variableValues fuel fieldType
            rightFields value) := by
    cases fuel with
    | zero =>
        exact responseValueResultEquivalent_of_eq (by simp [Execution.completeValue])
    | succ nextFuel =>
        cases hfieldType : fieldType with
        | nonNull inner =>
            subst fieldType
            simp only [Execution.completeValue]
            apply responseValueResultEquivalent_nonNullCompletion
            apply completeValueBundles_equivalent schema resolvers variableValues hschema
              boundary (nextFuel + 1) responseName bundles leftFields rightFields inner
              value fieldDefinition hrightGroup hleftFields hrightFields hlookupAll
            · exact hnamed
            · exact hbundles
            · exact hchildren
            · exact hlookupBundles
        | named typeName =>
            subst fieldType
            cases hvalue : value with
            | null =>
                exact responseValueResultEquivalent_of_eq (by simp [Execution.completeValue])
            | scalar scalarValue =>
                exact responseValueResultEquivalent_of_eq (by simp [Execution.completeValue])
            | list values =>
                exact responseValueResultEquivalent_of_eq (by simp [Execution.completeValue])
            | object childRuntime childRef =>
                subst value
                by_cases hinclude :
                    schema.typeIncludesObjectBool typeName childRuntime = true
                · let childUnits := RuntimeFieldBundle.allChildUnits bundles
                  let leftSelectionSet := Execution.mergedFieldSelectionSet leftFields
                  let rightSelectionSet := Execution.mergedFieldSelectionSet rightFields
                  have hleftSelection :
                      (ReductionUnit.outputSelectionSet schema childUnits).Perm
                        leftSelectionSet := by
                    have hchildrenEq :=
                      RuntimeFieldBundle.reducedSelectionSet_eq_outputChildUnits
                        schema bundles (fun bundle hbundle =>
                          (hbundles bundle hbundle).reducedChildren)
                    have hperm := List.Perm.flatMap hleftFields
                      ExecutableField.selectionSet
                    rw [← hchildrenEq]
                    simpa [childUnits, leftSelectionSet,
                      RuntimeFieldBundle.reducedFields,
                      Execution.FieldGroups.mergedFieldSelectionSet_eq_flatMap] using hperm
                  have hrightSelection :
                      (ReductionUnit.inputSelectionSet childUnits).Perm
                        rightSelectionSet := by
                    have hchildrenEq :=
                      RuntimeFieldBundle.sourceSelectionSet_eq_inputChildUnits
                        bundles (fun bundle hbundle =>
                          (hbundles bundle hbundle).sourceChildren)
                    have hperm := List.Perm.flatMap hrightFields
                      ExecutableField.selectionSet
                    rw [← hchildrenEq]
                    simpa [childUnits, rightSelectionSet,
                      RuntimeFieldBundle.allSourceFields,
                      Execution.FieldGroups.mergedFieldSelectionSet_eq_flatMap] using hperm
                  have hchildApplicable : ReductionUnit.AllRuntimeApplicable schema
                      variableValues childRuntime childUnits := by
                    intro unit hunit
                    rcases List.mem_map.mp hunit with ⟨bundle, hbundle, rfl⟩
                    apply hchildren bundle hbundle fieldDefinition
                      (hlookupBundles bundle hbundle) childRuntime
                    · rw [← hnamed]
                      exact hinclude
                    · simp
                  have hchildReady :
                      NormalForm.selectionSetSemanticsReady schema childRuntime
                        rightSelectionSet := by
                    apply Algorithms.ExecutionUngroupedUncached.Eager.selectionSetSemanticsReady_mergedFieldSelectionSet
                    intro field hfield
                    exact boundary.fieldChildSemanticsReady hrightGroup hfield
                      fieldDefinition (hlookupAll field hfield) childRuntime
                      (by rw [← hnamed]; exact hinclude)
                  have hresponses : ∀ field, field ∈ rightFields ->
                      field.responseName = responseName :=
                    (collectFields_wellFormed schema variableValues boundary.parentType
                      (.object boundary.runtimeType boundary.ref) boundary.selectionSet)
                      (responseName, rightFields) (by
                        rw [← boundary.allSpecGroups_eq]
                        exact hrightGroup) |>.2
                  have hchildMerge : FieldMerge.fieldsInSetCanMerge schema childRuntime
                      rightSelectionSet := by
                    apply Algorithms.ExecutionUngroupedUncached.Eager.fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped
                      schema boundary.extractionParentType boundary.runtimeType
                      boundary.selectionSet
                      responseName rightFields boundary.fieldsCanMerge hresponses
                      (boundary.groupRuntimeScoped hrightGroup) childRuntime
                  have hchildObject : schema.objectType childRuntime :=
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
                      typeName childRuntime (List.contains_iff_mem.mp hinclude)
                  have hchildSelf :
                      Algorithms.ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies
                        schema childRuntime childRuntime :=
                    NormalForm.object_typeIncludesObjectBool_self schema hchildObject
                  let childGroups := collectFields schema variableValues childRuntime
                    (.object childRuntime childRef) rightSelectionSet
                  have hchildSelectionArgumentsNodup :
                      Execution.selectionSetArgumentsNodup rightSelectionSet := by
                    apply Algorithms.ExecutionUngroupedUncached.Eager.selectionSetArgumentsNodup_mergedFieldSelectionSet
                    intro field hfield
                    exact boundary.childrenArgumentsNodup field
                      (boundary.groupField_mem_collected hrightGroup hfield)
                  have hchildArgumentsAndChildrenNodup :=
                    Algorithms.ExecutionUngroupedUncached.Eager.collectFields_argumentsAndChildrenNodup
                      schema variableValues childRuntime (.object childRuntime childRef)
                      rightSelectionSet hchildSelectionArgumentsNodup
                  let childBoundary : ExecutionBoundary (ObjectRef := ObjectRef) schema
                      variableValues :=
                    {
                      extractionParentType := typeName
                      parentType := childRuntime
                      runtimeType := childRuntime
                      ref := childRef
                      selectionSet := rightSelectionSet
                      allSpecGroups := childGroups
                      allSpecGroups_eq := rfl
                      extractionPossible := hinclude
                      parentObject := hchildObject
                      parentRuntimeApplies := hchildSelf
                      semanticsReady := hchildReady
                      fieldsCanMerge := hchildMerge
                      argumentsNodup := hchildArgumentsAndChildrenNodup.1
                      childrenArgumentsNodup := hchildArgumentsAndChildrenNodup.2
                    }
                  have hchild := reductionUnits_execute_equivalent schema resolvers
                    variableValues hschema nextFuel childRuntime childRuntime childRef
                    childUnits leftSelectionSet rightSelectionSet hchildObject hchildSelf
                    hchildReady
                    (by simpa [childBoundary, childGroups] using
                      childBoundary.groupsFieldCompatible)
                    hchildArgumentsAndChildrenNodup.1
                    hchildArgumentsAndChildrenNodup.2
                    (by
                      intro childResponseName childFields hchildGroup
                      exact childBoundary.groupRuntimeScoped (by
                        simpa [childBoundary, childGroups] using hchildGroup))
                    hchildMerge hchildApplicable hleftSelection hrightSelection
                  have hcaught := selectionSetResultEquivalent_catchBubbleAsNull hchild
                  simpa [Execution.completeValue, hinclude, leftSelectionSet, rightSelectionSet,
                    Execution.executeSelectionSet, executeRootSelectionSet,
                    NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                    using hcaught
                · have hfalse :
                      schema.typeIncludesObjectBool typeName childRuntime = false := by
                    cases hvalue : schema.typeIncludesObjectBool typeName childRuntime
                    · rfl
                    · contradiction
                  exact responseValueResultEquivalent_of_eq (by
                    simp [Execution.completeValue, hfalse])
        | list inner =>
            subst fieldType
            cases hvalue : value with
            | list values =>
                subst value
                have hlist := completeValueListBundles_equivalent schema resolvers
                  variableValues hschema boundary nextFuel responseName bundles
                  leftFields rightFields inner values fieldDefinition hrightGroup
                  hleftFields hrightFields hlookupAll hnamed hbundles hchildren
                  hlookupBundles
                have hcaught :=
                  listResponseValueResultEquivalent_catchBubbleAsNull hlist
                simpa [Execution.completeValue] using hcaught
            | null =>
                exact responseValueResultEquivalent_of_eq (by simp [Execution.completeValue])
            | scalar scalarValue =>
                exact responseValueResultEquivalent_of_eq (by simp [Execution.completeValue])
            | object runtime ref =>
                exact responseValueResultEquivalent_of_eq (by simp [Execution.completeValue])
  termination_by (fuel, 1, sizeOf fieldType + sizeOf value)
  decreasing_by
    all_goals subst_vars
    all_goals
      first
      | apply Prod.Lex.left
        omega
      | apply Prod.Lex.right
        apply Prod.Lex.right
        simp_wf

  theorem completeValueListBundles_equivalent
      {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boundary
        : ReductionExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
      (fuel : Nat) (responseName : Name)
      (bundles : List RuntimeFieldBundle)
      (leftFields rightFields : List ExecutableField)
      (itemType : TypeRef) (values : List (ResolverValue ObjectRef))
      (fieldDefinition : FieldDefinition)
      (hrightGroup : (responseName, rightFields) ∈ boundary.allSpecGroups)
      (hleftFields : (bundles.map RuntimeFieldBundle.reducedField).Perm leftFields)
      (hrightFields : (bundles.flatMap RuntimeFieldBundle.sourceFields).Perm rightFields)
      (hlookupAll
        : ∀ field,
            field ∈ rightFields
            -> schema.lookupField field.parentType field.fieldName = some fieldDefinition)
      (hnamed : itemType.namedType = fieldDefinition.outputType.namedType)
      (hbundles : ∀ bundle, bundle ∈ bundles -> bundle.WellFormed schema)
      (hchildren
        : ∀ bundle,
            bundle ∈ bundles
            -> ∀ runtimeFieldDefinition,
                schema.lookupField boundary.runtimeType bundle.reducedField.fieldName
                  = some runtimeFieldDefinition
                -> ∀ childRuntimeType,
                    schema.typeIncludesObjectBool
                        runtimeFieldDefinition.outputType.namedType childRuntimeType
                      = true
                    -> bundle.ChildrenRuntimeApplicable schema variableValues
                        childRuntimeType)
      (hlookupBundles
        : ∀ bundle,
            bundle ∈ bundles
            -> schema.lookupField boundary.runtimeType bundle.reducedField.fieldName
                = some fieldDefinition)
      : ListResponseValueResultEquivalent
          (Execution.completeValueList schema resolvers variableValues fuel itemType
            leftFields values)
          (Execution.completeValueList schema resolvers variableValues fuel itemType
            rightFields values) := by
    cases values with
    | nil =>
        simp [Execution.completeValueList, ListResponseValueResultEquivalent,
          ResponseValue.canonicalList]
    | cons value rest =>
        rw [Execution.completeValueList, Execution.completeValueList]
        apply listResponseValueResultEquivalent_combine_cons
        · exact completeValueBundles_equivalent schema resolvers variableValues
            hschema boundary fuel responseName bundles leftFields rightFields itemType
            value fieldDefinition hrightGroup hleftFields hrightFields hlookupAll
            hnamed hbundles hchildren hlookupBundles
        · exact completeValueListBundles_equivalent schema resolvers variableValues
            hschema boundary fuel responseName bundles leftFields rightFields itemType
            rest fieldDefinition hrightGroup hleftFields hrightFields hlookupAll
            hnamed hbundles hchildren hlookupBundles
  termination_by (fuel, 2, sizeOf itemType + sizeOf values)
  decreasing_by
    all_goals
      apply Prod.Lex.right
      first
      | apply Prod.Lex.left
        omega
      | apply Prod.Lex.right
        simp_wf
        omega
end

end ConditionTree
end GraphQL
