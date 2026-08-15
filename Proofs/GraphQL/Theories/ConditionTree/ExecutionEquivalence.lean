import Proofs.GraphQL.Theories.ConditionTree.RuntimeExtraction
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection.StateInvariant
import Proofs.GraphQL.Execution.Fuel
import Proofs.GraphQL.Execution.SemanticEquivalence

/-! Recursive correspondence between total condition-tree and specification execution. -/

namespace GraphQL
namespace ConditionTree
namespace ExecutionEquivalence

open Execution
open Algorithms.ExecutionUngroupedUncached
open Algorithms.ExecutionUngroupedUncached.Eager
open NormalForm.GroundTypeNormalization.ReorderingSoundness
open RuntimeExtraction
open Execution.FieldGroups

-----------------------------------------------------------------------------------------
-- Response-depth and schema-aware fuel bounds
-----------------------------------------------------------------------------------------

theorem fieldDefinitionsExecutionCompletionFuel_mem
    {field : FieldDefinition} {fields : List FieldDefinition}
    (hfield : field ∈ fields)
    : typeRefExecutionCompletionFuel field.outputType
      ≤ fieldDefinitionsExecutionCompletionFuel fields := by
  induction fields with
  | nil => simp at hfield
  | cons head rest ih =>
      rcases List.mem_cons.mp hfield with rfl | hrest
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hrest) (Nat.le_max_right _ _)

theorem typeDefinitionsExecutionCompletionFuel_object_mem
    {objectType : ObjectType} {types : List TypeDefinition}
    (hobject : TypeDefinition.object objectType ∈ types)
    : fieldDefinitionsExecutionCompletionFuel objectType.fields
      ≤ typeDefinitionsExecutionCompletionFuel types := by
  induction types with
  | nil => simp at hobject
  | cons head rest ih =>
      rcases List.mem_cons.mp hobject with hhead | hrest
      · subst head
        exact Nat.le_max_left _ _
      · cases head <;>
          simp only [typeDefinitionsExecutionCompletionFuel]
        all_goals first
          | exact Nat.le_trans (ih hrest) (Nat.le_max_right _ _)
          | exact ih hrest

theorem typeDefinitionsExecutionCompletionFuel_interface_mem
    {interfaceType : InterfaceType} {types : List TypeDefinition}
    (hinterface : TypeDefinition.interface interfaceType ∈ types)
    : fieldDefinitionsExecutionCompletionFuel interfaceType.fields
      ≤ typeDefinitionsExecutionCompletionFuel types := by
  induction types with
  | nil => simp at hinterface
  | cons head rest ih =>
      rcases List.mem_cons.mp hinterface with hhead | hrest
      · subst head
        exact Nat.le_max_left _ _
      · cases head <;>
          simp only [typeDefinitionsExecutionCompletionFuel]
        all_goals first
          | exact Nat.le_trans (ih hrest) (Nat.le_max_right _ _)
          | exact ih hrest

theorem lookupField_executionCompletionFuel_le
    (schema : Schema) {parentType fieldName : Name}
    {fieldDefinition : FieldDefinition}
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    : typeRefExecutionCompletionFuel fieldDefinition.outputType
      ≤ typeDefinitionsExecutionCompletionFuel schema.types := by
  unfold Schema.lookupField at hlookup
  cases htype : schema.lookupType parentType with
  | none => simp [htype] at hlookup
  | some typeDefinition =>
      simp only [htype, Option.bind_eq_bind] at hlookup
      have htypeMem : typeDefinition ∈ schema.allTypes := by
        exact List.mem_of_find?_eq_some htype
      unfold Schema.allTypes at htypeMem
      rcases typeDefinition with scalar | scalar | objectType | interfaceType |
          unionType | enumType | inputObjectType
      all_goals simp only [TypeDefinition.fields?] at hlookup
      · cases hlookup
      · cases hlookup
      · have hfield : fieldDefinition ∈ objectType.fields :=
          List.mem_of_find?_eq_some hlookup
        have hobject : TypeDefinition.object objectType ∈ schema.types := by
          simpa [Schema.builtinScalarDefinitions] using htypeMem
        exact Nat.le_trans
          (fieldDefinitionsExecutionCompletionFuel_mem hfield)
          (typeDefinitionsExecutionCompletionFuel_object_mem hobject)
      · have hfield : fieldDefinition ∈ interfaceType.fields :=
          List.mem_of_find?_eq_some hlookup
        have hinterface : TypeDefinition.interface interfaceType ∈ schema.types := by
          simpa [Schema.builtinScalarDefinitions] using htypeMem
        exact Nat.le_trans
          (fieldDefinitionsExecutionCompletionFuel_mem hfield)
          (typeDefinitionsExecutionCompletionFuel_interface_mem hinterface)
      · cases hlookup
      · cases hlookup
      · cases hlookup

structure ExecutionBoundary {ObjectRef : Type}
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
  parentRuntimeApplies : ScopedParentRuntimeApplies schema runtimeType parentType
  semanticsReady : NormalForm.selectionSetSemanticsReady schema parentType selectionSet
  fieldsCanMerge : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
  argumentsNodup : CollectedGroupsArgumentsNodup allSpecGroups
  childrenArgumentsNodup
    : ∀ field,
        field ∈ collectedExecutableFields allSpecGroups
        -> selectionSetArgumentsNodup field.selectionSet

def GroupsSubset (groups allGroups : List (Name × List ExecutableField)) : Prop :=
  ∀ group, group ∈ groups -> group ∈ allGroups

theorem GroupsSubset.of_perm
    {groups reordered allGroups : List (Name × List ExecutableField)}
    (hsubset : GroupsSubset groups allGroups)
    (hperm : groups.Perm reordered)
    : GroupsSubset reordered allGroups := by
  intro group hgroup
  exact hsubset group (hperm.mem_iff.mpr hgroup)

theorem GroupsSubset.tail
    {group : Name × List ExecutableField}
    {groups allGroups : List (Name × List ExecutableField)}
    (hsubset : GroupsSubset (group :: groups) allGroups)
    : GroupsSubset groups allGroups := by
  intro candidate hcandidate
  exact hsubset candidate (by simp [hcandidate])

theorem ExecutionBoundary.fieldArgumentsNodup
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    {field : ExecutableField}
    (hfield : field ∈ collectedExecutableFields boundary.allSpecGroups)
    : (field.arguments.map Argument.name).Nodup := by
  rw [← RuntimeExtraction.flattenCollectedFields_eq_collectedExecutableFields] at hfield
  rcases (mem_flattenCollectedFields_iff boundary.allSpecGroups field).mp hfield with
    ⟨responseName, fields, hgroup, hfield⟩
  exact boundary.argumentsNodup responseName fields hgroup field hfield

theorem ExecutionBoundary.groupsFieldCompatible
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    : CollectedGroupsFieldValidationMergeCompatible boundary.allSpecGroups := by
  rw [boundary.allSpecGroups_eq]
  exact collectFields_fieldCompatible_of_canMerge_lookupValid schema variableValues
    boundary.parentType boundary.parentType boundary.runtimeType boundary.ref
    boundary.selectionSet boundary.fieldsCanMerge boundary.parentRuntimeApplies
    (NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady
      boundary.selectionSet boundary.semanticsReady)

theorem ExecutionBoundary.groupsSameParent
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    : CollectedGroupsSameResponseParent boundary.allSpecGroups := by
  rw [boundary.allSpecGroups_eq]
  exact collectFields_sameResponseParent schema variableValues boundary.parentType
    (.object boundary.runtimeType boundary.ref) boundary.selectionSet

theorem typeRefExecutionCompletionFuel_pos (fieldType : TypeRef)
    : 0 < typeRefExecutionCompletionFuel fieldType := by
  induction fieldType with
  | named name => simp [typeRefExecutionCompletionFuel]
  | list inner ih => simp [typeRefExecutionCompletionFuel]
  | nonNull inner ih => simpa [typeRefExecutionCompletionFuel] using ih

theorem typeRefExecutionCompletionFuel_inner_le
    (inner : TypeRef) (wrapper : TypeRef -> TypeRef)
    (hwrapper : wrapper = TypeRef.list ∨ wrapper = TypeRef.nonNull)
    : typeRefExecutionCompletionFuel inner
      ≤ typeRefExecutionCompletionFuel (wrapper inner) := by
  rcases hwrapper with rfl | rfl <;> simp [typeRefExecutionCompletionFuel]

theorem ExecutionBoundary.groupField_mem_collected
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    {responseName : Name} {fields : List ExecutableField}
    (hgroup : (responseName, fields) ∈ boundary.allSpecGroups)
    {field : ExecutableField} (hfield : field ∈ fields)
    : field ∈ collectedExecutableFields boundary.allSpecGroups := by
  rw [← RuntimeExtraction.flattenCollectedFields_eq_collectedExecutableFields]
  exact (mem_flattenCollectedFields_iff boundary.allSpecGroups field).mpr
    ⟨responseName, fields, hgroup, hfield⟩

theorem ExecutionBoundary.fieldLookup
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    {responseName : Name} {fields : List ExecutableField}
    (hgroup : (responseName, fields) ∈ boundary.allSpecGroups)
    {field : ExecutableField} (hfield : field ∈ fields)
    : ∃ fieldDefinition,
        schema.lookupField field.parentType field.fieldName = some fieldDefinition := by
  have hlookup :=
    collectFields_lookupValid_of_selectionSetSemanticsReady_object schema
      variableValues boundary.parentType boundary.runtimeType boundary.ref
      boundary.selectionSet boundary.parentObject boundary.parentRuntimeApplies
      boundary.semanticsReady
  rw [← boundary.allSpecGroups_eq] at hlookup
  rw [← RuntimeExtraction.flattenCollectedFields_eq_collectedExecutableFields] at hlookup
  have hparent : field.parentType = boundary.parentType := by
    have hgroupsParent : CollectedGroupsParent boundary.parentType
        boundary.allSpecGroups := by
      rw [boundary.allSpecGroups_eq]
      exact collectFields_parent schema variableValues boundary.parentType
        (.object boundary.runtimeType boundary.ref) boundary.selectionSet
    exact hgroupsParent responseName fields hgroup field hfield
  rw [hparent]
  exact hlookup field
      ((mem_flattenCollectedFields_iff boundary.allSpecGroups field).mpr
        ⟨responseName, fields, hgroup, hfield⟩)

theorem ExecutionBoundary.fieldChildSemanticsReady
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
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
    collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object schema
      variableValues boundary.parentType boundary.runtimeType boundary.ref
      boundary.selectionSet boundary.parentObject boundary.parentRuntimeApplies
      boundary.semanticsReady
  rw [← boundary.allSpecGroups_eq] at hready
  rw [← RuntimeExtraction.flattenCollectedFields_eq_collectedExecutableFields] at hready
  exact hready field
    ((mem_flattenCollectedFields_iff boundary.allSpecGroups field).mpr
      ⟨responseName, fields, hgroup, hfield⟩)
    fieldDefinition hlookup childRuntime hinclude

theorem ExecutionBoundary.groupRuntimeScoped
    {ObjectRef : Type} {schema : Schema} {variableValues : VariableValues}
    (boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
    {responseName : Name} {fields : List ExecutableField}
    (hgroup : (responseName, fields) ∈ boundary.allSpecGroups)
    : ExecutableFieldsRuntimeScopedBy schema boundary.runtimeType
        (FieldMerge.collectFields schema boundary.parentType boundary.selectionSet)
        fields := by
  have hscoped :=
    collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
      variableValues boundary.parentType boundary.parentType boundary.runtimeType
      boundary.ref boundary.selectionSet boundary.parentRuntimeApplies
      (NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady
        boundary.selectionSet boundary.semanticsReady)
  rw [← boundary.allSpecGroups_eq] at hscoped
  intro field hfield
  exact hscoped field (boundary.groupField_mem_collected hgroup hfield)

def valueCompletionFuelBound (schema : Schema) (depth : Nat) (fieldType : TypeRef)
    : Nat :=
  (depth - 1) * (typeDefinitionsExecutionCompletionFuel schema.types + 1)
  + typeRefExecutionCompletionFuel fieldType
  + 1

theorem valueCompletionFuelBound_le_after_field
    (schema : Schema) (depth completionFuel : Nat) (fieldType : TypeRef)
    (hdepth : 0 < depth)
    (htype
      : typeRefExecutionCompletionFuel fieldType
        ≤ typeDefinitionsExecutionCompletionFuel schema.types)
    (hfuel : responseDepthFuelBound schema depth ≤ completionFuel + 1)
    : valueCompletionFuelBound schema depth fieldType ≤ completionFuel := by
  let schemaFuel := typeDefinitionsExecutionCompletionFuel schema.types
  have hdepthEq : depth = (depth - 1) + 1 := by omega
  have hmul :
      depth * (schemaFuel + 1)
        = (depth - 1) * (schemaFuel + 1) + (schemaFuel + 1) := by
    calc
      depth * (schemaFuel + 1) = ((depth - 1) + 1) * (schemaFuel + 1) :=
        congrArg (fun value => value * (schemaFuel + 1)) hdepthEq
      _ = (depth - 1) * (schemaFuel + 1) + (schemaFuel + 1) := by
        simp [Nat.add_mul]
  have hmiddle :
      (depth - 1) * (schemaFuel + 1)
          + typeRefExecutionCompletionFuel fieldType + 1
        ≤ depth * (schemaFuel + 1) := by
    rw [hmul]
    omega
  exact Nat.le_trans hmiddle (by
    unfold responseDepthFuelBound at hfuel
    change depth * (schemaFuel + 1) + 1 ≤ completionFuel + 1 at hfuel
    omega)

theorem responseDepthFuelBound_le_of_value_named
    (schema : Schema) (depth fuel : Nat) (typeName : Name)
    (hvalue : valueCompletionFuelBound schema depth (.named typeName) ≤ fuel + 1)
    : responseDepthFuelBound schema (depth - 1) ≤ fuel := by
  unfold valueCompletionFuelBound typeRefExecutionCompletionFuel at hvalue
  unfold responseDepthFuelBound
  omega

theorem valueCompletionFuelBound_inner_list
    (schema : Schema) (depth fuel : Nat) (inner : TypeRef)
    (hvalue : valueCompletionFuelBound schema depth (.list inner) ≤ fuel + 1)
    : valueCompletionFuelBound schema depth inner ≤ fuel := by
  simp only [valueCompletionFuelBound, typeRefExecutionCompletionFuel] at hvalue ⊢
  omega

theorem valueCompletionFuelBound_inner_nonNull
    (schema : Schema) (depth : Nat) (inner : TypeRef)
    : valueCompletionFuelBound schema depth (.nonNull inner)
      = valueCompletionFuelBound schema depth inner := by
  simp [valueCompletionFuelBound, typeRefExecutionCompletionFuel]

-- Proof-facing wrapper matching the coercion-and-resolution view already used for the
-- specification executor.
theorem executeField_eq_coerceAndResolveFieldValue
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef)
    (responseName : Name) (field : ExecutableField) (fields : List ExecutableField)
    (fieldDefinition : FieldDefinition)
    (hlookup : schema.lookupField field.parentType field.fieldName = some fieldDefinition)
    : executeField schema resolvers variableValues source responseName (field :: fields)
      = match coerceAndResolveFieldValue schema resolvers variableValues fieldDefinition
                field.parentType field.fieldName field.arguments source with
        | none =>
            singleFieldResult responseName (handleFieldError fieldDefinition.outputType)
        | some resolved =>
            singleFieldResult responseName
              (completeValue schema resolvers variableValues
                fieldDefinition.outputType (field :: fields) resolved) := by
  simp only [executeField, hlookup]
  exact match_coerceArgumentValues_resolveFieldValue schema resolvers variableValues
    fieldDefinition field.parentType field.fieldName field.arguments source
    (singleFieldResult responseName (handleFieldError fieldDefinition.outputType))
    (fun resolved =>
      singleFieldResult responseName
        (completeValue schema resolvers variableValues fieldDefinition.outputType
          (field :: fields) resolved))

set_option maxRecDepth 10000 in
mutual
  theorem executeCollectedFields_equivalent
      {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
      (depth fuel : Nat)
      (leftGroups rightGroups : List (Name × List ExecutableField))
      (equivalent : RuntimeGroupsPermutationEquivalent leftGroups rightGroups)
      (rightSubset : GroupsSubset rightGroups boundary.allSpecGroups)
      (hdepth : RuntimeGroupsResponseDepthBound rightGroups depth)
      (hfuel : responseDepthFuelBound schema depth ≤ fuel)
      : SelectionSetResultEquivalent
          (executeCollectedFields schema resolvers variableValues
            (.object boundary.runtimeType boundary.ref) leftGroups)
          (Execution.executeCollectedFields schema resolvers variableValues fuel
            (.object boundary.runtimeType boundary.ref) rightGroups) := by
    cases hleftGroups : leftGroups with
    | nil =>
        subst leftGroups
        cases rightGroups with
        | nil =>
            apply selectionSetResultEquivalent_of_eq
            simp [executeCollectedFields, Execution.executeCollectedFields]
        | cons rightGroup rightTail =>
            have hkey : rightGroup.1 ∈ ((rightGroup :: rightTail).map Prod.fst) := by
              simp
            have : rightGroup.1 ∈ ([].map Prod.fst) :=
              (equivalent.keys rightGroup.1).mpr hkey
            simp at this
    | cons leftGroup leftTail =>
        subst leftGroups
        rcases leftGroup with ⟨responseName, leftFields⟩
        obtain ⟨rightFields, rightTail, hrightPerm, aligned⟩ :=
          equivalent.alignRightHead
        have alignedSubset :
            GroupsSubset ((responseName, rightFields) :: rightTail)
              boundary.allSpecGroups :=
          rightSubset.of_perm hrightPerm
        have alignedDepth :
            RuntimeGroupsResponseDepthBound
              ((responseName, rightFields) :: rightTail) depth := by
          intro field hfield
          exact hdepth field
            ((flatMap_snd_perm_of_perm hrightPerm).mem_iff.mpr
              hfield)
        have hrightGroup :
            (responseName, rightFields) ∈ boundary.allSpecGroups :=
          alignedSubset _ (by simp)
        have hleftNonempty : leftFields ≠ [] :=
          (aligned.leftWellFormed (responseName, leftFields) (by simp)).1
        have hrightNonempty : rightFields ≠ [] :=
          (aligned.rightWellFormed (responseName, rightFields) (by simp)).1
        cases hleftFields : leftFields with
        | nil => contradiction
        | cons leftHead leftRest =>
            subst leftFields
            cases hrightFields : rightFields with
            | nil => contradiction
            | cons rightHead rightRest =>
                subst rightFields
                have currentFieldCompatible :
                    CollectedGroupsFieldValidationMergeCompatible
                      ((responseName, rightHead :: rightRest) :: rightTail) := by
                  intro name fields hgroup
                  exact boundary.groupsFieldCompatible name fields
                    (alignedSubset (name, fields) hgroup)
                have currentSameParent :
                    CollectedGroupsSameResponseParent
                      ((responseName, rightHead :: rightRest) :: rightTail) := by
                  intro name fields hgroup
                  exact boundary.groupsSameParent name fields
                    (alignedSubset (name, fields) hgroup)
                have cross : RuntimeGroupsCrossCompatible
                    ((responseName, leftHead :: leftRest) :: leftTail)
                    ((responseName, rightHead :: rightRest) :: rightTail) :=
                  aligned.crossCompatible currentFieldCompatible currentSameParent
                have hleftHead :
                    leftHead ∈ flattenCollectedFields
                      ((responseName, leftHead :: leftRest) :: leftTail) := by
                  simp [flattenCollectedFields]
                have hrightHead :
                    rightHead ∈ flattenCollectedFields
                      ((responseName, rightHead :: rightRest) :: rightTail) := by
                  simp [flattenCollectedFields]
                have hleftResponse : leftHead.responseName = responseName :=
                  (aligned.leftWellFormed
                    (responseName, leftHead :: leftRest) (by simp)).2 leftHead (by simp)
                have hrightResponse : rightHead.responseName = responseName :=
                  (aligned.rightWellFormed
                    (responseName, rightHead :: rightRest) (by simp)).2 rightHead (by simp)
                rcases cross leftHead hleftHead rightHead hrightHead
                    (hleftResponse.trans hrightResponse.symm) with
                  ⟨hparent, hfieldName, harguments⟩
                have hdepthPositive : 0 < depth := by
                  have := alignedDepth rightHead hrightHead
                  omega
                cases fuel with
                | zero =>
                    simp [responseDepthFuelBound] at hfuel
                | succ completionFuel =>
                    have hlookupEq :
                        schema.lookupField leftHead.parentType leftHead.fieldName
                          = schema.lookupField rightHead.parentType rightHead.fieldName := by
                      rw [hparent, hfieldName]
                    cases hlookup
                          : schema.lookupField rightHead.parentType
                              rightHead.fieldName with
                    | none =>
                        have htail :=
                          executeCollectedFields_equivalent schema resolvers variableValues
                            hschema boundary depth (completionFuel + 1) leftTail rightTail
                            aligned.tails alignedSubset.tail
                            (by
                              intro field hfield
                              exact alignedDepth field (by
                                simp [hfield]))
                            hfuel
                        have hhead : ResponseValueResultEquivalent
                            (.error 1 : Result ResponseValue) (.error 1) := rfl
                        have hcombined :=
                          selectionSetResultEquivalent_combine_singleField_append
                            (responseName := responseName) hhead htail
                        have hcore : SelectionSetResultEquivalent
                            (executeCollectedFields schema resolvers variableValues
                              (.object boundary.runtimeType boundary.ref)
                              ((responseName, leftHead :: leftRest) :: leftTail))
                            (Execution.executeCollectedFields schema resolvers variableValues
                              (completionFuel + 1)
                              (.object boundary.runtimeType boundary.ref)
                              ((responseName, rightHead :: rightRest) :: rightTail)) := by
                          simpa [executeCollectedFields, executeField,
                            Execution.executeCollectedFields, Execution.executeField,
                            singleFieldResult, hlookupEq, hlookup]
                            using hcombined
                        have hreorder :=
                          executeCollectedFields_equivalent_of_perm schema resolvers
                            variableValues (completionFuel + 1)
                            (.object boundary.runtimeType boundary.ref)
                            hrightPerm equivalent.rightKeysNodup
                        exact selectionSetResultEquivalent_trans hcore
                          (selectionSetResultEquivalent_symm hreorder)
                    | some fieldDefinition =>
                        have hleftSpec : leftHead ∈
                            collectedExecutableFields boundary.allSpecGroups := by
                          have hleftRight : leftHead ∈ flattenCollectedFields
                              ((responseName, rightHead :: rightRest) :: rightTail) :=
                            aligned.fieldsPerm.mem_iff.mp hleftHead
                          rcases (mem_flattenCollectedFields_iff _ leftHead).mp
                              hleftRight with ⟨name, fields, hgroup, hfield⟩
                          exact collectedExecutableFields_mem_of_group_mem
                            (alignedSubset (name, fields) hgroup) hfield
                        have hrightSpec : rightHead ∈
                            collectedExecutableFields boundary.allSpecGroups :=
                          collectedExecutableFields_mem_of_group_mem hrightGroup (by simp)
                        have hleftLookup :
                            schema.lookupField leftHead.parentType leftHead.fieldName
                              = some fieldDefinition := by
                          rw [hlookupEq, hlookup]
                        have hcoercedArguments : ArgumentCoercionResult.equivalent
                            (coerceArgumentValues schema variableValues
                              fieldDefinition.arguments leftHead.arguments)
                            (coerceArgumentValues schema variableValues
                              fieldDefinition.arguments rightHead.arguments) :=
                          coerceArgumentValues_equivalent_of_equivalent schema
                            variableValues fieldDefinition.arguments
                            (boundary.fieldArgumentsNodup hleftSpec)
                            (boundary.fieldArgumentsNodup hrightSpec) harguments
                        have hresolveEq :
                            coerceAndResolveFieldValue schema resolvers variableValues
                                fieldDefinition leftHead.parentType leftHead.fieldName
                                leftHead.arguments
                                (.object boundary.runtimeType boundary.ref)
                              = coerceAndResolveFieldValue schema resolvers variableValues
                                fieldDefinition rightHead.parentType rightHead.fieldName
                                rightHead.arguments
                                (.object boundary.runtimeType boundary.ref) := by
                          unfold coerceAndResolveFieldValue
                          cases hleftCoerce : coerceArgumentValues schema variableValues
                                  fieldDefinition.arguments leftHead.arguments <;>
                            cases hrightCoerce : coerceArgumentValues schema variableValues
                                  fieldDefinition.arguments rightHead.arguments <;>
                            simp [hleftCoerce, hrightCoerce,
                              ArgumentCoercionResult.equivalent] at hcoercedArguments ⊢
                          rw [hparent, hfieldName]
                          exact resolvers.resolve_argumentsEquivalent _ _ _ _ _
                            hcoercedArguments
                        cases hresolve
                              : coerceAndResolveFieldValue schema resolvers variableValues
                                  fieldDefinition rightHead.parentType rightHead.fieldName
                                  rightHead.arguments
                                  (.object boundary.runtimeType boundary.ref) with
                        | none =>
                            have htail :=
                              executeCollectedFields_equivalent schema resolvers
                                variableValues hschema boundary depth
                                (completionFuel + 1) leftTail rightTail aligned.tails
                                alignedSubset.tail
                                (by
                                  intro field hfield
                                  exact alignedDepth field (by
                                    simp [hfield]))
                                hfuel
                            have hhead := responseValueResultEquivalent_of_eq
                              (left := handleFieldError fieldDefinition.outputType)
                              (right := handleFieldError fieldDefinition.outputType) rfl
                            have hcombined :=
                              selectionSetResultEquivalent_combine_singleField_append
                                (responseName := responseName) hhead htail
                            have hcore : SelectionSetResultEquivalent
                                (executeCollectedFields schema resolvers variableValues
                                  (.object boundary.runtimeType boundary.ref)
                                  ((responseName, leftHead :: leftRest) :: leftTail))
                                  (Execution.executeCollectedFields schema resolvers variableValues
                                    (completionFuel + 1)
                                    (.object boundary.runtimeType boundary.ref)
                                    ((responseName, rightHead :: rightRest) :: rightTail)) := by
                              simp only [executeCollectedFields,
                                Execution.executeCollectedFields]
                              rw [executeField_eq_coerceAndResolveFieldValue schema
                                resolvers variableValues
                                (.object boundary.runtimeType boundary.ref) responseName
                                leftHead leftRest fieldDefinition hleftLookup]
                              rw [Execution.executeField_succ_eq_coerceAndResolveFieldValue
                                schema resolvers variableValues completionFuel
                                (.object boundary.runtimeType boundary.ref) responseName
                                rightHead rightRest fieldDefinition hlookup]
                              rw [hresolveEq, hresolve]
                              exact hcombined
                            have hreorder :=
                              executeCollectedFields_equivalent_of_perm schema resolvers
                                variableValues (completionFuel + 1)
                                (.object boundary.runtimeType boundary.ref)
                                hrightPerm equivalent.rightKeysNodup
                            exact selectionSetResultEquivalent_trans hcore
                              (selectionSetResultEquivalent_symm hreorder)
                        | some resolved =>
                            have hlookupAll :
                                ∀ field,
                                  field ∈ rightHead :: rightRest
                                  -> schema.lookupField field.parentType field.fieldName
                                    = some fieldDefinition := by
                              intro field hfield
                              have hfieldResponse :=
                                (aligned.rightWellFormed
                                  (responseName, rightHead :: rightRest) (by simp)).2
                                  field hfield
                              have hsameField :=
                                currentFieldCompatible responseName
                                  (rightHead :: rightRest) (by simp) rightHead field
                                  (by simp) hfield
                                  (hrightResponse.trans hfieldResponse.symm)
                              have hsameParent :=
                                currentSameParent responseName (rightHead :: rightRest)
                                  (by simp) rightHead field (by simp) hfield
                                  (hrightResponse.trans hfieldResponse.symm)
                              rw [← hsameParent, ← hsameField.1]
                              exact hlookup
                            have htypeFuel :=
                              lookupField_executionCompletionFuel_le schema hlookup
                            have hcompletionFuel :=
                              valueCompletionFuelBound_le_after_field schema depth
                                completionFuel fieldDefinition.outputType hdepthPositive
                                htypeFuel hfuel
                            have hfieldsPerm := aligned.headFields
                            have hgroupDepth : ExecutableFieldsResponseDepthBound
                                (rightHead :: rightRest) depth := by
                              intro field hfield
                              apply alignedDepth field
                              exact (mem_flattenCollectedFields_iff _ field).mpr
                                ⟨responseName, rightHead :: rightRest, by simp,
                                  hfield⟩
                            have hcompletion :=
                              completeValue_equivalent schema resolvers variableValues
                                hschema boundary depth completionFuel responseName
                                (leftHead :: leftRest) (rightHead :: rightRest)
                                fieldDefinition.outputType resolved fieldDefinition
                                hrightGroup hfieldsPerm hgroupDepth hlookupAll rfl htypeFuel
                                hcompletionFuel
                            have htail :=
                              executeCollectedFields_equivalent schema resolvers
                                variableValues hschema boundary depth
                                (completionFuel + 1) leftTail rightTail aligned.tails
                                alignedSubset.tail
                                (by
                                  intro field hfield
                                  exact alignedDepth field (by
                                    simp [hfield]))
                                hfuel
                            have hcombined :=
                              selectionSetResultEquivalent_combine_singleField_append
                                (responseName := responseName) hcompletion htail
                            have hcore : SelectionSetResultEquivalent
                                (executeCollectedFields schema resolvers variableValues
                                  (.object boundary.runtimeType boundary.ref)
                                  ((responseName, leftHead :: leftRest) :: leftTail))
                                  (Execution.executeCollectedFields schema resolvers variableValues
                                    (completionFuel + 1)
                                    (.object boundary.runtimeType boundary.ref)
                                    ((responseName, rightHead :: rightRest) :: rightTail)) := by
                              simp only [executeCollectedFields,
                                Execution.executeCollectedFields]
                              rw [executeField_eq_coerceAndResolveFieldValue schema
                                resolvers variableValues
                                (.object boundary.runtimeType boundary.ref) responseName
                                leftHead leftRest fieldDefinition hleftLookup]
                              rw [Execution.executeField_succ_eq_coerceAndResolveFieldValue
                                schema resolvers variableValues completionFuel
                                (.object boundary.runtimeType boundary.ref) responseName
                                rightHead rightRest fieldDefinition hlookup]
                              rw [hresolveEq, hresolve]
                              exact hcombined
                            have hreorder :=
                              executeCollectedFields_equivalent_of_perm schema resolvers
                                variableValues (completionFuel + 1)
                                (.object boundary.runtimeType boundary.ref)
                                hrightPerm equivalent.rightKeysNodup
                            exact selectionSetResultEquivalent_trans hcore
                              (selectionSetResultEquivalent_symm hreorder)
  termination_by (depth, 4, sizeOf leftGroups)
  decreasing_by
    all_goals
      first
      | apply Prod.Lex.right
        apply Prod.Lex.right
        simp_wf
        simp [hleftGroups]
        omega
      | apply Prod.Lex.right
        apply Prod.Lex.left
        omega

  theorem completeValue_equivalent
      {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
      (depth fuel : Nat) (responseName : Name)
      (leftFields rightFields : List ExecutableField)
      (fieldType : TypeRef) (value : ResolverValue ObjectRef)
      (fieldDefinition : FieldDefinition)
      (hrightGroup : (responseName, rightFields) ∈ boundary.allSpecGroups)
      (hfieldsPerm : leftFields.Perm rightFields)
      (hdepth : ExecutableFieldsResponseDepthBound rightFields depth)
      (hlookupAll
        : ∀ field,
            field ∈ rightFields
            -> schema.lookupField field.parentType field.fieldName = some fieldDefinition)
      (hnamed : fieldType.namedType = fieldDefinition.outputType.namedType)
      (htypeFuel
        : typeRefExecutionCompletionFuel fieldType
          ≤ typeDefinitionsExecutionCompletionFuel schema.types)
      (hfuel : valueCompletionFuelBound schema depth fieldType ≤ fuel)
      : ResponseValueResultEquivalent
          (completeValue schema resolvers variableValues fieldType leftFields value)
          (Execution.completeValue schema resolvers variableValues fuel fieldType
            rightFields value) := by
    cases fuel with
    | zero =>
        have hpositive : 0 < valueCompletionFuelBound schema depth fieldType := by
          unfold valueCompletionFuelBound
          have := typeRefExecutionCompletionFuel_pos fieldType
          omega
        omega
    | succ nextFuel =>
        cases hfieldType : fieldType with
        | nonNull inner =>
            subst fieldType
            simp only [completeValue, Execution.completeValue]
            apply responseValueResultEquivalent_nonNullCompletion
            apply completeValue_equivalent schema resolvers variableValues hschema
              boundary depth (nextFuel + 1) responseName leftFields rightFields inner
              value fieldDefinition hrightGroup hfieldsPerm hdepth hlookupAll
            · exact hnamed
            · exact Nat.le_trans
                (typeRefExecutionCompletionFuel_inner_le inner TypeRef.nonNull
                  (Or.inr rfl)) htypeFuel
            · simpa [valueCompletionFuelBound_inner_nonNull] using hfuel
        | named typeName =>
            subst fieldType
            cases hvalueEq : value with
            | null =>
                subst value
                exact responseValueResultEquivalent_of_eq (by
                  simp [completeValue, Execution.completeValue])
            | scalar scalarValue =>
                subst value
                exact responseValueResultEquivalent_of_eq (by
                  simp [completeValue, Execution.completeValue])
            | list values =>
                subst value
                exact responseValueResultEquivalent_of_eq (by
                  simp [completeValue, Execution.completeValue])
            | object childRuntime childRef =>
                subst value
                cases hright : rightFields with
                | nil =>
                    have hnonempty :=
                      (NormalForm.GroundTypeNormalization.collectFields_wellFormed
                        schema variableValues boundary.parentType
                        (.object boundary.runtimeType boundary.ref)
                        boundary.selectionSet)
                        (responseName, rightFields) (by
                          rw [← boundary.allSpecGroups_eq]
                          exact hrightGroup) |>.1
                    exact False.elim (hnonempty hright)
                | cons rightHead rightRest =>
                    subst rightFields
                    cases hleft : leftFields with
                    | nil =>
                        have := hfieldsPerm.length_eq
                        simp [hleft] at this
                    | cons leftHead leftRest =>
                        subst leftFields
                        by_cases hinclude :
                            schema.typeIncludesObjectBool typeName childRuntime = true
                        · have hincludeDefinition :
                              schema.typeIncludesObjectBool
                                  fieldDefinition.outputType.namedType childRuntime
                                = true := by
                            rw [← hnamed]
                            exact hinclude
                          let rightSelectionSet :=
                            Execution.mergedFieldSelectionSet
                              (rightHead :: rightRest)
                          let leftSelectionSet :=
                            Execution.mergedFieldSelectionSet
                              (leftHead :: leftRest)
                          have hleftSelectionSet :
                              ConditionTree.mergedExecutableSelectionSet
                                  (leftHead :: leftRest)
                                = leftSelectionSet := by
                            dsimp only [leftSelectionSet]
                            rw [mergedFieldSelectionSet_eq_flatMap]
                            rfl
                          have hselectionPerm :
                              leftSelectionSet.Perm rightSelectionSet := by
                            exact mergedFieldSelectionSet_perm hfieldsPerm
                          have hchildReady :
                              NormalForm.selectionSetSemanticsReady schema childRuntime
                                rightSelectionSet := by
                            apply selectionSetSemanticsReady_mergedFieldSelectionSet
                            intro field hfield
                            exact boundary.fieldChildSemanticsReady hrightGroup hfield
                              fieldDefinition (hlookupAll field hfield) childRuntime
                              hincludeDefinition
                          have hresponses :
                              ∀ field, field ∈ rightHead :: rightRest
                                -> field.responseName = responseName :=
                            (NormalForm.GroundTypeNormalization.collectFields_wellFormed
                              schema variableValues boundary.parentType
                              (.object boundary.runtimeType boundary.ref)
                              boundary.selectionSet) -- rewritten below
                              (responseName, rightHead :: rightRest) (by
                                rw [← boundary.allSpecGroups_eq]
                                exact hrightGroup) |>.2
                          have hchildMerge :
                              FieldMerge.fieldsInSetCanMerge schema childRuntime
                                rightSelectionSet := by
                            apply fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped
                              schema boundary.parentType boundary.runtimeType
                              boundary.selectionSet responseName
                              (rightHead :: rightRest) boundary.fieldsCanMerge
                              hresponses
                              (boundary.groupRuntimeScoped hrightGroup) childRuntime
                          have hchildObject : schema.objectType childRuntime :=
                            SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                              hschema typeName childRuntime
                              (List.contains_iff_mem.mp hinclude)
                          have hchildSelf :
                              ScopedParentRuntimeApplies schema childRuntime
                                childRuntime :=
                            NormalForm.object_typeIncludesObjectBool_self schema
                              hchildObject
                          let childGroups :=
                            collectFields schema variableValues childRuntime
                              (.object childRuntime childRef) rightSelectionSet
                          have hchildSelectionArgumentsNodup :
                              selectionSetArgumentsNodup rightSelectionSet := by
                            apply selectionSetArgumentsNodup_mergedFieldSelectionSet
                            intro field hfield
                            exact boundary.childrenArgumentsNodup field
                              (boundary.groupField_mem_collected hrightGroup hfield)
                          have hchildArgumentsAndChildrenNodup :=
                            collectFields_argumentsAndChildrenNodup schema variableValues
                              childRuntime (.object childRuntime childRef)
                              rightSelectionSet hchildSelectionArgumentsNodup
                          let childBoundary :
                              ExecutionBoundary (ObjectRef := ObjectRef) schema
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
                              childrenArgumentsNodup :=
                                hchildArgumentsAndChildrenNodup.2
                            }
                          have hchildEquivalent :
                              RuntimeGroupsPermutationEquivalent
                                ((ofSelectionSetInScope schema typeName []
                                  leftSelectionSet).collectRuntimeFieldGroups
                                    variableValues childRuntime childRuntime)
                                childGroups := by
                            exact
                              extracted_runtimeGroups_permutationEquivalent_toPermutedSelectionSet
                                schema typeName []
                                hselectionPerm variableValues childRuntime childRuntime
                                childRef rfl hinclude
                          have hchildDepthSelection :
                              selectionSetResponseDepth rightSelectionSet
                                ≤ depth - 1 := by
                            dsimp only [rightSelectionSet]
                            rw [mergedFieldSelectionSet_eq_flatMap]
                            apply selectionSetResponseDepth_flatMap_le
                              (rightHead :: rightRest) (depth - 1)
                            intro field hfield
                            have hfieldDepth := hdepth field hfield
                            omega
                          have hchildDepth : RuntimeGroupsResponseDepthBound
                              childGroups (depth - 1) := by
                            intro field hfield
                            exact Nat.le_trans
                              (collectFields_responseDepth_bound schema variableValues
                                childRuntime (.object childRuntime childRef)
                                rightSelectionSet field hfield)
                              hchildDepthSelection
                          have hchildFuel :
                              responseDepthFuelBound schema (depth - 1)
                                ≤ nextFuel :=
                            responseDepthFuelBound_le_of_value_named schema depth
                              nextFuel typeName hfuel
                          have hchild :=
                            executeCollectedFields_equivalent schema resolvers
                              variableValues hschema childBoundary (depth - 1) nextFuel
                              ((ofSelectionSetInScope schema typeName []
                                leftSelectionSet).collectRuntimeFieldGroups
                                  variableValues childRuntime childRuntime)
                              childGroups hchildEquivalent (by
                                intro group hgroup
                                exact hgroup) hchildDepth hchildFuel
                          have hcaught :=
                            selectionSetResultEquivalent_catchBubbleAsNull hchild
                          rw [completeValue.eq_5, Execution.completeValue]
                          simp only [hinclude, if_true]
                          rw [executeSelectionSet.eq_1, hleftSelectionSet]
                          simpa [childBoundary, childGroups, leftSelectionSet,
                            ofSelectionSet,
                            rightSelectionSet,
                            NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                            using hcaught
                        · have hfalse :
                              schema.typeIncludesObjectBool typeName childRuntime = false := by
                            cases hvalue :
                                schema.typeIncludesObjectBool typeName childRuntime
                            · rfl
                            · contradiction
                          exact responseValueResultEquivalent_of_eq (by
                            simp [completeValue, Execution.completeValue,
                              hfalse])
        | list inner =>
            subst fieldType
            cases hvalueEq : value with
            | list values =>
                subst value
                have hvalues :=
                  completeValueList_equivalent schema resolvers variableValues
                    hschema boundary depth nextFuel responseName leftFields rightFields
                    inner values fieldDefinition hrightGroup hfieldsPerm hdepth
                    hlookupAll hnamed
                    (Nat.le_trans
                      (typeRefExecutionCompletionFuel_inner_le inner TypeRef.list
                        (Or.inl rfl)) htypeFuel)
                    (valueCompletionFuelBound_inner_list schema depth nextFuel
                      inner hfuel)
                have hcaught :=
                  listResponseValueResultEquivalent_catchBubbleAsNull hvalues
                simpa [completeValue, Execution.completeValue] using hcaught
            | null =>
                subst value
                exact responseValueResultEquivalent_of_eq (by
                  simp [completeValue, Execution.completeValue])
            | scalar value =>
                exact responseValueResultEquivalent_of_eq (by
                  simp [completeValue, Execution.completeValue])
            | object runtime ref =>
                subst value
                exact responseValueResultEquivalent_of_eq (by
                  simp [completeValue, Execution.completeValue])
  termination_by (depth, 2, sizeOf fieldType + sizeOf value)
  decreasing_by
    all_goals
      first
      | apply Prod.Lex.left
        have := hdepth rightHead (by simp)
        omega
      | apply Prod.Lex.right
        apply Prod.Lex.right
        simp_wf
        simp [hfieldType] <;> omega
      | apply Prod.Lex.right
        apply Prod.Lex.left
        omega

  theorem completeValueList_equivalent
      {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema variableValues)
      (depth fuel : Nat) (responseName : Name)
      (leftFields rightFields : List ExecutableField)
      (itemType : TypeRef) (values : List (ResolverValue ObjectRef))
      (fieldDefinition : FieldDefinition)
      (hrightGroup : (responseName, rightFields) ∈ boundary.allSpecGroups)
      (hfieldsPerm : leftFields.Perm rightFields)
      (hdepth : ExecutableFieldsResponseDepthBound rightFields depth)
      (hlookupAll
        : ∀ field,
            field ∈ rightFields
            -> schema.lookupField field.parentType field.fieldName = some fieldDefinition)
      (hnamed : itemType.namedType = fieldDefinition.outputType.namedType)
      (htypeFuel
        : typeRefExecutionCompletionFuel itemType
          ≤ typeDefinitionsExecutionCompletionFuel schema.types)
      (hfuel : valueCompletionFuelBound schema depth itemType ≤ fuel)
      : ListResponseValueResultEquivalent
          (completeValueList schema resolvers variableValues itemType leftFields values)
          (Execution.completeValueList schema resolvers variableValues fuel itemType
            rightFields values) := by
    cases values with
    | nil =>
        simp [completeValueList, Execution.completeValueList,
          ListResponseValueResultEquivalent]
    | cons value rest =>
        rw [completeValueList, Execution.completeValueList]
        apply listResponseValueResultEquivalent_combine_cons
        · exact completeValue_equivalent schema resolvers variableValues hschema
            boundary depth fuel responseName leftFields rightFields itemType value
            fieldDefinition hrightGroup hfieldsPerm hdepth hlookupAll hnamed htypeFuel
            hfuel
        · exact completeValueList_equivalent schema resolvers variableValues
            hschema boundary depth fuel responseName leftFields rightFields itemType
            rest fieldDefinition hrightGroup hfieldsPerm hdepth hlookupAll hnamed
            htypeFuel hfuel
  termination_by (depth, 2, sizeOf itemType + sizeOf values)
  decreasing_by
    all_goals
      apply Prod.Lex.right
      apply Prod.Lex.right
      simp_wf
      omega
end

theorem execution_equivalent_of_sufficient_fuel
    (schema : Schema) (operation : Operation) (fuel : Nat)
    (hfuel
      : responseDepthFuelBound schema (selectionSetResponseDepth operation.selectionSet)
        ≤ fuel)
    : ExecutionEquivalentAtFuel schema operation fuel := by
  intro ObjectRef resolvers variableValues source hschema hoperation
  change Response.semanticEquivalent
    (executeQuery schema resolvers variableValues operation source)
    (Execution.executeQueryWithFuel schema resolvers variableValues operation fuel source)
  cases hroot : rootSourceAppliesBool schema operation source with
  | false =>
      simp [executeQuery, Execution.executeQueryWithFuel, hroot,
        Response.semanticEquivalent, ResponseValue.semanticEquivalent,
        ResponseValue.canonical]
  | true =>
      obtain ⟨runtimeType, ref, rfl, hpossible⟩ :=
        NormalForm.GroundTypeNormalization.rootSourceAppliesBool_true_object
          schema operation source hroot
      let coercedVariableValues :=
        coerceVariableValues operation variableValues
      let specGroups :=
        collectFields schema coercedVariableValues (operation.rootType schema)
          (.object runtimeType ref) operation.selectionSet
      have hrootSelectionArgumentsNodup :
          selectionSetArgumentsNodup operation.selectionSet :=
        Eager.selectionSetArgumentsNodup_of_selectionSetValid
          (Validation.operationDefinitionValid_selectionSetValid hoperation)
      have hrootArgumentsAndChildrenNodup :=
        collectFields_argumentsAndChildrenNodup schema coercedVariableValues
          (operation.rootType schema) (.object runtimeType ref)
          operation.selectionSet hrootSelectionArgumentsNodup
      let boundary : ExecutionBoundary (ObjectRef := ObjectRef) schema
          coercedVariableValues :=
        {
          extractionParentType := operation.rootType schema
          parentType := operation.rootType schema
          runtimeType := runtimeType
          ref := ref
          selectionSet := operation.selectionSet
          allSpecGroups := specGroups
          allSpecGroups_eq := rfl
          extractionPossible := by
            simpa [Schema.typeIncludesObjectBool] using hpossible
          parentObject :=
            NormalForm.CompleteNormalization.operation_root_object_of_valid
              hschema hoperation
          parentRuntimeApplies := by
            simpa [ScopedParentRuntimeApplies] using hpossible
          semanticsReady :=
            NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
              hschema hoperation
          fieldsCanMerge :=
            Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
          argumentsNodup := hrootArgumentsAndChildrenNodup.1
          childrenArgumentsNodup := hrootArgumentsAndChildrenNodup.2
        }
      have hequivalent :
          RuntimeGroupsPermutationEquivalent
            ((ofOperation schema operation).collectRuntimeFieldGroups
              coercedVariableValues (operation.rootType schema) runtimeType)
            specGroups := by
        simpa [ofOperation, ofSelectionSet, specGroups] using
          (extracted_runtimeGroups_permutationEquivalent_toPermutedSelectionSet
            schema (operation.rootType schema) [] (List.Perm.refl _)
            coercedVariableValues (operation.rootType schema) runtimeType ref rfl
            (by simpa [Schema.typeIncludesObjectBool] using hpossible))
      have hdepth : RuntimeGroupsResponseDepthBound specGroups
          (selectionSetResponseDepth operation.selectionSet) := by
        simpa [specGroups] using
          (collectFields_responseDepth_bound schema coercedVariableValues
            (operation.rootType schema) (.object runtimeType ref)
            operation.selectionSet)
      have hresult :=
        executeCollectedFields_equivalent schema resolvers coercedVariableValues
          hschema boundary (selectionSetResponseDepth operation.selectionSet)
          fuel
          ((ofOperation schema operation).collectRuntimeFieldGroups
            coercedVariableValues (operation.rootType schema) runtimeType)
          specGroups hequivalent (by
            intro group hgroup
            exact hgroup) hdepth hfuel
      have hresponse := responseEquivalent_of_selectionSetResultEquivalent hresult
      simpa [executeQuery, Execution.executeQueryWithFuel, hroot,
        Execution.executeRootSelectionSet, executeSelectionSet.eq_1, ofOperation,
        ofSelectionSet, coercedVariableValues,
        specGroups, boundary] using hresponse

theorem execution_equivalent (schema : Schema) (operation : Operation)
    : ExecutionEquivalent schema operation := by
  intro ObjectRef resolvers variableValues source hschema hoperation
  change Response.semanticEquivalent
    (executeQuery schema resolvers variableValues operation source)
    (Execution.executeQuery schema resolvers variableValues operation source)
  have hequivalent :=
    execution_equivalent_of_sufficient_fuel schema operation
      (executeQueryFuelBound schema operation)
      (Execution.doesNotExhaustFuel schema operation)
      ObjectRef resolvers variableValues source hschema hoperation
  change Response.semanticEquivalent
    (executeQuery schema resolvers variableValues operation source)
    (Execution.executeQueryWithFuel schema resolvers variableValues operation
      (executeQueryFuelBound schema operation) source) at hequivalent
  simpa [Execution.executeQuery] using hequivalent

end ExecutionEquivalence
end ConditionTree
end GraphQL
