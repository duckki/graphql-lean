import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.QueryInclusion.Execution
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Variables
import Proofs.GraphQL.Theories.ExecutionReadiness

/-! Error-free annotated execution for resolver values that conform to field types. -/

namespace GraphQL
namespace QueryInclusion

open Execution.FieldGroups

open Execution AnnotatedExecution
open SelectionConditions
open Algorithms.ExecutionUngroupedUncached
open Algorithms.ExecutionUngroupedUncached.Eager

private theorem named_composite_of_typeIncludesObjectBool
    (schema : Schema) (typeName objectName : Name)
    (hincludes : schema.typeIncludesObjectBool typeName objectName = true)
    : (TypeRef.named typeName).isCompositeBool schema = true := by
  unfold Schema.typeIncludesObjectBool Schema.getPossibleTypes at hincludes
  unfold TypeRef.isCompositeBool TypeRef.namedType
  cases hlookup : schema.lookupType typeName with
  | none => simp [hlookup] at hincludes
  | some typeDefinition =>
      cases typeDefinition <;> simp [hlookup] at hincludes ⊢

mutual
  def resolverValueSupported (schema : Schema)
      : TypeRef -> ResolverValue ObjectRef -> Prop
    | .named typeName, .scalar _value =>
        (TypeRef.named typeName).isCompositeBool schema = false
    | .named typeName, .object runtimeType _ref =>
        schema.typeIncludesObjectBool typeName runtimeType = true
    | .list inner, .list values =>
        resolverValuesSupported schema inner values
    | .nonNull inner, value => resolverValueSupported schema inner value
    | _, _ => False

  def resolverValuesSupported (schema : Schema) (itemType : TypeRef)
      : List (ResolverValue ObjectRef) -> Prop
    | [] => True
    | value :: rest =>
        resolverValueSupported schema itemType value
        ∧ resolverValuesSupported schema itemType rest
end

def ResolversSupported (schema : Schema) (resolvers : Resolvers ObjectRef) : Prop :=
  ∀ parentType fieldName arguments source definition,
    schema.lookupField parentType fieldName = some definition
    -> (definition.outputType.isCompositeBool schema = true
        -> schema.getPossibleTypes definition.outputType.namedType ≠ [])
    -> ∃ value,
        resolvers.resolve parentType fieldName arguments source = some value
        ∧ resolverValueSupported schema definition.outputType value

def executableFieldReady (schema : Schema) (field : ExecutableField) : Prop :=
  ∃ definition,
    schema.lookupField field.parentType field.fieldName = some definition
    ∧ (∀ runtimeType,
        schema.typeIncludesObjectBool definition.outputType.namedType runtimeType = true
        -> NormalForm.selectionSetSemanticsReady schema runtimeType field.selectionSet)
    ∧ (definition.outputType.isCompositeBool schema = true
        -> schema.getPossibleTypes definition.outputType.namedType ≠ []
            ∧ ∀ runtimeType,
                schema.typeIncludesObjectBool definition.outputType.namedType runtimeType
                  = true
                -> selectionSetCompositeFieldTypesInhabited schema runtimeType
                    field.selectionSet)

def executableFieldsSameResolver (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.parentType = later.parentType
        ∧ first.fieldName = later.fieldName
        ∧ Argument.argumentsEquivalent first.arguments later.arguments

def executableFieldsReady (schema : Schema) (fields : List ExecutableField) : Prop :=
  fields ≠ []
  ∧ (∀ field, field ∈ fields -> executableFieldReady schema field)
  ∧ executableFieldsSameResolver fields
  ∧ ∀ objectType,
      FieldMerge.fieldsInSetCanMerge schema objectType (mergedFieldSelectionSet fields)

def completionFieldsReady (schema : Schema) (fieldType : TypeRef)
    (fields : List ExecutableField)
    : Prop :=
  executableFieldsReady schema fields
  ∧ ∃ field definition,
      field ∈ fields
      ∧ schema.lookupField field.parentType field.fieldName = some definition
      ∧ fieldType.namedType = definition.outputType.namedType

def executableGroupsReady (schema : Schema) (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups -> executableFieldsReady schema fields

def executableFieldArgumentCoercionReady (schema : Schema)
    (variableValues : VariableValues) (field : ExecutableField)
    : Prop :=
  ∃ definition,
    schema.lookupField field.parentType field.fieldName = some definition
    ∧ (coerceArgumentValues schema variableValues definition.arguments
        field.arguments).isSuccess
      = true
    ∧ ∀ runtimeType,
        schema.typeIncludesObjectBool definition.outputType.namedType runtimeType = true
        -> selectionSetArgumentsCoercible schema variableValues runtimeType
            field.selectionSet

def executableFieldsArgumentCoercionReady (schema : Schema)
    (variableValues : VariableValues) (fields : List ExecutableField)
    : Prop :=
  ∀ field,
    field ∈ fields -> executableFieldArgumentCoercionReady schema variableValues field

def executableGroupsArgumentCoercionReady (schema : Schema)
    (variableValues : VariableValues)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> executableFieldsArgumentCoercionReady schema variableValues fields

def executableFieldsExecutionReady (schema : Schema)
    (variableValues : VariableValues) (fields : List ExecutableField)
    : Prop :=
  executableFieldsReady schema fields
  ∧ executableFieldsArgumentCoercionReady schema variableValues fields

def completionFieldsExecutionReady (schema : Schema)
    (variableValues : VariableValues) (fieldType : TypeRef)
    (fields : List ExecutableField)
    : Prop :=
  completionFieldsReady schema fieldType fields
  ∧ executableFieldsArgumentCoercionReady schema variableValues fields

def executableGroupsExecutionReady (schema : Schema)
    (variableValues : VariableValues)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  executableGroupsReady schema groups
  ∧ executableGroupsArgumentCoercionReady schema variableValues groups

def executableGroupsDepthBound (groups : List (Name × List ExecutableField)) (depth : Nat)
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> ∀ field, field ∈ fields -> selectionSetResponseDepth field.selectionSet + 1 ≤ depth

private theorem executableGroupsDepthBound_of_runtime
    {groups : List (Name × List ExecutableField)} {depth : Nat}
    (hdepth : RuntimeGroupsResponseDepthBound groups depth)
    : executableGroupsDepthBound groups depth := by
  intro responseName fields hgroup field hfield
  apply hdepth field
  rw [← Execution.FieldGroups.flattenCollectedFields_eq_flatMap_snd]
  exact (mem_flattenCollectedFields_iff groups field).mpr
    ⟨responseName, fields, hgroup, hfield⟩

private theorem collectFlatFields_field_compositeType_inhabited
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (ref : ObjectRef) (selectionSet : List Selection)
    (hinhabited : selectionSetCompositeFieldTypesInhabited schema parentType selectionSet)
    (field : ExecutableField)
    (hfield
      : field
        ∈ collectFlatFields schema variableValues parentType
            (.object parentType ref) selectionSet)
    : ∀ definition,
        schema.lookupField field.parentType field.fieldName = some definition
        -> definition.outputType.isCompositeBool schema = true
        -> schema.getPossibleTypes definition.outputType.namedType ≠ []
            ∧ ∀ runtimeType,
                schema.typeIncludesObjectBool definition.outputType.namedType runtimeType
                  = true
                -> selectionSetCompositeFieldTypesInhabited schema runtimeType
                    field.selectionSet := by
  unfold selectionSetCompositeFieldTypesInhabited at hinhabited
  cases selectionSet with
  | nil => simp [collectFlatFields] at hfield
  | cons selection rest =>
      have hrestInhabited :
          selectionSetCompositeFieldTypesInhabited schema parentType rest := by
        unfold selectionSetCompositeFieldTypesInhabited
        intro candidate hcandidate
        exact hinhabited candidate (by simp [hcandidate])
      simp only [collectFlatFields, List.mem_append] at hfield
      rcases hfield with hhead | hrest
      · have hselection := hinhabited selection (by simp)
        cases selection with
        | field responseName fieldName arguments directives childSelectionSet =>
            cases hdirectives :
                selectionDirectivesAllowBool variableValues directives <;>
              simp [collectFlatSelection, hdirectives] at hhead
            subst field
            simpa [selectionCompositeFieldTypesInhabited] using hselection
        | inlineFragment typeCondition directives childSelectionSet =>
            cases typeCondition with
            | none =>
                cases hdirectives :
                    selectionDirectivesAllowBool variableValues directives <;>
                  simp [collectFlatSelection, hdirectives] at hhead
                simp only [selectionCompositeFieldTypesInhabited] at hselection
                exact collectFlatFields_field_compositeType_inhabited schema
                  variableValues parentType ref childSelectionSet hselection field hhead
            | some typeName =>
                cases hdirectives :
                    selectionDirectivesAllowBool variableValues directives <;>
                  simp [collectFlatSelection, hdirectives] at hhead
                have happly :
                    schema.typeIncludesObjectBool typeName parentType = true := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using hhead.1
                have hhead' := hhead.2
                simp only [selectionCompositeFieldTypesInhabited] at hselection
                exact collectFlatFields_field_compositeType_inhabited schema
                  variableValues parentType ref childSelectionSet
                  (hselection happly) field hhead'
      · exact collectFlatFields_field_compositeType_inhabited schema variableValues
          parentType ref rest hrestInhabited field hrest
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    try subst selectionSet
    try subst selection
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    first
    | cases selection <;> simp [Selection.size] <;> omega
    | omega

private theorem collectFlatFields_field_argumentCoercionReady
    (schema : Schema) (variableValues : VariableValues)
    (sourceRuntimeType parentType : Name) (ref : ObjectRef)
    (selectionSet : List Selection)
    (hsourceType : sourceRuntimeType = parentType)
    (hready
      : selectionSetArgumentsCoercible schema variableValues parentType selectionSet)
    (field : ExecutableField)
    (hfield
      : field
        ∈ collectFlatFields schema variableValues parentType
            (.object sourceRuntimeType ref) selectionSet)
    : ∀ definition,
        schema.lookupField field.parentType field.fieldName = some definition
        -> (coerceArgumentValues schema variableValues definition.arguments
                field.arguments).isSuccess
              = true
            ∧ ∀ runtimeType,
                schema.typeIncludesObjectBool definition.outputType.namedType runtimeType
                  = true
                -> selectionSetArgumentsCoercible schema variableValues runtimeType
                    field.selectionSet := by
  cases selectionSet with
  | nil => simp [collectFlatFields] at hfield
  | cons selection rest =>
      have hheadReady := hready.1
      have hrestReady := hready.2
      simp only [collectFlatFields, List.mem_append] at hfield
      rcases hfield with hhead | hrest
      · cases selection with
        | field responseName fieldName arguments directives childSelectionSet =>
            cases hdirectives :
                selectionDirectivesAllowBool variableValues directives <;>
              simp [collectFlatSelection, hdirectives] at hhead
            subst field
            exact hheadReady hdirectives
        | inlineFragment typeCondition directives childSelectionSet =>
            cases typeCondition with
            | none =>
                cases hdirectives :
                    selectionDirectivesAllowBool variableValues directives <;>
                  simp [collectFlatSelection, hdirectives] at hhead
                exact collectFlatFields_field_argumentCoercionReady schema
                  variableValues sourceRuntimeType parentType ref childSelectionSet
                  hsourceType (hheadReady hdirectives trivial) field hhead
            | some typeName =>
                cases hdirectives :
                    selectionDirectivesAllowBool variableValues directives <;>
                  simp [collectFlatSelection, hdirectives] at hhead
                exact collectFlatFields_field_argumentCoercionReady schema
                  variableValues sourceRuntimeType parentType ref childSelectionSet
                  hsourceType
                  (hheadReady hdirectives (by
                    simpa [hsourceType, doesFragmentTypeApplyBool,
                      runtimeObjectType?] using hhead.1))
                  field hhead.2
      · exact collectFlatFields_field_argumentCoercionReady schema variableValues
          sourceRuntimeType parentType ref rest hsourceType hrestReady field hrest
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    first
    | cases selection <;> simp [Selection.size] <;> omega
    | omega

theorem executableGroupsReady_collectFields
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (ref : ObjectRef) (selectionSet : List Selection)
    (hobject : schema.objectType parentType)
    (hready : NormalForm.selectionSetSemanticsReady schema parentType selectionSet)
    (hinhabited : selectionSetCompositeFieldTypesInhabited schema parentType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    : executableGroupsReady schema
        (collectFields schema variableValues parentType (.object parentType ref)
          selectionSet) := by
  let groups :=
    collectFields schema variableValues parentType (.object parentType ref) selectionSet
  have hself : ScopedParentRuntimeApplies schema parentType parentType :=
    NormalForm.object_typeIncludesObjectBool_self schema hobject
  have hnonempty : CollectedGroupsFieldsNonempty groups := by
    exact collectFields_fieldsNonempty schema variableValues parentType
      (.object parentType ref) selectionSet
  have hparents : CollectedGroupsParent parentType groups := by
    exact collectFields_parent schema variableValues parentType
      (.object parentType ref) selectionSet
  have hlookup :=
    collectFields_lookupValid_of_selectionSetSemanticsReady_object schema
      variableValues parentType parentType ref selectionSet hobject hself hready
  have hchild :=
    collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object schema
      variableValues parentType parentType ref selectionSet hobject hself hready
  have hresponses : CollectedGroupsResponseName groups := by
    exact collectFields_responseName schema variableValues parentType
      (.object parentType ref) selectionSet
  have hcompatible : CollectedGroupsFieldValidationMergeCompatible groups := by
    dsimp only [groups]
    exact collectFields_fieldCompatible_of_canMerge_lookupValid_object schema
      variableValues parentType parentType parentType ref selectionSet hmerge hself
      (NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
        hready)
  have hscoped :
      ExecutableFieldsRuntimeScopedBy schema parentType
        (FieldMerge.collectFields schema parentType selectionSet)
        (collectedExecutableFields groups) := by
    dsimp only [groups]
    exact collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
      variableValues parentType parentType parentType ref selectionSet hself
      (NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
        hready)
  intro responseName fields hgroup
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hnonempty responseName fields hgroup
  · intro field hfield
    have hparent : field.parentType = parentType :=
      hparents responseName fields hgroup field hfield
    have hflat : field ∈ collectedExecutableFields groups :=
      collectedExecutableFields_mem_of_group_mem hgroup hfield
    rcases hlookup field hflat with ⟨definition, hdefinition⟩
    have hfieldFlat :
        field ∈ collectFlatFields schema variableValues parentType
          (.object parentType ref) selectionSet :=
      (collectFlatFields_mem_collectFields schema variableValues parentType
        (.object parentType ref) selectionSet field).mpr (by
          rw [flattenCollectedFields_eq_collectedExecutableFields]
          exact hflat)
    refine ⟨definition, ?_, ?_, ?_⟩
    · simpa [hparent] using hdefinition
    · intro runtimeType hincludes
      exact hchild field hflat definition (by simpa [hparent] using hdefinition)
        runtimeType hincludes
    · exact collectFlatFields_field_compositeType_inhabited schema variableValues
        parentType ref selectionSet hinhabited field hfieldFlat definition
        (by simpa [hparent] using hdefinition)
  · intro first later hfirst hlater
    have hparent : first.parentType = later.parentType := by
      rw [hparents responseName fields hgroup first hfirst,
        hparents responseName fields hgroup later hlater]
    have hresponse : first.responseName = later.responseName := by
      rw [hresponses responseName fields hgroup first hfirst,
        hresponses responseName fields hgroup later hlater]
    exact ⟨hparent,
      hcompatible responseName fields hgroup first later hfirst hlater hresponse⟩
  · intro objectType
    apply fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped schema
      parentType parentType selectionSet responseName fields hmerge
    · exact hresponses responseName fields hgroup
    · intro field hfield
      exact hscoped field
        (collectedExecutableFields_mem_of_group_mem hgroup hfield)

theorem executableGroupsArgumentCoercionReady_collectFields
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (ref : ObjectRef) (selectionSet : List Selection)
    (hobject : schema.objectType parentType)
    (hready : NormalForm.selectionSetSemanticsReady schema parentType selectionSet)
    (hcoercion
      : selectionSetArgumentsCoercible schema variableValues parentType selectionSet)
    : executableGroupsArgumentCoercionReady schema variableValues
        (collectFields schema variableValues parentType (.object parentType ref)
          selectionSet) := by
  let groups :=
    collectFields schema variableValues parentType (.object parentType ref) selectionSet
  have hself : ScopedParentRuntimeApplies schema parentType parentType :=
    NormalForm.object_typeIncludesObjectBool_self schema hobject
  have hparents : CollectedGroupsParent parentType groups :=
    collectFields_parent schema variableValues parentType
      (.object parentType ref) selectionSet
  have hlookup :=
    collectFields_lookupValid_of_selectionSetSemanticsReady_object schema
      variableValues parentType parentType ref selectionSet hobject hself hready
  intro responseName fields hgroup field hfield
  have hparent : field.parentType = parentType :=
    hparents responseName fields hgroup field hfield
  have hflat : field ∈ collectedExecutableFields groups :=
    collectedExecutableFields_mem_of_group_mem hgroup hfield
  rcases hlookup field hflat with ⟨definition, hdefinition⟩
  have hfieldFlat :
      field ∈ collectFlatFields schema variableValues parentType
        (.object parentType ref) selectionSet :=
    (collectFlatFields_mem_collectFields schema variableValues parentType
      (.object parentType ref) selectionSet field).mpr (by
        rw [flattenCollectedFields_eq_collectedExecutableFields]
        exact hflat)
  have hfieldCoercion :=
    collectFlatFields_field_argumentCoercionReady schema variableValues
      parentType parentType ref selectionSet rfl hcoercion field hfieldFlat definition
      (by simpa [hparent] using hdefinition)
  exact ⟨definition, by simpa [hparent] using hdefinition,
    hfieldCoercion.1, hfieldCoercion.2⟩

private theorem executableFieldsReady_tail
    {schema : Schema} {field : ExecutableField} {fields : List ExecutableField}
    (hready : executableFieldsReady schema (field :: fields))
    : ∀ candidate, candidate ∈ fields -> executableFieldReady schema candidate := by
  intro candidate hcandidate
  exact hready.2.1 candidate (by simp [hcandidate])

private theorem executableFieldsReady_composite_inhabited
    {schema : Schema} {fields : List ExecutableField}
    (hready : executableFieldsReady schema fields)
    (field : ExecutableField) (hfield : field ∈ fields)
    (definition : FieldDefinition)
    (hlookup : schema.lookupField field.parentType field.fieldName = some definition)
    : definition.outputType.isCompositeBool schema = true
      -> schema.getPossibleTypes definition.outputType.namedType ≠ [] := by
  rcases hready.2.1 field hfield with
      ⟨readyDefinition, hreadyLookup, _hchild, hinhabited⟩
  rw [hlookup] at hreadyLookup
  injection hreadyLookup with hdefinition
  subst readyDefinition
  intro hcomposite
  exact (hinhabited hcomposite).1

private theorem executableGroupsReady_tail
    {schema : Schema}
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)}
    (hready : executableGroupsReady schema (group :: groups))
    : executableGroupsReady schema groups := by
  intro responseName fields hgroup
  exact hready responseName fields (by simp [hgroup])

private theorem executableFieldsArgumentCoercionReady_tail
    {schema : Schema} {variableValues : VariableValues}
    {field : ExecutableField} {fields : List ExecutableField}
    (hready
      : executableFieldsArgumentCoercionReady schema variableValues (field :: fields))
    : executableFieldsArgumentCoercionReady schema variableValues fields := by
  intro candidate hcandidate
  exact hready candidate (by simp [hcandidate])

private theorem executableGroupsArgumentCoercionReady_tail
    {schema : Schema} {variableValues : VariableValues}
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)}
    (hready
      : executableGroupsArgumentCoercionReady schema variableValues (group :: groups))
    : executableGroupsArgumentCoercionReady schema variableValues groups := by
  intro responseName fields hgroup
  exact hready responseName fields (by simp [hgroup])

private theorem executableGroupsDepthBound_tail
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)} {depth : Nat}
    (hdepth : executableGroupsDepthBound (group :: groups) depth)
    : executableGroupsDepthBound groups depth := by
  intro responseName fields hgroup
  exact hdepth responseName fields (by simp [hgroup])

theorem completionFieldsReady_merged_semantics
    {schema : Schema}
    {fieldType : TypeRef} {fields : List ExecutableField}
    {runtimeType : Name}
    (hready : completionFieldsReady schema fieldType fields)
    (hincludes : schema.typeIncludesObjectBool fieldType.namedType runtimeType = true)
    : NormalForm.selectionSetSemanticsReady schema runtimeType
        (mergedFieldSelectionSet fields) := by
  rcases hready with
    ⟨hfieldsReady, sourceField, sourceDefinition, hsource, hsourceLookup, htype⟩
  have heach : ∀ field, field ∈ fields ->
      NormalForm.selectionSetSemanticsReady schema runtimeType field.selectionSet := by
    intro field hfield
    rcases hfieldsReady.2.1 field hfield with
      ⟨fieldDefinition, hfieldLookup, hchild, _hinhabited⟩
    rcases hfieldsReady.2.2.1 sourceField field hsource hfield with
      ⟨hparent, hfieldName, _harguments⟩
    have hfieldLookup' :
        schema.lookupField sourceField.parentType sourceField.fieldName
          = some fieldDefinition := by
      simpa [hparent, hfieldName] using hfieldLookup
    rw [hsourceLookup] at hfieldLookup'
    injection hfieldLookup' with hdefinition
    subst fieldDefinition
    exact hchild runtimeType (by
      rw [← htype]
      exact hincludes)
  have hflat : ∀ candidates : List ExecutableField,
      (∀ field, field ∈ candidates ->
        NormalForm.selectionSetSemanticsReady schema runtimeType field.selectionSet)
      -> NormalForm.selectionSetSemanticsReady schema runtimeType
          (candidates.flatMap ExecutableField.selectionSet) := by
    intro candidates
    induction candidates with
    | nil =>
        intro _hready
        exact NormalForm.selectionSetSemanticsReady_nil schema runtimeType
    | cons field rest ih =>
        intro hready
        rw [List.flatMap_cons]
        apply NormalForm.selectionSetSemanticsReady_append
        · exact hready field (by simp)
        · apply ih
          intro candidate hcandidate
          exact hready candidate (by simp [hcandidate])
  rw [Execution.FieldGroups.mergedFieldSelectionSet_eq_flatMap]
  exact hflat fields heach

theorem completionFieldsReady_merged_argumentCoercion
    {schema : Schema} {variableValues : VariableValues}
    {fieldType : TypeRef} {fields : List ExecutableField}
    {runtimeType : Name}
    (hready : completionFieldsReady schema fieldType fields)
    (hcoercion : executableFieldsArgumentCoercionReady schema variableValues fields)
    (hincludes : schema.typeIncludesObjectBool fieldType.namedType runtimeType = true)
    : selectionSetArgumentsCoercible schema variableValues runtimeType
        (mergedFieldSelectionSet fields) := by
  rcases hready with
    ⟨hfieldsReady, sourceField, sourceDefinition, hsource, hsourceLookup, htype⟩
  have heach : ∀ field, field ∈ fields ->
      selectionSetArgumentsCoercible schema variableValues runtimeType
        field.selectionSet := by
    intro field hfield
    rcases hcoercion field hfield with
      ⟨fieldDefinition, hfieldLookup, _hfieldCoercion, hchild⟩
    rcases hfieldsReady.2.2.1 sourceField field hsource hfield with
      ⟨hparent, hfieldName, _harguments⟩
    have hfieldLookup' :
        schema.lookupField sourceField.parentType sourceField.fieldName
          = some fieldDefinition := by
      simpa [hparent, hfieldName] using hfieldLookup
    rw [hsourceLookup] at hfieldLookup'
    injection hfieldLookup' with hdefinition
    subst fieldDefinition
    exact hchild runtimeType (by
      rw [← htype]
      exact hincludes)
  have hflat : ∀ candidates : List ExecutableField,
      (∀ field, field ∈ candidates ->
        selectionSetArgumentsCoercible schema variableValues runtimeType
          field.selectionSet) ->
        selectionSetArgumentsCoercible schema variableValues runtimeType
          (candidates.flatMap ExecutableField.selectionSet) := by
    intro candidates
    induction candidates with
    | nil => intro _hready; trivial
    | cons field rest ih =>
        intro hready
        rw [List.flatMap_cons]
        rw [selectionSetArgumentsCoercible_append]
        constructor
        · exact hready field (by simp)
        · apply ih
          intro candidate hcandidate
          exact hready candidate (by simp [hcandidate])
  rw [Execution.FieldGroups.mergedFieldSelectionSet_eq_flatMap]
  exact hflat fields heach

theorem completionFieldsReady_merged_inhabited
    {schema : Schema}
    {fieldType : TypeRef} {fields : List ExecutableField}
    {runtimeType : Name}
    (hready : completionFieldsReady schema fieldType fields)
    (hincludes : schema.typeIncludesObjectBool fieldType.namedType runtimeType = true)
    : selectionSetCompositeFieldTypesInhabited schema runtimeType
        (mergedFieldSelectionSet fields) := by
  rcases hready with
    ⟨hfieldsReady, sourceField, sourceDefinition, hsource, hsourceLookup, htype⟩
  have hcomposite : sourceDefinition.outputType.isCompositeBool schema = true := by
    change (TypeRef.named sourceDefinition.outputType.namedType).isCompositeBool
      schema = true
    apply named_composite_of_typeIncludesObjectBool schema _ runtimeType
    rw [← htype]
    exact hincludes
  have heach : ∀ field, field ∈ fields ->
      selectionSetCompositeFieldTypesInhabited schema runtimeType
        field.selectionSet := by
    intro field hfield
    rcases hfieldsReady.2.1 field hfield with
      ⟨fieldDefinition, hfieldLookup, _hchild, hfieldInhabited⟩
    rcases hfieldsReady.2.2.1 sourceField field hsource hfield with
      ⟨hparent, hfieldName, _harguments⟩
    have hfieldLookup' :
        schema.lookupField sourceField.parentType sourceField.fieldName
          = some fieldDefinition := by
      simpa [hparent, hfieldName] using hfieldLookup
    rw [hsourceLookup] at hfieldLookup'
    injection hfieldLookup' with hdefinition
    subst fieldDefinition
    exact (hfieldInhabited hcomposite).2 runtimeType (by
      rw [← htype]
      exact hincludes)
  rw [Execution.FieldGroups.mergedFieldSelectionSet_eq_flatMap]
  unfold selectionSetCompositeFieldTypesInhabited
  intro selection hselection
  simp only [List.mem_flatMap] at hselection
  rcases hselection with ⟨field, hfield, hselection⟩
  have hfieldInhabited := heach field hfield
  unfold selectionSetCompositeFieldTypesInhabited at hfieldInhabited
  exact hfieldInhabited selection hselection

theorem completionFieldsReady_merged_canMerge
    {schema : Schema}
    {fieldType : TypeRef} {fields : List ExecutableField}
    (hready : completionFieldsReady schema fieldType fields)
    (objectType : Name)
    : FieldMerge.fieldsInSetCanMerge schema objectType (mergedFieldSelectionSet fields) :=
  hready.1.2.2.2 objectType

set_option maxRecDepth 10000 in
private theorem supportedAnnotatedExecution_all
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hresolvers : ResolversSupported schema resolvers)
    : (∀ fuel source groups depth,
        executableGroupsExecutionReady schema variableValues groups
        -> executableGroupsDepthBound groups depth
        -> responseDepthFuelBound schema depth ≤ fuel
        -> ∃ fields,
            executeQueryAnnotatedCollectedFields schema resolvers variableValues
              fuel source groups
            = .ok (fields, 0))
      ∧ (∀ fuel source responseName fields depth,
          executableFieldsExecutionReady schema variableValues fields
          -> (∀ field,
                field ∈ fields
                -> selectionSetResponseDepth field.selectionSet + 1 ≤ depth)
          -> responseDepthFuelBound schema depth ≤ fuel
          -> ∃ result,
              executeQueryAnnotatedField schema resolvers variableValues fuel source
                responseName fields
              = .ok (result, 0))
      ∧ (∀ fuel fieldType fields value depth,
          completionFieldsExecutionReady schema variableValues fieldType fields
          -> (∀ field,
                field ∈ fields
                -> selectionSetResponseDepth field.selectionSet + 1 ≤ depth)
          -> resolverValueSupported schema fieldType value
          -> valueCompletionFuelBound schema depth fieldType ≤ fuel
          -> ∃ result,
              completeAnnotatedResponseValue schema resolvers variableValues fuel
                  fieldType fields value
                = .ok (result, 0)
              ∧ result ≠ .null)
      ∧ (∀ fuel itemType fields values depth,
          completionFieldsExecutionReady schema variableValues itemType fields
          -> (∀ field,
                field ∈ fields
                -> selectionSetResponseDepth field.selectionSet + 1 ≤ depth)
          -> resolverValuesSupported schema itemType values
          -> valueCompletionFuelBound schema depth itemType ≤ fuel
          -> ∃ result,
              completeAnnotatedResponseValueList schema resolvers variableValues fuel
                itemType fields values
              = .ok (result, 0)) := by
  apply executeQueryAnnotatedCollectedFields.mutual_induct schema resolvers variableValues
  case case1 =>
    intro fuel source depth _hready _hdepth _hfuel
    exact ⟨[], by simp [executeQueryAnnotatedCollectedFields]⟩
  case case2 =>
    intro fuel source responseName fields rest headIH tailIH depth hready hdepth hfuel
    have hheadReady : executableFieldsExecutionReady schema variableValues fields :=
      ⟨hready.1 responseName fields (by simp), hready.2 responseName fields (by simp)⟩
    have htailReady : executableGroupsExecutionReady schema variableValues rest :=
      ⟨executableGroupsReady_tail hready.1,
        executableGroupsArgumentCoercionReady_tail hready.2⟩
    have hheadDepth : ∀ field, field ∈ fields
        -> selectionSetResponseDepth field.selectionSet + 1 ≤ depth := by
      intro field hfield
      exact hdepth responseName fields (by simp) field hfield
    have htailDepth : executableGroupsDepthBound rest depth :=
      executableGroupsDepthBound_tail hdepth
    rcases headIH depth hheadReady hheadDepth hfuel with ⟨head, hhead⟩
    rcases tailIH depth htailReady htailDepth hfuel with ⟨tail, htail⟩
    exact ⟨head ++ tail, by
      simp [executeQueryAnnotatedCollectedFields, hhead, htail, Result.combine]⟩
  case case3 =>
    intro fuel source responseName depth hready _hdepth _hfuel
    exact False.elim (hready.1.1 rfl)
  case case4 =>
    intro source responseName field rest depth hready hdepth hfuel
    have hpositive : 0 < responseDepthFuelBound schema depth := by
      unfold responseDepthFuelBound
      omega
    omega
  case case5 =>
    intro source responseName field rest fuel hlookup depth hready _hdepth _hfuel
    rcases hready.1.2.1 field (by simp) with
      ⟨definition, hdefinition, _hchild, _hinhabited⟩
    rw [hlookup] at hdefinition
    cases hdefinition
  case case6 =>
    intro source responseName field rest fuel definition hlookup hcoerce depth
      hready _hdepth _hfuel
    rcases hready.2 field (by simp) with
      ⟨readyDefinition, hreadyLookup, hcoercion, _hchild⟩
    rw [hlookup] at hreadyLookup
    injection hreadyLookup with hdefinition
    subst readyDefinition
    rw [hcoerce] at hcoercion
    simp at hcoercion
  case case7 =>
    intro source responseName field rest fuel definition hlookup coercedArguments
      _hcoerce hresolve depth hready _hdepth _hfuel
    rcases hresolvers field.parentType field.fieldName coercedArguments source
        definition hlookup
        (executableFieldsReady_composite_inhabited hready.1 field (by simp)
          definition hlookup) with ⟨value, hvalue, _hsupported⟩
    change resolvers.resolve field.parentType field.fieldName coercedArguments source
      = none at hresolve
    rw [hresolve] at hvalue
    cases hvalue
  case case8 =>
    intro source responseName field rest fuel definition hlookup coercedArguments
      _hcoerce resolved hresolve completeIH depth hready hdepth hfuel
    rcases hready.2 field (by simp) with
      ⟨readyDefinition, hreadyLookup, _hcoercion, _hchild⟩
    rw [hlookup] at hreadyLookup
    injection hreadyLookup with hdefinition
    subst readyDefinition
    have htypeFuel :
        typeRefExecutionCompletionFuel definition.outputType
          ≤ typeDefinitionsExecutionCompletionFuel schema.types :=
      lookupField_executionCompletionFuel_le schema hlookup
    have hdepthPositive : 0 < depth := by
      have := hdepth field (by simp)
      omega
    have hvalueFuel :
        valueCompletionFuelBound schema depth definition.outputType ≤ fuel :=
      valueCompletionFuelBound_le_after_field schema depth fuel
        definition.outputType hdepthPositive htypeFuel hfuel
    have hcompletionReady :
        completionFieldsExecutionReady schema variableValues definition.outputType
          (field :: rest) := by
      exact ⟨⟨hready.1, field, definition, by simp, hlookup, rfl⟩, hready.2⟩
    rcases hresolvers field.parentType field.fieldName coercedArguments source
        definition hlookup
        (executableFieldsReady_composite_inhabited hready.1 field (by simp)
          definition hlookup) with ⟨value, hvalue, hsupported⟩
    change resolvers.resolve field.parentType field.fieldName coercedArguments source
      = some resolved at hresolve
    rw [hresolve] at hvalue
    injection hvalue with hvalue
    subst value
    rcases completeIH depth hcompletionReady hdepth hsupported hvalueFuel with
      ⟨completed, hcompleted, _hnonnull⟩
    exact ⟨[.resolved responseName
        (resolvedFieldProvenance schema variableValues definition field) completed], by
      simp [executeQueryAnnotatedField, hlookup, _hcoerce, resolveFieldValue,
        hresolve, hcompleted, singleAnnotatedResponseFieldResult]⟩
  case case9 =>
    intro fieldType fields value depth _hready _hdepth _hsupported hfuel
    unfold valueCompletionFuelBound at hfuel
    omega
  case case10 =>
    intro fuel inner fields value hfuelPositive completeIH depth hready hdepth
      hsupported hfuel
    have hinnerReady : completionFieldsExecutionReady schema variableValues inner fields := by
      simpa [completionFieldsExecutionReady, completionFieldsReady,
        TypeRef.namedType] using hready
    have hinnerSupported : resolverValueSupported schema inner value := by
      simpa [resolverValueSupported] using hsupported
    have hinnerFuel : valueCompletionFuelBound schema depth inner ≤ fuel := by
      simpa [valueCompletionFuelBound_inner_nonNull] using hfuel
    rcases completeIH depth hinnerReady hdepth hinnerSupported hinnerFuel with
      ⟨result, hresult, hnonnull⟩
    cases fuel with
    | zero => exact False.elim (hfuelPositive rfl)
    | succ fuel =>
        exact ⟨result, by
          simp [completeAnnotatedResponseValue, hresult,
            completeNonNullAnnotatedResponseValue], hnonnull⟩
  case case11 =>
    intro fuel fieldType fields hnotNonNull depth _hready _hdepth hsupported _hfuel
    cases fieldType with
    | named typeName => simp [resolverValueSupported] at hsupported
    | list inner => simp [resolverValueSupported] at hsupported
    | nonNull inner => exact False.elim (hnotNonNull inner rfl)
  case case12 =>
    intro fuel typeName fields value hcomposite depth _hready _hdepth hsupported
      _hfuel
    simp [resolverValueSupported, hcomposite] at hsupported
  case case13 =>
    intro fuel typeName fields value hnotComposite depth _hready _hdepth
      _hsupported _hfuel
    have hleaf : (TypeRef.named typeName).isCompositeBool schema = false := by
      simpa using hnotComposite
    exact ⟨.scalar value, by
      simp [completeAnnotatedResponseValue, hleaf], by simp⟩
  case case14 =>
    intro fuel parentType fields runtimeType ref hincludes childGroups childIH depth
      hready hdepth _hsupported hfuel
    have hchildSemantics :
        NormalForm.selectionSetSemanticsReady schema runtimeType
          (mergedFieldSelectionSet fields) :=
      completionFieldsReady_merged_semantics hready.1 hincludes
    have hchildCoercion :
        selectionSetArgumentsCoercible schema variableValues runtimeType
          (mergedFieldSelectionSet fields) :=
      completionFieldsReady_merged_argumentCoercion hready.1 hready.2 hincludes
    have hchildMerge :
        FieldMerge.fieldsInSetCanMerge schema runtimeType
          (mergedFieldSelectionSet fields) :=
      completionFieldsReady_merged_canMerge hready.1 runtimeType
    have hchildInhabited :
        selectionSetCompositeFieldTypesInhabited schema runtimeType
          (mergedFieldSelectionSet fields) :=
      completionFieldsReady_merged_inhabited hready.1 hincludes
    have hchildObject : schema.objectType runtimeType := by
      apply SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
        parentType runtimeType
      exact List.contains_iff_mem.mp hincludes
    have hchildReady : executableGroupsExecutionReady schema variableValues childGroups := by
      dsimp only [childGroups]
      rw [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
      exact ⟨
        executableGroupsReady_collectFields schema variableValues runtimeType ref
          (mergedFieldSelectionSet fields) hchildObject hchildSemantics
          hchildInhabited hchildMerge,
        executableGroupsArgumentCoercionReady_collectFields schema variableValues
          runtimeType ref (mergedFieldSelectionSet fields) hchildObject
          hchildSemantics hchildCoercion
      ⟩
    have hdepthPositive : 0 < depth := by
      rcases hready.1.1.1 with hnonempty
      cases hfields : fields with
      | nil => exact False.elim (hnonempty hfields)
      | cons field rest =>
          have := hdepth field (by simp [hfields])
          omega
    have hselectionDepth :
        selectionSetResponseDepth (mergedFieldSelectionSet fields) ≤ depth - 1 := by
      rw [Execution.FieldGroups.mergedFieldSelectionSet_eq_flatMap]
      apply selectionSetResponseDepth_flatMap_le fields (depth - 1)
      intro field hfield
      have hfieldDepth := hdepth field hfield
      omega
    have hchildDepth : executableGroupsDepthBound childGroups (depth - 1) := by
      dsimp only [childGroups]
      rw [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
      apply executableGroupsDepthBound_of_runtime
      intro field hfield
      exact Nat.le_trans
        (collectFields_responseDepth_bound schema variableValues runtimeType
          (.object runtimeType ref) (mergedFieldSelectionSet fields) field hfield)
        hselectionDepth
    have hchildFuel : responseDepthFuelBound schema (depth - 1) ≤ fuel :=
      responseDepthFuelBound_le_of_value_named schema depth fuel parentType hfuel
    rcases childIH (depth - 1) hchildReady hchildDepth hchildFuel with
      ⟨responseFields, hresponse⟩
    have hresponse' :
        executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
            (.object runtimeType ref)
            (collectFields schema variableValues runtimeType
              (.object runtimeType ref) (mergedFieldSelectionSet fields))
          = .ok (responseFields, 0) := by
      simpa [childGroups,
        NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
        using hresponse
    exact ⟨.object runtimeType responseFields, by
      simp [completeAnnotatedResponseValue, hincludes, hresponse',
        catchAnnotatedResponseBubbleAsNull], by simp⟩
  case case15 =>
    intro fuel parentType fields runtimeType ref hnotIncludes depth _hready _hdepth
      hsupported _hfuel
    exact False.elim (hnotIncludes (by
      simpa [resolverValueSupported] using hsupported))
  case case16 =>
    intro fuel inner fields values completeListIH depth hready hdepth hsupported
      hfuel
    have hinnerReady : completionFieldsExecutionReady schema variableValues inner fields := by
      simpa [completionFieldsExecutionReady, completionFieldsReady,
        TypeRef.namedType] using hready
    have hvaluesSupported : resolverValuesSupported schema inner values := by
      simpa [resolverValueSupported] using hsupported
    have hinnerFuel : valueCompletionFuelBound schema depth inner ≤ fuel :=
      valueCompletionFuelBound_inner_list schema depth fuel inner hfuel
    rcases completeListIH depth hinnerReady hdepth hvaluesSupported hinnerFuel with
      ⟨result, hresult⟩
    exact ⟨.list result, by
      simp [completeAnnotatedResponseValue, hresult,
        catchAnnotatedResponseBubbleAsNull], by simp⟩
  case case17 =>
    intro fuel typeName fields values depth _hready _hdepth hsupported _hfuel
    simp [resolverValueSupported] at hsupported
  case case18 =>
    intro fuel inner fields value hnotNull hnotList depth _hready _hdepth
      hsupported _hfuel
    cases value with
    | null => exact False.elim (hnotNull rfl)
    | scalar scalarValue => simp [resolverValueSupported] at hsupported
    | object runtimeType ref => simp [resolverValueSupported] at hsupported
    | list values => exact False.elim (hnotList values rfl)
  case case19 =>
    intro fuel itemType fields depth _hready _hdepth _hsupported _hfuel
    exact ⟨[], by simp [completeAnnotatedResponseValueList]⟩
  case case20 =>
    intro fuel itemType fields value values tailIH headIH depth hready hdepth
      hsupported hfuel
    simp only [resolverValuesSupported] at hsupported
    rcases hsupported with ⟨hheadSupported, htailSupported⟩
    rcases tailIH depth hready hdepth hheadSupported hfuel with
      ⟨head, hhead, _hheadNonnull⟩
    rcases headIH depth hready hdepth htailSupported hfuel with ⟨tail, htail⟩
    exact ⟨head :: tail, by
      simp [completeAnnotatedResponseValueList, hhead, htail, Result.combine]⟩

theorem executeQueryAnnotatedCollectedFields_supported
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hresolvers : ResolversSupported schema resolvers)
    (runtimeType : Name) (ref : ObjectRef) (selectionSet : List Selection)
    (hobject : schema.objectType runtimeType)
    (hready : NormalForm.selectionSetSemanticsReady schema runtimeType selectionSet)
    (hcoercion
      : selectionSetArgumentsCoercible schema variableValues runtimeType selectionSet)
    (hinhabited
      : selectionSetCompositeFieldTypesInhabited schema runtimeType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema runtimeType selectionSet)
    (fuel : Nat)
    (hfuel
      : responseDepthFuelBound schema (selectionSetResponseDepth selectionSet) ≤ fuel)
    : ∃ fields,
        executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
          (.object runtimeType ref)
          (collectFields schema variableValues runtimeType
            (.object runtimeType ref) selectionSet)
        = .ok (fields, 0) := by
  apply (supportedAnnotatedExecution_all schema resolvers variableValues hschema
    hresolvers).1 fuel (.object runtimeType ref)
    (collectFields schema variableValues runtimeType (.object runtimeType ref)
      selectionSet)
    (selectionSetResponseDepth selectionSet)
  · exact ⟨
      executableGroupsReady_collectFields schema variableValues runtimeType ref
        selectionSet hobject hready hinhabited hmerge,
      executableGroupsArgumentCoercionReady_collectFields schema variableValues
        runtimeType ref selectionSet hobject hready hcoercion
    ⟩
  · exact executableGroupsDepthBound_of_runtime
      (collectFields_responseDepth_bound schema variableValues runtimeType
        (.object runtimeType ref) selectionSet)
  · exact hfuel

theorem named_isCompositeBool_eq_true_iff (schema : Schema) (typeName : Name)
    : (TypeRef.named typeName).isCompositeBool schema = true
      ↔ schema.isCompositeType typeName := by
  unfold TypeRef.isCompositeBool Schema.isCompositeType TypeRef.namedType
  cases hlookup : schema.lookupType typeName with
  | none => simp
  | some typeDefinition =>
      cases typeDefinition <;> simp [TypeDefinition.isCompositeType]

noncomputable def representativePossibleObject (schema : Schema) (typeName : Name)
    : Name :=
  if hpossible : schema.getPossibleTypes typeName ≠ [] then
    Classical.choose (List.exists_mem_of_ne_nil _ hpossible)
  else
    typeName

theorem representativePossibleObject_mem
    (schema : Schema) (typeName : Name)
    (hpossible : schema.getPossibleTypes typeName ≠ [])
    : representativePossibleObject schema typeName
      ∈ schema.getPossibleTypes typeName := by
  classical
  simp only [representativePossibleObject, dif_pos hpossible]
  exact Classical.choose_spec (List.exists_mem_of_ne_nil _ hpossible)

noncomputable def supportedResolverValue (schema : Schema)
    : TypeRef -> ResolverValue PUnit
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        .object (representativePossibleObject schema typeName) PUnit.unit
      else
        .scalar "query-inclusion-probe"
  | .list inner => .list [supportedResolverValue schema inner]
  | .nonNull inner => supportedResolverValue schema inner

private theorem supportedResolverValue_supported (schema : Schema)
    : ∀ fieldType,
        (fieldType.isCompositeBool schema = true
          -> schema.getPossibleTypes fieldType.namedType ≠ [])
        -> resolverValueSupported schema fieldType
            (supportedResolverValue schema fieldType) := by
  intro fieldType hinhabited
  induction fieldType with
  | named typeName =>
      by_cases hcomposite :
          (TypeRef.named typeName).isCompositeBool schema = true
      · simp only [supportedResolverValue, hcomposite, if_true,
          resolverValueSupported]
        apply List.contains_iff_mem.mpr
        exact representativePossibleObject_mem schema typeName
          (hinhabited hcomposite)
      · have hleaf :
            (TypeRef.named typeName).isCompositeBool schema = false := by
          simpa using hcomposite
        simp [supportedResolverValue, hleaf, resolverValueSupported]
  | list inner ih =>
      simpa [supportedResolverValue, resolverValueSupported,
        resolverValuesSupported] using ih (by
          simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hinhabited)
  | nonNull inner ih =>
      simpa [supportedResolverValue, resolverValueSupported] using
        ih (by
          simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hinhabited)

noncomputable def supportedResolvers (schema : Schema) : Resolvers PUnit where
  resolve parentType fieldName _arguments _source :=
    match schema.lookupField parentType fieldName with
    | none => none
    | some definition =>
        some (supportedResolverValue schema definition.outputType)
  resolve_argumentsEquivalent := by
    intros
    rfl

private theorem supportedResolvers_supported (schema : Schema)
    : ResolversSupported schema (supportedResolvers schema) := by
  intro parentType fieldName arguments source definition hlookup hinhabited
  refine ⟨supportedResolverValue schema definition.outputType, ?_, ?_⟩
  · simp [supportedResolvers, hlookup]
  · exact supportedResolverValue_supported schema definition.outputType hinhabited

theorem executeQueryAnnotated_supported
    (schema : Schema)
    (suppliedValues : VariableValues) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (hcoercion : operationArgumentsCoercible schema suppliedValues operation)
    (hinhabited : operationCompositeFieldTypesInhabited schema operation)
    : ∃ fields,
        executeQueryAnnotated schema (supportedResolvers schema)
          suppliedValues operation (.object (operation.rootType schema) PUnit.unit)
        = { data := .object (operation.rootType schema) fields, errors := 0 } := by
  let variableValues := coerceVariableValues operation suppliedValues
  have hobject : schema.objectType (operation.rootType schema) :=
    NormalForm.CompleteNormalization.operation_root_object_of_valid hschema hoperation
  have hready : NormalForm.selectionSetSemanticsReady schema
      (operation.rootType schema) operation.selectionSet :=
    NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
      hschema hoperation
  have hmerge : FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
      operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  rcases executeQueryAnnotatedCollectedFields_supported schema
      (supportedResolvers schema) variableValues hschema
      (supportedResolvers_supported schema) (operation.rootType schema)
      PUnit.unit operation.selectionSet hobject hready
      (by simpa [operationArgumentsCoercible, variableValues] using hcoercion)
      hinhabited hmerge
      (executeQueryFuelBound schema operation)
      (doesNotExhaustFuel schema operation) with ⟨fields, hfields⟩
  refine ⟨fields, ?_⟩
  unfold executeQueryAnnotated executeQueryAnnotatedWithFuel
  have hroot : rootSourceAppliesBool schema operation
      (.object (operation.rootType schema) PUnit.unit) = true := by
    simp only [rootSourceAppliesBool, runtimeObjectType?]
    exact NormalForm.object_typeIncludesObjectBool_self schema hobject
  simp [hroot, variableValues, hfields, runtimeObjectType?]

abbrev RuntimePlan := Nat -> Name -> Name

def RuntimePlan.Valid (schema : Schema) (plan : RuntimePlan) : Prop :=
  ∀ depth typeName,
    schema.getPossibleTypes typeName ≠ []
    -> plan depth typeName ∈ schema.getPossibleTypes typeName

noncomputable def defaultRuntimePlan (schema : Schema) : RuntimePlan :=
  fun _depth typeName => representativePossibleObject schema typeName

theorem defaultRuntimePlan_valid (schema : Schema)
    : (defaultRuntimePlan schema).Valid schema := by
  intro depth typeName hpossible
  exact representativePossibleObject_mem schema typeName hpossible

def plannedResolverValue (schema : Schema) (plan : RuntimePlan) (depth : Nat)
    : TypeRef -> ResolverValue Nat
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        .object (plan depth typeName) (depth + 1)
      else
        .scalar "query-inclusion-probe"
  | .list inner => .list [plannedResolverValue schema plan depth inner]
  | .nonNull inner => plannedResolverValue schema plan depth inner

private theorem plannedResolverValue_supported
    (schema : Schema) (plan : RuntimePlan) (hplan : plan.Valid schema)
    (depth : Nat)
    : ∀ fieldType,
        (fieldType.isCompositeBool schema = true
          -> schema.getPossibleTypes fieldType.namedType ≠ [])
        -> resolverValueSupported schema fieldType
            (plannedResolverValue schema plan depth fieldType) := by
  intro fieldType hinhabited
  induction fieldType with
  | named typeName =>
      by_cases hcomposite :
          (TypeRef.named typeName).isCompositeBool schema = true
      · simp only [plannedResolverValue, hcomposite, if_true,
          resolverValueSupported]
        exact List.contains_iff_mem.mpr
          (hplan depth typeName (hinhabited hcomposite))
      · have hleaf :
            (TypeRef.named typeName).isCompositeBool schema = false := by
          simpa using hcomposite
        simp [plannedResolverValue, hleaf, resolverValueSupported]
  | list inner ih =>
      simpa [plannedResolverValue, resolverValueSupported,
        resolverValuesSupported] using ih (by
          simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hinhabited)
  | nonNull inner ih =>
      simpa [plannedResolverValue, resolverValueSupported] using
        ih (by
          simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hinhabited)

def plannedResolvers (schema : Schema) (plan : RuntimePlan) : Resolvers Nat where
  resolve parentType fieldName _arguments source :=
    let depth :=
      match source with
      | .object _runtimeType depth => depth
      | _ => 0
    match schema.lookupField parentType fieldName with
    | some definition =>
        some (plannedResolverValue schema plan depth definition.outputType)
    | none => none
  resolve_argumentsEquivalent := by
    intro parentType fieldName firstArguments laterArguments source _hequivalent
    rfl

theorem plannedResolvers_supported
    (schema : Schema) (plan : RuntimePlan) (hplan : plan.Valid schema)
    : ResolversSupported schema (plannedResolvers schema plan) := by
  intro parentType fieldName arguments source definition hlookup hinhabited
  cases source with
  | null => exact ⟨_, by simp [plannedResolvers, hlookup],
      plannedResolverValue_supported schema plan hplan 0 definition.outputType
        hinhabited⟩
  | scalar value => exact ⟨_, by simp [plannedResolvers, hlookup],
      plannedResolverValue_supported schema plan hplan 0 definition.outputType
        hinhabited⟩
  | object runtimeType depth => exact ⟨_, by simp [plannedResolvers, hlookup],
      plannedResolverValue_supported schema plan hplan depth definition.outputType
        hinhabited⟩
  | list values => exact ⟨_, by simp [plannedResolvers, hlookup],
      plannedResolverValue_supported schema plan hplan 0 definition.outputType
        hinhabited⟩

theorem executeQueryAnnotated_planned_supported
    (schema : Schema) (plan : RuntimePlan) (hplan : plan.Valid schema)
    (suppliedValues : VariableValues) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (hcoercion : operationArgumentsCoercible schema suppliedValues operation)
    (hinhabited : operationCompositeFieldTypesInhabited schema operation)
    : ∃ fields,
        executeQueryAnnotated schema (plannedResolvers schema plan)
          suppliedValues operation (.object (operation.rootType schema) 0)
        = { data := .object (operation.rootType schema) fields, errors := 0 } := by
  let variableValues := coerceVariableValues operation suppliedValues
  have hobject : schema.objectType (operation.rootType schema) :=
    NormalForm.CompleteNormalization.operation_root_object_of_valid hschema hoperation
  have hready : NormalForm.selectionSetSemanticsReady schema
      (operation.rootType schema) operation.selectionSet :=
    NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
      hschema hoperation
  have hmerge : FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
      operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  rcases executeQueryAnnotatedCollectedFields_supported schema
      (plannedResolvers schema plan) variableValues hschema
      (plannedResolvers_supported schema plan hplan) (operation.rootType schema) 0
      operation.selectionSet hobject hready
      (by simpa [operationArgumentsCoercible, variableValues] using hcoercion)
      hinhabited hmerge
      (executeQueryFuelBound schema operation)
      (doesNotExhaustFuel schema operation) with ⟨fields, hfields⟩
  refine ⟨fields, ?_⟩
  unfold executeQueryAnnotated executeQueryAnnotatedWithFuel
  have hroot : rootSourceAppliesBool schema operation
      (.object (operation.rootType schema) 0) = true := by
    simp only [rootSourceAppliesBool, runtimeObjectType?]
    exact NormalForm.object_typeIncludesObjectBool_self schema hobject
  simp [hroot, variableValues, hfields, runtimeObjectType?]

def RuntimePlan.shift (plan : RuntimePlan) : RuntimePlan :=
  fun depth typeName => plan (depth + 1) typeName

def RuntimePlan.cons (head : Name -> Name) (tail : RuntimePlan) : RuntimePlan
  | 0, typeName => head typeName
  | depth + 1, typeName => tail depth typeName

@[simp]
theorem RuntimePlan.shift_cons (head : Name -> Name) (tail : RuntimePlan)
    : (RuntimePlan.cons head tail).shift = tail := by
  funext depth typeName
  rfl

theorem RuntimePlan.Valid.shift
    {schema : Schema} {plan : RuntimePlan} (hplan : plan.Valid schema)
    : plan.shift.Valid schema := by
  intro depth typeName hpossible
  exact hplan (depth + 1) typeName hpossible

theorem RuntimePlan.Valid.cons
    {schema : Schema} {head : Name -> Name} {tail : RuntimePlan}
    (hhead
      : ∀ typeName,
          schema.getPossibleTypes typeName ≠ []
          -> head typeName ∈ schema.getPossibleTypes typeName)
    (htail : tail.Valid schema)
    : (RuntimePlan.cons head tail).Valid schema := by
  intro depth typeName hpossible
  cases depth with
  | zero => exact hhead typeName hpossible
  | succ depth => exact htail depth typeName hpossible

noncomputable def spineRuntime (schema : Schema) (plan : RuntimePlan) (typeName : Name)
    : Name :=
  if plan 0 typeName ∈ schema.getPossibleTypes typeName then
    plan 0 typeName
  else
    representativePossibleObject schema typeName

theorem spineRuntime_eq_of_valid
    (schema : Schema) (plan : RuntimePlan) (hplan : plan.Valid schema)
    (typeName : Name)
    (hpossible : schema.getPossibleTypes typeName ≠ [])
    : spineRuntime schema plan typeName = plan 0 typeName := by
  classical
  simp [spineRuntime, hplan 0 typeName hpossible]

noncomputable def spineResolverValue (schema : Schema) (plan : RuntimePlan)
    : TypeRef -> ResolverValue RuntimePlan
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        .object (spineRuntime schema plan typeName) plan.shift
      else
        .scalar "query-inclusion-probe"
  | .list inner => .list [spineResolverValue schema plan inner]
  | .nonNull inner => spineResolverValue schema plan inner

private theorem spineResolverValue_supported (schema : Schema) (plan : RuntimePlan)
    : ∀ fieldType,
        (fieldType.isCompositeBool schema = true
          -> schema.getPossibleTypes fieldType.namedType ≠ [])
        -> resolverValueSupported schema fieldType
            (spineResolverValue schema plan fieldType) := by
  intro fieldType hinhabited
  induction fieldType with
  | named typeName =>
      by_cases hcomposite :
          (TypeRef.named typeName).isCompositeBool schema = true
      · simp only [spineResolverValue, hcomposite, if_true,
          resolverValueSupported]
        apply List.contains_iff_mem.mpr
        classical
        simp only [spineRuntime]
        split
        · assumption
        · exact representativePossibleObject_mem schema typeName
            (hinhabited hcomposite)
      · have hleaf :
            (TypeRef.named typeName).isCompositeBool schema = false := by
          simpa using hcomposite
        simp [spineResolverValue, hleaf, resolverValueSupported]
  | list inner ih =>
      simpa [spineResolverValue, resolverValueSupported,
        resolverValuesSupported] using ih (by
          simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hinhabited)
  | nonNull inner ih =>
      simpa [spineResolverValue, resolverValueSupported] using
        ih (by
          simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hinhabited)

noncomputable def spineResolvers (schema : Schema) : Resolvers RuntimePlan where
  resolve parentType fieldName _arguments source :=
    let plan :=
      match source with
      | .object _runtimeType plan => plan
      | _ => defaultRuntimePlan schema
    match schema.lookupField parentType fieldName with
    | some definition =>
        some (spineResolverValue schema plan definition.outputType)
    | none => none
  resolve_argumentsEquivalent := by
    intros
    rfl

theorem spineResolvers_supported (schema : Schema)
    : ResolversSupported schema (spineResolvers schema) := by
  intro parentType fieldName arguments source definition hlookup hinhabited
  cases source with
  | null =>
      exact ⟨
        spineResolverValue schema (defaultRuntimePlan schema) definition.outputType,
        by simp [spineResolvers, hlookup],
        spineResolverValue_supported schema
          (defaultRuntimePlan schema) definition.outputType hinhabited
      ⟩
  | scalar value =>
      exact ⟨
        spineResolverValue schema (defaultRuntimePlan schema) definition.outputType,
        by simp [spineResolvers, hlookup],
        spineResolverValue_supported schema
          (defaultRuntimePlan schema) definition.outputType hinhabited
      ⟩
  | object runtimeType plan => exact ⟨_, by simp [spineResolvers, hlookup],
      spineResolverValue_supported schema plan definition.outputType hinhabited⟩
  | list values =>
      exact ⟨
        spineResolverValue schema (defaultRuntimePlan schema) definition.outputType,
        by simp [spineResolvers, hlookup],
        spineResolverValue_supported schema
          (defaultRuntimePlan schema) definition.outputType hinhabited
      ⟩

theorem executeQueryAnnotated_spine_supported
    (schema : Schema)
    (plan : RuntimePlan) (_hplan : plan.Valid schema)
    (suppliedValues : VariableValues) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (hcoercion : operationArgumentsCoercible schema suppliedValues operation)
    (hinhabited : operationCompositeFieldTypesInhabited schema operation)
    : ∃ fields,
        executeQueryAnnotated schema (spineResolvers schema)
          suppliedValues operation (.object (operation.rootType schema) plan)
        = { data := .object (operation.rootType schema) fields, errors := 0 } := by
  let variableValues := coerceVariableValues operation suppliedValues
  have hobject : schema.objectType (operation.rootType schema) :=
    NormalForm.CompleteNormalization.operation_root_object_of_valid hschema hoperation
  have hready : NormalForm.selectionSetSemanticsReady schema
      (operation.rootType schema) operation.selectionSet :=
    NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
      hschema hoperation
  have hmerge : FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
      operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  rcases executeQueryAnnotatedCollectedFields_supported schema
      (spineResolvers schema) variableValues hschema
      (spineResolvers_supported schema) (operation.rootType schema) plan
      operation.selectionSet hobject hready
      (by simpa [operationArgumentsCoercible, variableValues] using hcoercion)
      hinhabited hmerge
      (executeQueryFuelBound schema operation)
      (doesNotExhaustFuel schema operation) with ⟨fields, hfields⟩
  refine ⟨fields, ?_⟩
  unfold executeQueryAnnotated executeQueryAnnotatedWithFuel
  have hroot : rootSourceAppliesBool schema operation
      (.object (operation.rootType schema) plan) = true := by
    simp only [rootSourceAppliesBool, runtimeObjectType?]
    exact NormalForm.object_typeIncludesObjectBool_self schema hobject
  simp [hroot, variableValues, hfields, runtimeObjectType?]

end QueryInclusion
end GraphQL
