import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngrouped.Equivalence.Collection
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngrouped.Equivalence.Collection.StateInvariant
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngrouped.Equivalence.Core
import Proofs.GraphQL.Theories.QueryInclusion.Support.Execution.FieldGroups
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.Execution
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.RuntimeTypes
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.SemanticReadiness.Readiness
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.QueryInclusion.ErrorFreeExecution

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.QueryInclusion

open Execution.FieldGroups
open GraphQL.ConditionTree
open Execution
open SelectionConditions
open Algorithms.ExecutionUngroupedUncached
open Algorithms.ExecutionUngroupedUncached.Eager

def executableFieldSemanticsReady (schema : Schema) (parentType : Name)
    (field : ExecutableField)
    : Prop :=
  ∃ definition,
    schema.lookupField parentType field.fieldName = some definition
    ∧ ∀ runtimeType,
        schema.typeIncludesObjectBool definition.outputType.namedType runtimeType = true
        -> NormalForm.selectionSetSemanticsReady schema runtimeType field.selectionSet

def executableFieldsSemanticsReady (schema : Schema) (parentType : Name)
    (fields : List ExecutableField)
    : Prop :=
  fields ≠ []
  ∧ (∀ field, field ∈ fields -> executableFieldSemanticsReady schema parentType field)
  ∧ executableFieldsSameResolver fields
  ∧ ∀ objectType,
      FieldMerge.fieldsInSetCanMerge schema objectType (mergedFieldSelectionSet fields)

def executableGroupsSemanticsReady (schema : Schema) (parentType : Name)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> executableFieldsSemanticsReady schema parentType fields

def completionFieldsWitness (schema : Schema) (parentType : Name)
    (fieldType : TypeRef)
    (fields : List ExecutableField)
    : Prop :=
  ∃ field definition,
    field ∈ fields
    ∧ schema.lookupField parentType field.fieldName = some definition
    ∧ fieldType.namedType = definition.outputType.namedType

def completionFieldsSemanticsReady (schema : Schema) (parentType : Name)
    (fieldType : TypeRef)
    (fields : List ExecutableField)
    : Prop :=
  executableFieldsSemanticsReady schema parentType fields
  ∧ completionFieldsWitness schema parentType fieldType fields

theorem executableGroupsSemanticsReady_collectFields
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (ref : ObjectRef) (selectionSet : List Selection)
    (hobject : schema.objectType parentType)
    (hready : NormalForm.selectionSetSemanticsReady schema parentType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    : executableGroupsSemanticsReady schema parentType
        (collectFields schema variableValues parentType (.object parentType ref)
          selectionSet) := by
  let groups :=
    collectFields schema variableValues parentType (.object parentType ref) selectionSet
  have hself : ScopedParentRuntimeApplies schema parentType parentType :=
    NormalForm.object_typeIncludesObjectBool_self schema hobject
  have hnonempty : CollectedGroupsFieldsNonempty groups := by
    exact collectFields_fieldsNonempty schema variableValues parentType
      (.object parentType ref) selectionSet
  have hlookup :=
    collectFields_lookupValid_of_selectionSetSemanticsReady_object schema
      variableValues parentType parentType ref selectionSet hobject hself hready
  have hchild :=
    collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object schema
      variableValues parentType parentType ref selectionSet hobject hself hready
  have hcompatible : CollectedGroupsFieldValidationMergeCompatible groups := by
    dsimp only [groups]
    exact collectFields_fieldCompatible_of_canMerge_lookupValid_object schema
      variableValues parentType parentType parentType ref selectionSet hmerge hself
      (NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
        hready)
  have hscoped :
      ExecutableEntriesRuntimeScopedBy schema parentType
        (FieldMerge.collectFields schema parentType selectionSet)
        (collectedExecutableEntries groups) := by
    dsimp only [groups]
    exact collectFields_entriesRuntimeScopedBy_of_selectionSetLookupValid schema
      variableValues parentType parentType parentType ref selectionSet hself
      (NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
        hready)
  intro responseName fields hgroup
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hnonempty responseName fields hgroup
  · intro field hfield
    have hflat : field ∈ collectedExecutableFields groups :=
      collectedExecutableFields_mem_of_group_mem hgroup hfield
    rcases hlookup field hflat with ⟨definition, hdefinition⟩
    refine ⟨definition, hdefinition, ?_⟩
    intro runtimeType hincludes
    exact hchild field hflat definition hdefinition
      runtimeType hincludes
  · intro first later hfirst hlater
    exact hcompatible responseName fields hgroup first later hfirst hlater
  · intro objectType
    apply fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped schema
      parentType parentType selectionSet responseName fields hmerge
    intro entry hentry
    rcases List.mem_map.mp hentry with ⟨field, hfield, rfl⟩
    exact hscoped (responseName, field)
      (collectedExecutableEntries_mem_of_group_mem hgroup hfield)

theorem completionFieldsSemanticsReady_merged_semantics
    {schema : Schema} {parentType : Name}
    {fieldType : TypeRef} {fields : List ExecutableField}
    {runtimeType : Name}
    (hready : completionFieldsSemanticsReady schema parentType fieldType fields)
    (hincludes : schema.typeIncludesObjectBool fieldType.namedType runtimeType = true)
    : NormalForm.selectionSetSemanticsReady schema runtimeType
        (mergedFieldSelectionSet fields) := by
  rcases hready with
    ⟨hfieldsReady, sourceField, sourceDefinition, hsource, hsourceLookup, htype⟩
  have heach : ∀ field, field ∈ fields ->
      NormalForm.selectionSetSemanticsReady schema runtimeType field.selectionSet := by
    intro field hfield
    rcases hfieldsReady.2.1 field hfield with
      ⟨fieldDefinition, hfieldLookup, hchild⟩
    rcases hfieldsReady.2.2.1 sourceField field hsource hfield with
      ⟨hfieldName, _harguments⟩
    have hfieldLookup' :
        schema.lookupField parentType sourceField.fieldName
          = some fieldDefinition := by
      simpa [hfieldName] using hfieldLookup
    rw [hsourceLookup] at hfieldLookup'
    injection hfieldLookup' with hdefinition
    subst fieldDefinition
    apply hchild runtimeType
    rw [← htype]
    exact hincludes
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
        intro hcandidates
        rw [List.flatMap_cons]
        apply NormalForm.selectionSetSemanticsReady_append
        · exact hcandidates field (by simp)
        · apply ih
          intro candidate hcandidate
          exact hcandidates candidate (by simp [hcandidate])
  rw [Execution.FieldGroups.mergedFieldSelectionSet_eq_flatMap]
  exact hflat fields heach

theorem completionFieldsSemanticsReady_merged_canMerge
    {schema : Schema} {parentType : Name}
    {fieldType : TypeRef} {fields : List ExecutableField}
    (hready : completionFieldsSemanticsReady schema parentType fieldType fields)
    (objectType : Name)
    : FieldMerge.fieldsInSetCanMerge schema objectType (mergedFieldSelectionSet fields) :=
  hready.1.2.2.2 objectType

theorem getPossibleTypes_eq_singleton_of_object
    (schema : Schema) {typeName : Name} (hobject : schema.objectType typeName)
    : schema.getPossibleTypes typeName = [typeName] := by
  rcases hobject with ⟨objectType, hlookup⟩
  have hname : objectType.name = typeName := by
    have hmatch := List.find?_some hlookup
    simpa [Schema.lookupType, TypeDefinition.name] using hmatch
  simp [Schema.getPossibleTypes, hlookup, hname]

end GraphQL.QueryInclusion
