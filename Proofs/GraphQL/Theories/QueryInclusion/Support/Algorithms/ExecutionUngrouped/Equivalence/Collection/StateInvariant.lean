import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngrouped.Equivalence.Collection
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngrouped.Equivalence.Core
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngrouped.Equivalence.Validation
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.Execution
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.LookupValidity
import Proofs.GraphQL.Theories.QueryInclusion.Support.Validation.FieldMerge

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.Algorithms.ExecutionUngroupedUncached.Eager

open GraphQL.Execution

def CollectedGroupsResolveStable
    {ObjectIdentity : Type} (schema : Schema)
    (resolvers : Resolvers ObjectIdentity) (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> ExecutableFieldsResolveStable schema resolvers variableValues source fields

theorem CollectedGroupsResolveStable.group
    {ObjectIdentity : Type} (schema : Schema)
    (resolvers : Resolvers ObjectIdentity) (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (fields : List ExecutableField)
    : CollectedGroupsResolveStable schema resolvers variableValues source groups
      -> (responseName, fields) ∈ groups
      -> ExecutableFieldsResolveStable schema resolvers variableValues source fields := by
  intro hstable hmem
  exact hstable responseName fields hmem

theorem CollectedGroupsResolveStable.tail
    {ObjectIdentity : Type} (schema : Schema)
    (resolvers : Resolvers ObjectIdentity) (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : CollectedGroupsResolveStable schema resolvers variableValues source
        (group :: groups)
      -> CollectedGroupsResolveStable schema resolvers variableValues source groups := by
  intro hstable responseName fields hmem
  exact hstable responseName fields (by simp [hmem])

theorem fieldsInSetCanMerge_executable_runtimeScoped
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection) (responseName : Name)
    (fields : List ExecutableField)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> ExecutableEntriesRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema parentType selectionSet)
          (fields.map (fun field => (responseName, field)))
      -> ExecutableFieldsFieldValidationMergeCompatible fields := by
  intro hmerge hscoped first later hfirst hlater
  rcases hscoped (responseName, first) (by simp [hfirst]) with
    ⟨firstScoped, hfirstScopedMem, hfirstResponse, hfirstMatch, hfirstRuntime⟩
  rcases hscoped (responseName, later) (by simp [hlater]) with
    ⟨laterScoped, hlaterScopedMem, hlaterResponse, hlaterMatch, hlaterRuntime⟩
  rcases hfirstMatch with
    ⟨hfirstField, hfirstArguments, _hfirstSelection⟩
  rcases hlaterMatch with
    ⟨hlaterField, hlaterArguments, _hlaterSelection⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    exact hfirstResponse.trans hlaterResponse.symm
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema firstScoped laterScoped :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hfirstScopedMem
      hlaterScopedMem hscopedResponse
  rcases
      FieldMerge.fieldsForNameCanMerge_identity hfieldMerge
        (ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
          firstScoped laterScoped hfirstRuntime hlaterRuntime) with
    ⟨hfield, hargumentsEquivalent⟩
  constructor
  · rw [← hfirstField, ← hlaterField]
    exact hfield
  · rw [← hfirstArguments, ← hlaterArguments]
    exact hargumentsEquivalent

theorem fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection) (responseName : Name)
    (fields : List ExecutableField)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> ExecutableEntriesRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema parentType selectionSet)
          (fields.map (fun field => (responseName, field)))
      -> ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hmerge hscoped objectType
  apply FieldMerge.fieldsInSetCanMerge_mergedFieldSelectionSet_of_pairwise
  intro first hfirst later hlater
  rcases hscoped (responseName, first) (by simp [hfirst]) with
    ⟨firstScoped, hfirstScopedMem, hfirstResponse, hfirstMatch, hfirstRuntime⟩
  rcases hscoped (responseName, later) (by simp [hlater]) with
    ⟨laterScoped, hlaterScopedMem, hlaterResponse, hlaterMatch, hlaterRuntime⟩
  rcases hfirstMatch with
    ⟨_hfirstField, _hfirstArguments, hfirstSelectionSet⟩
  rcases hlaterMatch with
    ⟨_hlaterField, _hlaterArguments, hlaterSelectionSet⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    exact hfirstResponse.trans hlaterResponse.symm
  have hparents :
      firstScoped.parentType = laterScoped.parentType
        ∨ ¬schema.objectType firstScoped.parentType
        ∨ ¬schema.objectType laterScoped.parentType :=
    ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
      firstScoped laterScoped hfirstRuntime hlaterRuntime
  simpa [hfirstSelectionSet, hlaterSelectionSet]
    using FieldMerge.fieldsInSetCanMerge_pair_subfields schema parentType
      selectionSet firstScoped laterScoped hmerge hfirstScopedMem
      hlaterScopedMem hscopedResponse hparents objectType

theorem collectFields_fieldCompatible_of_canMerge_runtimeScoped
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ExecutableEntriesRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableEntries
            (GraphQL.Execution.collectFields schema variableValues collectParent
              source selectionSet))
      -> CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues collectParent
            source selectionSet) := by
  intro hmerge hscoped
  intro responseName fields hgroup
  apply fieldsInSetCanMerge_executable_runtimeScoped schema validParent
    runtimeType selectionSet responseName fields hmerge
  intro entry hentry
  rcases List.mem_map.mp hentry with ⟨field, hfield, rfl⟩
  exact hscoped (responseName, field)
    (collectedExecutableEntries_mem_of_group_mem hgroup hfield)

theorem collectFields_fieldCompatible_of_canMerge_lookupValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> NormalForm.selectionSetLookupValid schema validParent selectionSet
      -> CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet) := by
  intro hmerge hparentRuntime hlookupValid
  apply collectFields_fieldCompatible_of_canMerge_runtimeScoped
    schema variableValues collectParent validParent runtimeType
    (.object runtimeType identity) selectionSet hmerge
  exact collectFields_entriesRuntimeScopedBy_of_selectionSetLookupValid schema
    variableValues collectParent validParent runtimeType identity selectionSet
    hparentRuntime hlookupValid

end GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
