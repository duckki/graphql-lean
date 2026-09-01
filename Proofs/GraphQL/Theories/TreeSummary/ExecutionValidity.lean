import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.TreeSoundness.Invariants
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection.StateInvariant

/-! Validation facts shared by TreeSummary execution-soundness proofs. -/

namespace GraphQL
namespace TreeSummary

open GraphQL.Execution
open GraphQL.Algorithms.ExecutionUngroupedUncached.Eager

/-- Validation facts retained for the children of one concrete response-name group. -/
def ExecutableFieldsChildrenValid (schema : Schema) (fields : List ExecutableField)
    : Prop :=
  ∀ first definition childRuntime,
    first ∈ fields
    -> schema.lookupField first.parentType first.fieldName = some definition
    -> schema.typeIncludesObjectBool definition.outputType.namedType childRuntime = true
    -> schema.objectType childRuntime
        ∧ NormalForm.selectionSetSemanticsReady schema childRuntime
            (Execution.mergedFieldSelectionSet fields)
        ∧ FieldMerge.fieldsInSetCanMerge schema childRuntime
            (Execution.mergedFieldSelectionSet fields)

/-- Field-merging and argument-validity facts retained recursively for collected runtime
groups. Named fields keep the recursive soundness proofs independent of conjunction
nesting. -/
structure ExecutableFieldGroupValid (schema : Schema) (fields : List ExecutableField)
    : Prop where
  mergeCompatible : ExecutableFieldsFieldValidationMergeCompatible fields
  childrenValid : ExecutableFieldsChildrenValid schema fields
  argumentsNodup : ExecutableFieldsArgumentsNodup fields
  childArgumentsNodup
    : ∀ field, field ∈ fields -> selectionSetArgumentsNodup field.selectionSet

def ExecutableGroupsValid (schema : Schema) (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups -> ExecutableFieldGroupValid schema fields

theorem collectFields_executableGroupsValid
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name) (ref : ObjectRef) (selectionSet : List Selection)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hobject : schema.objectType runtimeType)
    (hready : NormalForm.selectionSetSemanticsReady schema runtimeType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema runtimeType selectionSet)
    (harguments : selectionSetArgumentsNodup selectionSet)
    : ExecutableGroupsValid schema
        (collectFields schema variableValues runtimeType (.object runtimeType ref)
          selectionSet) := by
  let source : ResolverValue ObjectRef := .object runtimeType ref
  let groups := collectFields schema variableValues runtimeType source selectionSet
  have hself : ScopedParentRuntimeApplies schema runtimeType runtimeType := by
    exact NormalForm.object_typeIncludesObjectBool_self schema hobject
  have hlookupValid :
      NormalForm.selectionSetLookupValid schema runtimeType selectionSet :=
    NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet hready
  intro responseName fields hgroup
  have hcompatible : ExecutableFieldsFieldValidationMergeCompatible fields := by
    have hall := collectFields_fieldCompatible_of_canMerge_lookupValid_object schema
      variableValues runtimeType runtimeType runtimeType ref selectionSet hmerge hself
      hlookupValid
    exact hall responseName fields (by simpa [groups, source] using hgroup)
  have hargumentFacts := collectFields_argumentsAndChildrenNodup schema variableValues
    runtimeType source selectionSet harguments
  exact {
    mergeCompatible := hcompatible
    childrenValid := by
      intro first definition childRuntime hfirst hlookup hinclude
      have hchildScoped :
          ScopedParentRuntimeApplies schema childRuntime definition.outputType.namedType :=
        ScopedParentRuntimeApplies.of_typeIncludesObjectBool schema childRuntime
          definition.outputType.namedType hinclude
      have hchildObject : schema.objectType childRuntime :=
        ScopedParentRuntimeApplies.runtimeObjectType schema hschema hchildScoped
      refine ⟨hchildObject, ?_, ?_⟩
      · exact
          Algorithms.ExecutionUngrouped.collectedGroup_mergedFieldSelectionSet_semanticsReady
            schema variableValues runtimeType runtimeType ref selectionSet responseName
            fields first definition childRuntime hobject hself hready hmerge
            (by simpa [groups, source] using hgroup) hfirst hlookup hinclude
      · exact Algorithms.ExecutionUngrouped.collectedGroup_mergedFieldSelectionSet_canMerge
          schema variableValues runtimeType runtimeType ref selectionSet responseName fields
          hmerge hself hlookupValid (by simpa [groups, source] using hgroup) childRuntime
    argumentsNodup :=
      hargumentFacts.1 responseName fields (by simpa [groups, source] using hgroup)
    childArgumentsNodup := by
      intro field hfield
      exact hargumentFacts.2 field
        (collectedExecutableFields_mem_of_group_mem
          (by simpa [groups, source] using hgroup) hfield)
  }

end TreeSummary
end GraphQL
