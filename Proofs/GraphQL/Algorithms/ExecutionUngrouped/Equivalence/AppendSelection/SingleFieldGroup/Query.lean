import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection.SingleFieldGroup.Executable

/-!
Root-selection and query wrappers for exact single-field groups.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_merged_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = [(responseName, field :: fields)])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate, candidate ∈ field :: fields -> candidate.parentType = parentType)
    (hungrouped
      : executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source (executableFieldSelections (field :: fields))
        = GraphQL.Execution.executeField schema resolvers variableValues
            (depth + 1) source responseName (field :: fields))
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  have hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) := by
    rw [hcollect]
    exact
      ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_merged_complete
        schema resolvers variableValues depth parentType source responseName
        field fields
        (resolveFieldValueByName schema resolvers variableValues field.parentType
          field.fieldName field.arguments source)
        hresponse hparent rfl hungrouped
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues (depth + 1) parentType source
      selectionSet hdirect hgroups

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = [(responseName, field :: fields)])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate, candidate ∈ field :: fields -> candidate.parentType = parentType)
    (hmerged
      : ExecutableFieldsMergedComplete schema resolvers variableValues depth
          parentType source responseName field fields
          (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source))
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  unfold ExecutableFieldsMergedComplete at hmerged
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_merged_complete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect hresponse hparent hmerged

theorem executeQueryWithFuel_eq_spec_of_exact_nonempty_group_merged_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema)
          source operation.selectionSet
        = [(responseName, field :: fields)])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate,
          candidate ∈ field :: fields
          -> candidate.parentType = (operation.rootType schema))
    (hungrouped
      : executeRootSelectionSet schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source
          (executableFieldSelections (field :: fields))
        = GraphQL.Execution.executeField schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            (depth + 1) source responseName (field :: fields))
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_merged_complete
      schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hungrouped

theorem executeQueryWithFuel_eq_spec_of_exact_nonempty_group_mergedComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema)
          source operation.selectionSet
        = [(responseName, field :: fields)])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate,
          candidate ∈ field :: fields
          -> candidate.parentType = (operation.rootType schema))
    (hmerged
      : ExecutableFieldsMergedComplete schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source responseName field fields
          (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source))
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hmerged

theorem executeQuery_eq_spec_of_exact_nonempty_group_merged_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema)
          source operation.selectionSet
        = [(responseName, field :: fields)])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate,
          candidate ∈ field :: fields
          -> candidate.parentType = (operation.rootType schema))
    (hungrouped
      : executeRootSelectionSet schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source
          (executableFieldSelections (field :: fields))
        = GraphQL.Execution.executeField schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            (depth + 1) source responseName (field :: fields))
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_exact_nonempty_group_merged_complete
      schema resolvers variableValues operation depth source responseName field
      fields hroot hcollect hdirect hresponse hparent hungrouped

theorem executeQuery_eq_spec_of_exact_nonempty_group_mergedComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema)
          source operation.selectionSet
        = [(responseName, field :: fields)])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate,
          candidate ∈ field :: fields
          -> candidate.parentType = (operation.rootType schema))
    (hmerged
      : ExecutableFieldsMergedComplete schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source responseName field fields
          (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source))
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues operation depth source responseName field
      fields hroot hcollect hdirect hresponse hparent hmerged

theorem executeRootSelectionSet_eq_spec_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = [(responseName, [field])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hparent : field.parentType = parentType)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  have hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) := by
    rw [hcollect]
    exact
      ExecutableGroupsFlatSpecEquivalent_single_field_group_of_child_states
        schema resolvers variableValues depth parentType responseName source
        field hparent hchildren
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues (depth + 1) parentType source
      selectionSet hdirect hgroups

theorem stateEquivalent_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = [(responseName, [field])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hparent : field.parentType = parentType)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth + 1
              parentType := parentType
              source := source
              selectionSet := selectionSet
            }
          initial := .object []
        } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (depth + 1) parentType source selectionSet
    (executeRootSelectionSet_eq_spec_of_exact_single_field_group schema
      resolvers variableValues depth parentType source selectionSet
      responseName field hcollect hdirect hparent hchildren)

theorem stateEquivalent_of_collected_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, [field]) ∈ groups)
    (hexact : groups = [(responseName, [field])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth + 1
              parentType := parentType
              source := source
              selectionSet := selectionSet
            }
          initial := .object []
        } := by
  let state : ExecutionEquivalenceState ObjectIdentity :=
    { window :=
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := parentType
        source := source
        selectionSet := selectionSet }
      initial := .object [] }
  have hparents : CollectedGroupsParent parentType groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups
        hcollect
  have hparent : field.parentType = parentType :=
    (hparents responseName [field] hgroup) field (by simp)
  exact
    stateEquivalent_of_exact_single_field_group schema resolvers
      variableValues depth parentType source selectionSet responseName field
      (by simpa [hexact] using hcollect) hdirect hparent hchildren

theorem executeQueryWithFuel_eq_spec_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema)
          source operation.selectionSet
        = [(responseName, [field])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hparent : field.parentType = (operation.rootType schema))
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact stateEquivalent_of_exact_single_field_group schema resolvers
    (GraphQL.Execution.coerceVariableValues operation variableValues)
    depth (operation.rootType schema) source operation.selectionSet
    responseName field hcollect hdirect hparent hchildren

theorem executeQuery_eq_spec_of_exact_single_field_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema)
          source operation.selectionSet
        = [(responseName, [field])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hparent : field.parentType = (operation.rootType schema))
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact executeQueryWithFuel_eq_spec_of_exact_single_field_group schema
    resolvers variableValues operation depth source responseName field hroot
    hcollect hdirect hparent hchildren

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
