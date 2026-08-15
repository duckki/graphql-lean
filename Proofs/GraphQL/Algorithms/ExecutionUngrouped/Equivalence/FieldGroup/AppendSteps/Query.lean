import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldGroup.AppendSteps.FlatSpec
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection.SingleFieldGroup.Query

/-!
Root-selection and query wrappers for field-group append steps.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance fieldGroupAppendStepsQueryResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendSteps
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
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
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
    (hsteps
      : ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
          depth parentType source responseName field
          (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source)
          [] fields)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields
        (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source) :=
    ExecutableFieldsMergedComplete_of_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields
      (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source)
      hfieldResponse hfieldParent rfl hfieldLookup
      hfieldChildren
      hsteps
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect hresponse hparent hmerged

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_contained_appendSteps
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
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject
              (resolveFieldValueByName schema resolvers variableValues field.parentType
                field.fieldName field.arguments source)
              runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
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
    (hsteps
      : ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
          variableValues depth parentType source responseName field
          (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source)
          [] fields)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields
        (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source) :=
    ExecutableFieldsMergedComplete_of_contained_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields
      (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source)
      hfieldResponse hfieldParent rfl hfieldLookup hfieldChildren hsteps
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect hresponse hparent hmerged

theorem executeQueryWithFuel_eq_spec_of_exact_nonempty_group_appendSteps
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
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
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
    (hsteps
      : ExecutableFieldsMergedCompleteAppendSteps schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth (operation.rootType schema) source responseName field
          (resolveFieldValueByName schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            field.parentType field.fieldName field.arguments source)
          [] fields)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendSteps
      schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hfieldLookup
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      hsteps

theorem executeQueryWithFuel_eq_spec_of_exact_nonempty_group_contained_appendSteps
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
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject
              (resolveFieldValueByName schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                field.parentType field.fieldName field.arguments source)
              runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
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
    (hsteps
      : ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth (operation.rootType schema) source responseName field
          (resolveFieldValueByName schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            field.parentType field.fieldName field.arguments source)
          [] fields)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_contained_appendSteps
      schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hfieldLookup hfieldChildren hsteps

theorem executeQuery_eq_spec_of_exact_nonempty_group_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound schema operation = depth + 1)
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
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
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
    (hsteps
      : ExecutableFieldsMergedCompleteAppendSteps schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth (operation.rootType schema) source responseName field
          (resolveFieldValueByName schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            field.parentType field.fieldName field.arguments source)
          [] fields)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_exact_nonempty_group_appendSteps schema
      resolvers variableValues operation depth source responseName field fields
      hroot hcollect hdirect hresponse hparent hfieldLookup hfieldChildren
      hsteps

theorem executeQuery_eq_spec_of_exact_nonempty_group_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound schema operation = depth + 1)
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
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject
              (resolveFieldValueByName schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                field.parentType field.fieldName field.arguments source)
              runtimeType identity
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
    (hsteps
      : ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth (operation.rootType schema) source responseName field
          (resolveFieldValueByName schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            field.parentType field.fieldName field.arguments source)
          [] fields)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_exact_nonempty_group_contained_appendSteps
      schema resolvers variableValues operation depth source responseName field
      fields hroot hcollect hdirect hresponse hparent hfieldLookup
      (by
        intro childDepth runtimeType identity hlt hcontains _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt hcontains)
      hsteps

theorem executeRootSelectionSet_eq_spec_of_executedFieldGroup
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
    (group
      : ExecutedFieldGroup schema resolvers variableValues depth parentType
          source responseName field fields)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_mergedComplete
      schema resolvers variableValues depth parentType source selectionSet
      responseName field fields hcollect hdirect group.responseName_eq
      group.parent_eq group.mergedComplete_resolved

theorem executeQueryWithFuel_eq_spec_of_executedFieldGroup
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
    (group
      : ExecutedFieldGroup schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth (operation.rootType schema)
          source responseName field fields)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source operation.selectionSet
      responseName field fields hcollect hdirect group

theorem executeQuery_eq_spec_of_executedFieldGroup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound schema operation = depth + 1)
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
    (group
      : ExecutedFieldGroup schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth (operation.rootType schema)
          source responseName field fields)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_executedFieldGroup schema resolvers
      variableValues operation depth source responseName field fields hroot
      hcollect hdirect group

theorem executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendPlan
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
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
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
    (plan
      : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
          source responseName field
          (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source)
          [] fields)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_appendPlan schema resolvers variableValues depth
        parentType source responseName field fields
        (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source)
        hresponse hparent rfl hfieldLookup
        hfieldChildren
        plan)

theorem executeQueryWithFuel_eq_spec_of_exact_nonempty_group_appendPlan
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
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
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
    (plan
      : ExecutedFieldAppendPlan schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source responseName field
          (resolveFieldValueByName schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            field.parentType field.fieldName field.arguments source)
          [] fields)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_exact_nonempty_group_appendPlan schema
      resolvers (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source
      operation.selectionSet responseName field fields hcollect hdirect
      hresponse hparent hfieldLookup hfieldChildren plan

theorem executeQuery_eq_spec_of_exact_nonempty_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound schema operation = depth + 1)
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
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
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
    (plan
      : ExecutedFieldAppendPlan schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source responseName field
          (resolveFieldValueByName schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            field.parentType field.fieldName field.arguments source)
          [] fields)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_exact_nonempty_group_appendPlan schema
      resolvers variableValues operation depth source responseName field fields
      hroot hcollect hdirect hresponse hparent hfieldLookup
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      plan

theorem executeRootSelectionSet_eq_spec_of_collected_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
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
    (hsteps
      : ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
          depth parentType source responseName field
          (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source)
          [] fields)
    (hexact : groups = [(responseName, field :: fields)])
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_appendSteps schema resolvers
        variableValues depth parentType source [(responseName, field :: fields)]
        responseName field fields hgroup hresponses hparents
        hfieldLookup
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hfieldChildren childDepth runtimeType identity hlt)
        hsteps)

theorem executeQueryWithFuel_eq_spec_of_collected_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema)
          source operation.selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent (operation.rootType schema) groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
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
    (hsteps
      : ExecutableFieldsMergedCompleteAppendSteps schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth (operation.rootType schema) source responseName field
          (resolveFieldValueByName schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            field.parentType field.fieldName field.arguments source)
          [] fields)
    (hexact : groups = [(responseName, field :: fields)])
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_collected_appendSteps schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source operation.selectionSet
      [(responseName, field :: fields)] responseName field fields hcollect
      hgroup hdirect hresponses hparents hfieldLookup hfieldChildren hsteps rfl

theorem executeRootSelectionSet_eq_spec_of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
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
    (plan
      : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
          source responseName field
          (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source)
          [] fields)
    (hexact : groups = [(responseName, field :: fields)])
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_appendPlan schema resolvers
        variableValues depth parentType source [(responseName, field :: fields)]
        responseName field fields hgroup hresponses hparents
        hfieldLookup
        hfieldChildren
        plan)

theorem executeQueryWithFuel_eq_spec_of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema)
          source operation.selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent (operation.rootType schema) groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
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
    (plan
      : ExecutedFieldAppendPlan schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source responseName field
          (resolveFieldValueByName schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            field.parentType field.fieldName field.arguments source)
          [] fields)
    (hexact : groups = [(responseName, field :: fields)])
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  rw [hexact] at hcollect hgroup hresponses hparents
  exact
    executeRootSelectionSet_eq_spec_of_collected_appendPlan schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source operation.selectionSet
      [(responseName, field :: fields)] responseName field fields hcollect
      hgroup hdirect hresponses hparents
      hfieldLookup
      (by
        intro childDepth runtimeType identity hlt _hincludes
        exact hfieldChildren childDepth runtimeType identity hlt)
      plan rfl

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
