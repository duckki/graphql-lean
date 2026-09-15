import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldGroup.AppendSteps
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection.SingleFieldGroup.Executable

/-!
Flat-spec conversions for field-group append-step witnesses.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance fieldGroupAppendStepsFlatSpecResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

structure ExecutedFieldGroup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) where
  resolved : Option (ResolverValue ObjectIdentity)
  resolved_eq
    : resolveFieldValueByName schema resolvers variableValues parentType
        field.fieldName field.arguments source
      = resolved
  headLookup
    : ∃ fieldDefinition,
        schema.lookupField parentType field.fieldName = some fieldDefinition
  headChildren
    : ∀ childDepth runtimeType identity,
        childDepth < depth
        -> schema.typeIncludesObjectBool
              ((schema.fieldReturnType? parentType field.fieldName).getD field.fieldName)
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
            }
  appendSteps
    : ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
        depth parentType source responseName field resolved [] fields

theorem ExecutableFieldsMergedComplete_of_appendSteps_from_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresolveFirst
      : resolveFieldValueByName schema resolvers variableValues parentType
          field.fieldName field.arguments source
        = resolved)
    : (hfieldLookup
        : ∃ fieldDefinition,
            schema.lookupField parentType field.fieldName = some fieldDefinition)
      -> ∀ prefixTail remaining,
          ExecutableFieldsMergedRaw schema resolvers variableValues depth
            parentType source responseName field prefixTail resolved
          -> ExecutableFieldsMergedComplete schema resolvers variableValues depth
              parentType source responseName field prefixTail resolved
          -> ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
              depth parentType source responseName field resolved prefixTail
              remaining
          -> (∀ candidate,
                candidate ∈ prefixTail
                -> ∃ fieldDefinition,
                    schema.lookupField parentType candidate.fieldName
                    = some fieldDefinition)
          -> ExecutableFieldsMergedComplete schema resolvers variableValues depth
              parentType source responseName field (prefixTail ++ remaining)
              resolved
  | _hfieldLookup, prefixTail, [], _hprefixRaw, hprefix, _hsteps,
      _hprefixLookups => by
      simpa using hprefix
  | hfieldLookup, prefixTail, later :: rest, hprefixRaw, hprefix, hsteps,
      hprefixLookups => by
      simp [ExecutableFieldsMergedCompleteAppendSteps] at hsteps
      rcases hsteps with
        ⟨hfieldName, hresolveLater,
          hprefixChildren, hobjects, herrors, hchildren, hrest⟩
      have htailLookups :
          ∀ candidate, candidate ∈ prefixTail ++ [later] ->
            ∃ fieldDefinition, schema.lookupField parentType
              candidate.fieldName = some fieldDefinition := by
        intro candidate hmem
        simp at hmem
        rcases hmem with hprefixMem | hlater
        · exact hprefixLookups candidate hprefixMem
        · subst candidate
          rcases hfieldLookup with ⟨fieldDefinition, hlookup⟩
          exact ⟨fieldDefinition, by simpa [hfieldName] using hlookup⟩
      have hnextRaw :
          ExecutableFieldsMergedRaw schema resolvers variableValues depth
            parentType source responseName field (prefixTail ++ [later])
            resolved :=
        ExecutableFieldsMergedRaw_append_one_of_prefix schema resolvers
          variableValues depth parentType source responseName field prefixTail
          later resolved hprefixRaw hfieldName htailLookups hresolveFirst
          hresolveLater
          (by
            intro childDepth runtimeType identity hlt _hcontains hincludes
            exact hprefixChildren childDepth runtimeType identity hlt hincludes)
          (by
            intro childDepth runtimeType identity hlt _hcontains
            exact hobjects childDepth runtimeType identity hlt)
          (by
            intro childDepth runtimeType identity hlt _hcontains
            exact herrors childDepth runtimeType identity hlt)
          (by
            intro childDepth runtimeType identity hlt _hcontains hincludes
            exact hchildren childDepth runtimeType identity hlt hincludes)
      have hnext :
          ExecutableFieldsMergedComplete schema resolvers variableValues depth
            parentType source responseName field (prefixTail ++ [later])
            resolved :=
        ExecutableFieldsMergedComplete_append_one_of_prefix schema resolvers
          variableValues depth parentType source responseName field prefixTail
          later resolved hprefixRaw hfieldName htailLookups hresolveFirst
          hresolveLater hprefixChildren hobjects herrors hchildren
      have htail :=
        ExecutableFieldsMergedComplete_of_appendSteps_from_prefix schema
          resolvers variableValues depth parentType source responseName field
          resolved hresolveFirst hfieldLookup
          (prefixTail ++ [later]) rest hnextRaw hnext hrest
          htailLookups
      simpa [List.append_assoc] using htail

theorem ExecutableFieldsMergedComplete_of_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresolve
      : resolveFieldValueByName schema resolvers variableValues parentType
          field.fieldName field.arguments source
        = resolved)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType field.fieldName).getD
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
          depth parentType source responseName field resolved [] fields)
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved := by
  have hbase :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field [] resolved :=
    ExecutableFieldsMergedComplete_single_of_guarded_child_states schema resolvers
      variableValues depth parentType source responseName field resolved
      hresolve hfieldChildren
  have hbaseRaw :
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field [] resolved :=
    ExecutableFieldsMergedRaw_single_of_guarded_child_states schema resolvers
      variableValues depth parentType source responseName field resolved
      hresolve hfieldChildren
  simpa using
    ExecutableFieldsMergedComplete_of_appendSteps_from_prefix schema resolvers
      variableValues depth parentType source responseName field resolved
      hresolve hfieldLookup [] fields hbaseRaw hbase hsteps (by simp)

theorem ExecutableFieldsMergedComplete_of_contained_appendSteps_from_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresolveFirst
      : resolveFieldValueByName schema resolvers variableValues parentType
          field.fieldName field.arguments source
        = resolved)
    : (hfieldLookup
        : ∃ fieldDefinition,
            schema.lookupField parentType field.fieldName = some fieldDefinition)
      -> ∀ prefixTail remaining,
          ExecutableFieldsMergedRaw schema resolvers variableValues depth
            parentType source responseName field prefixTail resolved
          -> ExecutableFieldsMergedComplete schema resolvers variableValues depth
              parentType source responseName field prefixTail resolved
          -> ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
              variableValues depth parentType source responseName field resolved
              prefixTail remaining
          -> (∀ candidate,
                candidate ∈ prefixTail
                -> ∃ fieldDefinition,
                    schema.lookupField parentType candidate.fieldName
                    = some fieldDefinition)
          -> ExecutableFieldsMergedComplete schema resolvers variableValues depth
              parentType source responseName field (prefixTail ++ remaining)
              resolved
  | _hfieldLookup, prefixTail, [], _hprefixRaw, hprefix, _hsteps,
      _hprefixLookups => by
      simpa using hprefix
  | hfieldLookup, prefixTail, later :: rest, hprefixRaw, hprefix, hsteps,
      hprefixLookups => by
      simp [ExecutableFieldsMergedCompleteContainedAppendSteps] at hsteps
      rcases hsteps with
        ⟨hfieldName, hresolveLater,
          hprefixChildren, hobjects, herrors, hchildren, hrest⟩
      have htailLookups :
          ∀ candidate, candidate ∈ prefixTail ++ [later] ->
            ∃ fieldDefinition, schema.lookupField parentType
              candidate.fieldName = some fieldDefinition := by
        intro candidate hmem
        simp at hmem
        rcases hmem with hprefixMem | hlater
        · exact hprefixLookups candidate hprefixMem
        · subst candidate
          rcases hfieldLookup with ⟨fieldDefinition, hlookup⟩
          exact ⟨fieldDefinition, by simpa [hfieldName] using hlookup⟩
      have hnextRaw :
          ExecutableFieldsMergedRaw schema resolvers variableValues depth
            parentType source responseName field (prefixTail ++ [later])
            resolved :=
        ExecutableFieldsMergedRaw_append_one_of_prefix schema resolvers
          variableValues depth parentType source responseName field prefixTail
          later resolved hprefixRaw hfieldName htailLookups hresolveFirst
          hresolveLater hprefixChildren hobjects herrors hchildren
      have hnext :
          ExecutableFieldsMergedComplete schema resolvers variableValues depth
            parentType source responseName field (prefixTail ++ [later])
            resolved :=
        ExecutableFieldsMergedComplete_append_one_of_prefix_contained schema
          resolvers variableValues depth parentType source responseName field
          prefixTail later resolved hprefixRaw hfieldName htailLookups
          hresolveFirst hresolveLater hprefixChildren hobjects herrors hchildren
      have htail :=
        ExecutableFieldsMergedComplete_of_contained_appendSteps_from_prefix
          schema resolvers variableValues depth parentType source responseName
          field resolved hresolveFirst hfieldLookup
          (prefixTail ++ [later]) rest hnextRaw hnext hrest
          htailLookups
      simpa [List.append_assoc] using htail

theorem ExecutableFieldsMergedComplete_of_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresolve
      : resolveFieldValueByName schema resolvers variableValues parentType
          field.fieldName field.arguments source
        = resolved)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType field.fieldName).getD
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
          variableValues depth parentType source responseName field resolved []
          fields)
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved := by
  have hbase :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field [] resolved :=
    ExecutableFieldsMergedComplete_single_of_contained_child_states schema
      resolvers variableValues depth parentType source responseName field
      resolved hresolve hfieldChildren
  have hbaseRaw :
      ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field [] resolved :=
    ExecutableFieldsMergedRaw_single_of_contained_child_states schema
      resolvers variableValues depth parentType source responseName field
      resolved hresolve hfieldChildren
  simpa using
    ExecutableFieldsMergedComplete_of_contained_appendSteps_from_prefix schema
      resolvers variableValues depth parentType source responseName field
      resolved hresolve hfieldLookup [] fields hbaseRaw hbase hsteps (by simp)

namespace ExecutedFieldGroup

def of_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresolve
      : resolveFieldValueByName schema resolvers variableValues parentType
          field.fieldName field.arguments source
        = resolved)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType field.fieldName).getD
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
          source responseName field resolved [] fields)
    : ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields where
  resolved := resolved
  resolved_eq := hresolve
  headLookup := hfieldLookup
  headChildren := hfieldChildren
  appendSteps :=
    ExecutedFieldAppendPlan.toAppendSteps schema resolvers variableValues
      depth parentType source responseName field resolved [] fields plan

theorem mergedComplete
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group
      : ExecutedFieldGroup schema resolvers variableValues depth parentType
          source responseName field fields)
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields group.resolved :=
  ExecutableFieldsMergedComplete_of_appendSteps schema resolvers variableValues
    depth parentType source responseName field fields group.resolved
    group.resolved_eq group.headLookup group.headChildren group.appendSteps

theorem mergedComplete_resolved
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group
      : ExecutedFieldGroup schema resolvers variableValues depth parentType
          source responseName field fields)
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields
        (resolveFieldValueByName schema resolvers variableValues parentType
          field.fieldName field.arguments source) := by
  rw [group.resolved_eq]
  exact group.mergedComplete

theorem flatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group
      : ExecutedFieldGroup schema resolvers variableValues depth parentType
          source responseName field fields)
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source responseName (field :: fields) :=
  ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete schema
    resolvers variableValues depth parentType source responseName field fields
    group.resolved group.resolved_eq group.mergedComplete

theorem groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group
      : ExecutedFieldGroup schema resolvers variableValues depth parentType
          source responseName field fields)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableSelections]
  exact group.flatSpecEquivalent

end ExecutedFieldGroup

def ExecutedFieldGroups
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : List (Name × List ExecutableField) -> Type
  | [] => Unit
  | (_responseName, []) :: _rest => Empty
  | (responseName, field :: fields) :: rest =>
      ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields
      × ExecutedFieldGroups schema resolvers variableValues depth parentType source rest

def ExecutedFieldGroups.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    : ExecutedFieldGroups schema resolvers variableValues depth parentType source [] :=
  ()

def ExecutedFieldGroups.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)}
    (hgroup
      : ExecutedFieldGroup schema resolvers variableValues depth parentType source
          responseName field fields)
    (hrest
      : ExecutedFieldGroups schema resolvers variableValues depth parentType source rest)
    : ExecutedFieldGroups schema resolvers variableValues depth parentType source
        ((responseName, field :: fields) :: rest) :=
  (hgroup, hrest)

def ExecutedFieldGroups.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (hgroup
      : ExecutedFieldGroup schema resolvers variableValues depth parentType source
          responseName field fields)
    : ExecutedFieldGroups schema resolvers variableValues depth parentType source
        [(responseName, field :: fields)] :=
  ExecutedFieldGroups.cons hgroup ExecutedFieldGroups.nil

theorem ExecutedFieldGroups.no_empty_head
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {rest : List (Name × List ExecutableField)}
    : ExecutedFieldGroups schema resolvers variableValues depth parentType source
        ((responseName, []) :: rest)
      -> False := by
  intro hgroups
  exact nomatch hgroups

def ExecutedFieldGroups.head
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)}
    : ExecutedFieldGroups schema resolvers variableValues depth parentType source
        ((responseName, field :: fields) :: rest)
      -> ExecutedFieldGroup schema resolvers variableValues depth parentType source
          responseName field fields :=
  fun hgroups => hgroups.1

def ExecutedFieldGroups.tail
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)}
    : ExecutedFieldGroups schema resolvers variableValues depth parentType source
        ((responseName, field :: fields) :: rest)
      -> ExecutedFieldGroups schema resolvers variableValues depth parentType source
          rest :=
  fun hgroups => hgroups.2

theorem ExecutedFieldGroups.nil_groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [] :=
  ExecutableGroupsFlatSpecEquivalent_nil schema resolvers variableValues
    (depth + 1) parentType source

theorem ExecutedFieldGroups.head_groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)}
    (hgroups
      : ExecutedFieldGroups schema resolvers variableValues depth parentType source
          ((responseName, field :: fields) :: rest))
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [(responseName, field :: fields)] :=
  (ExecutedFieldGroups.head hgroups).groupFlatSpecEquivalent

def ExecutedFieldGroup.of_collected_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType field.fieldName).getD
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
          (resolveFieldValueByName schema resolvers variableValues parentType
            field.fieldName field.arguments source)
          [] fields)
    : ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields where
  resolved :=
    resolveFieldValueByName schema resolvers variableValues parentType
      field.fieldName field.arguments source
  resolved_eq := rfl
  headLookup := hfieldLookup
  headChildren := hfieldChildren
  appendSteps := hsteps

def ExecutedFieldGroup.of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType field.fieldName).getD
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
          (resolveFieldValueByName schema resolvers variableValues parentType
            field.fieldName field.arguments source)
          [] fields)
    : ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields :=
  ExecutedFieldGroup.of_collected_appendSteps schema resolvers variableValues
    depth parentType source responseName field fields hfieldLookup hfieldChildren
    (ExecutedFieldAppendPlan.toAppendSteps schema resolvers variableValues
      depth parentType source responseName field
      (resolveFieldValueByName schema resolvers variableValues parentType
        field.fieldName field.arguments source)
      [] fields plan)

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresolve
      : resolveFieldValueByName schema resolvers variableValues parentType
          field.fieldName field.arguments source
        = resolved)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType field.fieldName).getD
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
          depth parentType source responseName field resolved [] fields)
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source responseName (field :: fields) := by
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved :=
    ExecutableFieldsMergedComplete_of_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields resolved
      hresolve hfieldLookup hfieldChildren hsteps
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresolve
      : resolveFieldValueByName schema resolvers variableValues parentType
          field.fieldName field.arguments source
        = resolved)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType field.fieldName).getD
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
          depth parentType source responseName field resolved [] fields)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableSelections]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_appendSteps
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresolve hfieldLookup hfieldChildren hsteps

theorem ExecutableGroupsFlatSpecEquivalent_collected_nonempty_group_of_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
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
          (resolveFieldValueByName schema resolvers variableValues parentType
            field.fieldName field.arguments source)
          [] fields)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [(responseName, field :: fields)] := by
  exact ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_appendSteps
    schema resolvers variableValues depth parentType source responseName
    field fields
    (resolveFieldValueByName schema resolvers variableValues parentType
      field.fieldName field.arguments source)
    rfl hfieldLookup
    (by
      intro childDepth runtimeType identity hlt _hincludes
      exact hfieldChildren childDepth runtimeType identity hlt)
    hsteps

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_contained_appendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresolve
      : resolveFieldValueByName schema resolvers variableValues parentType
          field.fieldName field.arguments source
        = resolved)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType field.fieldName).getD
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
          variableValues depth parentType source responseName field resolved []
          fields)
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source responseName (field :: fields) := by
  have hmerged :
      ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved :=
    ExecutableFieldsMergedComplete_of_contained_appendSteps schema resolvers
      variableValues depth parentType source responseName field fields resolved
      hresolve hfieldLookup hfieldChildren hsteps
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_contained_appendSteps
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresolve
      : resolveFieldValueByName schema resolvers variableValues parentType
          field.fieldName field.arguments source
        = resolved)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType field.fieldName).getD
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
          variableValues depth parentType source responseName field resolved []
          fields)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableSelections]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_contained_appendSteps
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresolve hfieldLookup hfieldChildren hsteps

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
