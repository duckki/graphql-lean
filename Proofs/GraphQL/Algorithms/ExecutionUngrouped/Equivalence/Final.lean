import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList.AppendInvariant
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList.DepthZero

/-!
Final proof-boundary statements for ungrouped execution equivalence.

The main public bridge derives spec equivalence from the collected-field invariants
and a proof that each collected group can append its duplicate-field slices.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

def CollectedSelectionSetGroupsSingleton
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : Prop :=
  ∀ responseName fields,
    (responseName, fields)
      ∈ GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
    -> fields.length = 1

structure ExecutedGroupedSelectionSetState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : Type where
  groups : List (Name × List ExecutableField)
  collect_eq
    : GraphQL.Execution.collectFields schema variableValues parentType source selectionSet
      = groups
  flatCollects
    : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source selectionSet (.object [])
  flatSpec
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
        parentType source groups

structure ExecutedGroupedSelectionSetAlignedState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : Type where
  groups : List (Name × List ExecutableField)
  collect_eq
    : GraphQL.Execution.collectFields schema variableValues parentType source selectionSet
      = groups
  flatCollects
    : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source selectionSet (.object [])
  flatSpec
    : ExecutableGroupsFlatSpecAlignedEquivalent schema resolvers variableValues
        depth parentType source groups

namespace ExecutedGroupedSelectionSetState

theorem visitSubfieldsResult_eq_spec_of_executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hroot
      : executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet
        = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
            depth parentType source selectionSet)
    : ExecutionWindow.visitSubfieldsResult schema resolvers variableValues depth
        parentType source selectionSet (.object [])
      = match GraphQL.Execution.executeSelectionSet schema resolvers variableValues
                depth parentType source selectionSet with
        | .error errors => .error errors
        | .ok (fields, errors) => .ok (.object fields, errors) := by
  rw [visitSubfieldsResult_empty_eq_executeRootSelectionSet_object]
  rw [hroot]
  rfl

theorem executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedGroupedSelectionSetState schema resolvers variableValues depth
          parentType source selectionSet)
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet := by
  apply executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
    schema resolvers variableValues depth parentType source selectionSet
    state.flatCollects
  rw [state.collect_eq]
  exact state.flatSpec

theorem visitSubfieldsResult_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedGroupedSelectionSetState schema resolvers variableValues depth
          parentType source selectionSet)
    : ExecutionWindow.visitSubfieldsResult schema resolvers variableValues depth
        parentType source selectionSet (.object [])
      = match GraphQL.Execution.executeSelectionSet schema resolvers variableValues
                depth parentType source selectionSet with
        | .error errors => .error errors
        | .ok (fields, errors) => .ok (.object fields, errors) :=
  visitSubfieldsResult_eq_spec_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source selectionSet
    state.executeRootSelectionSet_eq_spec

theorem stateEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedGroupedSelectionSetState schema resolvers variableValues depth
          parentType source selectionSet)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := selectionSet
            }
          initial := .object []
        } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source selectionSet
    state.executeRootSelectionSet_eq_spec

def depth_zero_general
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : ExecutedGroupedSelectionSetState schema resolvers variableValues 0
        parentType source selectionSet :=
  {
    groups :=
      GraphQL.Execution.collectFields schema variableValues parentType source selectionSet
    collect_eq := rfl
    flatCollects :=
      VisitSubfieldsFlatCollects_depth_zero schema resolvers variableValues
        parentType source selectionSet [] ResponseMergeReady_empty_object
    flatSpec :=
      ExecutableGroupsFlatSpecEquivalent_depth_zero_general schema resolvers
        variableValues parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)
        (PairKeysNodup_of_executableGroupNamesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source selectionSet))
        (collectFields_fieldsNonempty schema variableValues parentType source
          selectionSet)
        (collectFields_responseName schema variableValues parentType source selectionSet)
        (collectFields_parent schema variableValues parentType source selectionSet)
  }

def depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (_hsingletons
      : CollectedSelectionSetGroupsSingleton schema variableValues parentType
          source selectionSet)
    : ExecutedGroupedSelectionSetState schema resolvers variableValues 0
        parentType source selectionSet :=
  depth_zero_general schema resolvers variableValues parentType source selectionSet

def of_empty_collect
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = [])
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
          source selectionSet (.object []))
    : ExecutedGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet :=
  {
    groups := []
    collect_eq := hcollect
    flatCollects := hflat
    flatSpec :=
      ExecutableGroupsFlatSpecEquivalent_nil schema resolvers variableValues
        depth parentType source
  }

def of_group_flat_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
          source selectionSet (.object []))
    (hgroups
      : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
          parentType source groups)
    : ExecutedGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet :=
  {
    groups := groups
    collect_eq := hcollect
    flatCollects := hflat
    flatSpec := hgroups
  }

def of_executedGroups
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hgroups
      : ExecutedFieldGroups schema resolvers variableValues depth parentType
          source groups)
    (hnodup : PairKeysNodup groups)
    : ExecutedGroupedSelectionSetState schema resolvers variableValues
        (depth + 1) parentType source selectionSet :=
  {
    groups := groups
    collect_eq := hcollect
    flatCollects := hflat
    flatSpec := ExecutedFieldGroups.groupFlatSpecEquivalent hgroups hnodup
  }

def of_collected_groups_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hplanStates
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ExecutedFieldAppendPlanState schema resolvers variableValues depth
              field fields [] fields)
    : ExecutedGroupedSelectionSetState schema resolvers variableValues
        (depth + 1) parentType source selectionSet := by
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
  have hnonempty : CollectedGroupsFieldsNonempty groups := by
    rw [← hcollect]
    exact collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet
  have hresponses : CollectedGroupsResponseName groups :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq state groups
      hcollect
  have hparents : CollectedGroupsParent parentType groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups
        hcollect
  have hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.resolveStable_of_collect_eq state groups
        hinvariant hcollect
  have hnodup : PairKeysNodup groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.pairKeysNodup_of_collect_eq state
        groups hinvariant hcollect
  exact
    of_executedGroups hcollect hflat
        (ExecutedFieldGroups.of_collected_groups_state schema resolvers
          variableValues depth parentType source groups hnonempty hresponses
          hparents hlookups hcompatible hstable hplanStates)
      hnodup

def of_collected_groups_appendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend : FieldGroupAppendInvariant schema resolvers variableValues depth)
    : ExecutedGroupedSelectionSetState schema resolvers variableValues
        (depth + 1) parentType source selectionSet :=
  of_collected_groups_state hcollect hflat hcollected hlookups hcompatible
    (by
      intro _responseName field fields _hmem
      exact ExecutedFieldAppendPlanState.of_appendInvariant happend field
        fields)

def of_collected_groups_collectedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupAppendInvariant schema resolvers variableValues depth groups)
    : ExecutedGroupedSelectionSetState schema resolvers variableValues
        (depth + 1) parentType source selectionSet :=
  of_collected_groups_state hcollect hflat hcollected hlookups hcompatible
    (by
      intro responseName field fields hgroup
      exact
        ExecutedFieldAppendPlanState.of_collectedAppendInvariant happend
          responseName field fields hgroup)

def of_collected_groups_collectedLocalAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
          depth groups)
    : ExecutedGroupedSelectionSetState schema resolvers variableValues
        (depth + 1) parentType source selectionSet :=
  of_collected_groups_state hcollect hflat hcollected hlookups hcompatible
    (by
      intro responseName field fields hgroup
      exact
        ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant happend
          responseName field fields hgroup)

end ExecutedGroupedSelectionSetState

namespace ExecutedGroupedSelectionSetAlignedState

theorem executeRootSelectionSet_aligned
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedGroupedSelectionSetAlignedState schema resolvers variableValues
          depth parentType source selectionSet)
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues depth parentType source selectionSet) := by
  apply executeRootSelectionSet_aligned_of_flatCollects_and_groupFlatSpecAligned
    schema resolvers variableValues depth parentType source selectionSet
    state.flatCollects
  rw [state.collect_eq]
  exact state.flatSpec

theorem executeRootSelectionSet_responseEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedGroupedSelectionSetAlignedState schema resolvers variableValues
          depth parentType source selectionSet)
    : RootSelectionResultDataAndErrorPresenceEquivalent
        (executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues depth parentType source selectionSet) :=
  RootSelectionResultAlignedEquivalent.to_dataAndErrorPresence
    state.executeRootSelectionSet_aligned

def of_group_flat_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
          source selectionSet (.object []))
    (hgroups
      : ExecutableGroupsFlatSpecAlignedEquivalent schema resolvers variableValues
          depth parentType source groups)
    : ExecutedGroupedSelectionSetAlignedState schema resolvers variableValues depth
        parentType source selectionSet :=
  {
    groups := groups
    collect_eq := hcollect
    flatCollects := hflat
    flatSpec := hgroups
  }

def of_exact
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedGroupedSelectionSetState schema resolvers variableValues depth
          parentType source selectionSet)
    : ExecutedGroupedSelectionSetAlignedState schema resolvers variableValues
        depth parentType source selectionSet :=
  {
    groups := state.groups
    collect_eq := state.collect_eq
    flatCollects := state.flatCollects
    flatSpec :=
      ExecutableGroupsFlatSpecAlignedEquivalent.of_exact state.flatSpec
  }

def of_executedGroups
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hgroups
      : ExecutedFieldGroups schema resolvers variableValues depth parentType
          source groups)
    (hnodup : PairKeysNodup groups)
    : ExecutedGroupedSelectionSetAlignedState schema resolvers variableValues
        (depth + 1) parentType source selectionSet :=
  {
    groups := groups
    collect_eq := hcollect
    flatCollects := hflat
    flatSpec :=
      ExecutedFieldGroups.groupFlatSpecAlignedEquivalent hgroups hnodup
  }

end ExecutedGroupedSelectionSetAlignedState

structure CollectedFieldGroupRecursiveAppendState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (groups : List (Name × List ExecutableField))
    : Type where
  prefixChildren
    : ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> ∀ childDepth runtimeType identity,
            childDepth < depth
            -> schema.typeIncludesObjectBool
                  ((schema.fieldReturnType? field.parentType field.fieldName).getD
                    field.fieldName)
                  runtimeType
                = true
            -> ExecutedGroupedSelectionSetState schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
  errorNeutral
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> later ∈ fields
        -> ∀ childDepth runtimeType identity,
            childDepth < depth
            -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                  (.object [])).fst

namespace CollectedFieldGroupRecursiveAppendState

def depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (groups : List (Name × List ExecutableField))
    : CollectedFieldGroupRecursiveAppendState schema resolvers variableValues 0 groups :=
  {
    prefixChildren := by
      intro _responseName _field _fields _prefixTail _hgroup _hprefix
        childDepth _runtimeType _identity hlt _hincludes
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    errorNeutral := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt)
  }

theorem localAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (state
      : CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
          depth groups)
    : CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
        depth groups :=
  {
    prefixChildren := by
      intro responseName field fields prefixTail hgroup hprefix childDepth
        runtimeType identity hlt hincludes
      exact (state.prefixChildren responseName field fields prefixTail hgroup
              hprefix childDepth runtimeType identity hlt
              hincludes).stateEquivalent
    errorNeutral := state.errorNeutral
  }

end CollectedFieldGroupRecursiveAppendState

structure CollectedFieldGroupRecursiveAlignedAppendState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : Type where
  prefixChildren
    : ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> ∀ childDepth runtimeType identity,
            childDepth < completionDepth + 1
            -> ValueContainsObject
                (resolveFieldValueByName schema resolvers variableValues field.parentType
                  field.fieldName field.arguments source)
                runtimeType identity
            -> schema.typeIncludesObjectBool
                  ((schema.fieldReturnType? field.parentType field.fieldName).getD
                    field.fieldName)
                  runtimeType
                = true
            -> ExecutedGroupedSelectionSetAlignedState schema resolvers variableValues
                childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
  absorbs
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> later ∈ fields
        -> ∀ childDepth runtimeType identity,
            childDepth < completionDepth + 1
            -> ValueContainsObject
                (resolveFieldValueByName schema resolvers variableValues field.parentType
                  field.fieldName field.arguments source)
                runtimeType identity
            -> ResponseAbsorbs
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                  (.object [])).fst
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])).fst).fst

namespace CollectedFieldGroupRecursiveAlignedAppendState

theorem alignedAppendSteps_from_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (state
      : CollectedFieldGroupRecursiveAlignedAppendState schema resolvers
          variableValues completionDepth source groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail remaining : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hprefix : ∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
    (hremaining : ∀ candidate, candidate ∈ remaining -> candidate ∈ fields)
    : ExecutableFieldsMergedAlignedAppendSteps schema resolvers variableValues
        (completionDepth + 1) parentType source responseName field
        (resolveFieldValueByName schema resolvers variableValues field.parentType
          field.fieldName field.arguments source)
        prefixTail remaining := by
  cases remaining with
  | nil =>
      simp [ExecutableFieldsMergedAlignedAppendSteps]
  | cons later rest =>
      have hlater : later ∈ fields := hremaining later (by simp)
      have hgroupResponses :
          ExecutableFieldsResponseName responseName (field :: fields) :=
        hresponses responseName (field :: fields) hgroup
      have hgroupParents :
          ExecutableFieldsParent parentType (field :: fields) :=
        hparents responseName (field :: fields) hgroup
      have hgroupCompatible :
          ExecutableFieldsFieldValidationMergeCompatible (field :: fields) :=
        hcompatible responseName (field :: fields) hgroup
      have hgroupStable :
          ExecutableFieldsResolveStable schema resolvers variableValues source (field :: fields) :=
        hstable responseName (field :: fields) hgroup
      have hfieldResponse : field.responseName = responseName :=
        hgroupResponses field (by simp)
      have hlaterResponse : later.responseName = responseName :=
        hgroupResponses later (List.mem_cons_of_mem field hlater)
      have hlaterParent : later.parentType = parentType :=
        hgroupParents later (List.mem_cons_of_mem field hlater)
      have hsameResponse : field.responseName = later.responseName := by
        rw [hfieldResponse, hlaterResponse]
      have hfieldName : later.fieldName = field.fieldName :=
        (hgroupCompatible field later (by simp)
          (List.mem_cons_of_mem field hlater) hsameResponse).1.symm
      have hresolveLater :
          resolveFieldValueByName schema resolvers variableValues later.parentType later.fieldName later.arguments source =
          resolveFieldValueByName schema resolvers variableValues field.parentType field.fieldName field.arguments source :=
        (hgroupStable field later (by simp)
          (List.mem_cons_of_mem field hlater) hsameResponse).symm
      have hprefixNext :
          ∀ candidate, candidate ∈ prefixTail ++ [later] ->
            candidate ∈ fields := by
        intro candidate hcandidate
        rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
        · exact hprefix candidate hprefixMem
        · rcases List.mem_singleton.mp hlaterMem
          exact hlater
      have hremainingRest :
          ∀ candidate, candidate ∈ rest -> candidate ∈ fields := by
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])
      simp [ExecutableFieldsMergedAlignedAppendSteps]
      exact ⟨
        hlaterResponse,
        hlaterParent,
        hfieldName,
        hresolveLater,
        (by
          intro childDepth runtimeType identity hlt hcontains hincludes
          exact (state.prefixChildren responseName field fields prefixTail hgroup
                  hprefix childDepth runtimeType identity hlt hcontains
                  hincludes).executeRootSelectionSet_aligned),
        (by
          intro childDepth runtimeType identity hlt hcontains
          exact state.absorbs responseName field fields prefixTail later hgroup
            hprefix hlater childDepth runtimeType identity hlt hcontains),
        (by
          intro childDepth runtimeType identity hlt hcontains hincludes
          exact (state.prefixChildren responseName field fields
                  (prefixTail ++ [later]) hgroup hprefixNext childDepth
                  runtimeType identity hlt hcontains
                  hincludes).executeRootSelectionSet_aligned),
        alignedAppendSteps_from_prefix state hresponses hparents hcompatible
          hstable responseName field fields (prefixTail ++ [later]) rest
          hgroup hprefixNext hremainingRest
      ⟩

theorem alignedAppendSteps
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (state
      : CollectedFieldGroupRecursiveAlignedAppendState schema resolvers
          variableValues completionDepth source groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    : ExecutableFieldsMergedAlignedAppendSteps schema resolvers variableValues
        (completionDepth + 1) parentType source responseName field
        (resolveFieldValueByName schema resolvers variableValues field.parentType
          field.fieldName field.arguments source)
        [] fields :=
  alignedAppendSteps_from_prefix state hresponses hparents hcompatible hstable
    responseName field fields [] fields hgroup
    (by intro candidate hmem; simp at hmem)
    (by intro candidate hmem; exact hmem)

end CollectedFieldGroupRecursiveAlignedAppendState

def
    ExecutedGroupedSelectionSetAlignedState.of_collected_groups_recursiveAlignedAppendState
    {ObjectIdentity : Type} {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity} {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues
          (completionDepth + 2) parentType source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := completionDepth + 1
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupRecursiveAlignedAppendState schema resolvers
          variableValues completionDepth source groups)
    : ExecutedGroupedSelectionSetAlignedState schema resolvers variableValues
        (completionDepth + 2) parentType source selectionSet := by
  let state :
      ExecutionEquivalenceState ObjectIdentity :=
    { window :=
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := completionDepth + 1
        parentType := parentType
        source := source
        selectionSet := selectionSet }
      initial := .object [] }
  have hresponses : CollectedGroupsResponseName groups :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq state groups
      hcollect
  have hparents : CollectedGroupsParent parentType groups :=
    ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups hcollect
  have hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups :=
    ExecutionCollectedFieldInvariant.resolveStable_of_collect_eq state groups
      hcollected hcollect
  have hnodup : PairKeysNodup groups :=
    ExecutionCollectedFieldInvariant.pairKeysNodup_of_collect_eq state groups
      hcollected hcollect
  have hnonempty : CollectedGroupsFieldsNonempty groups := by
    rw [← hcollect]
    exact collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet
  refine
    ExecutedGroupedSelectionSetAlignedState.of_group_flat_spec
      hcollect hflat ?_
  exact
    ExecutableGroupsFlatSpecAlignedEquivalent_of_alignedAppendSteps_positive
      schema resolvers variableValues completionDepth parentType source groups
      hnonempty hresponses hparents hlookups
      (by
        intro responseName field fields hgroup childDepth runtimeType identity hlt
          hcontains hincludes
        have hchild :=
          happend.prefixChildren responseName field fields [] hgroup
            (by intro candidate hmem; simp at hmem) childDepth runtimeType
            identity hlt hcontains hincludes
        simpa [GraphQL.Execution.mergedFieldSelectionSet] using
          hchild.executeRootSelectionSet_aligned)
      (by
        intro responseName field fields hgroup
        exact
          CollectedFieldGroupRecursiveAlignedAppendState.alignedAppendSteps
            happend hresponses hparents hcompatible hstable responseName field
            fields hgroup)
      hnodup

def ExecutedGroupedSelectionSetState.of_collected_groups_recursiveAppendState
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
          depth groups)
    : ExecutedGroupedSelectionSetState schema resolvers variableValues
        (depth + 1) parentType source selectionSet :=
  ExecutedGroupedSelectionSetState.of_collected_groups_collectedLocalAppendInvariant
    hcollect hflat hcollected hlookups hcompatible
    happend.localAppendInvariant

structure RecursiveGroupedSelectionSetState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : Type where
  groups : List (Name × List ExecutableField)
  collect_eq
    : GraphQL.Execution.collectFields schema variableValues parentType source selectionSet
      = groups
  flatCollects
    : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object [])
  collected
    : ExecutionCollectedFieldInvariant
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := selectionSet
            }
          initial := .object []
        }
  lookups : CollectedGroupsFieldLookupValid schema parentType groups
  compatible : CollectedGroupsFieldValidationMergeCompatible groups
  recursiveAppend
    : CollectedFieldGroupRecursiveAppendState schema resolvers variableValues depth groups

namespace RecursiveGroupedSelectionSetState

def of_allOutputs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues
          (depth + 1) parentType source selectionSet)
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
          depth groups)
    : RecursiveGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet :=
  {
    groups := groups
    collect_eq := hcollect
    flatCollects := hflat (.object [])
    collected := hcollected
    lookups := hlookups
    compatible := hcompatible
    recursiveAppend := happend
  }

def toExecutedGroupedSelectionSetState
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : RecursiveGroupedSelectionSetState schema resolvers variableValues depth
          parentType source selectionSet)
    : ExecutedGroupedSelectionSetState schema resolvers variableValues (depth + 1)
        parentType source selectionSet :=
  ExecutedGroupedSelectionSetState.of_collected_groups_recursiveAppendState
    state.collect_eq state.flatCollects state.collected state.lookups
    state.compatible state.recursiveAppend

theorem executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : RecursiveGroupedSelectionSetState schema resolvers variableValues depth
          parentType source selectionSet)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  state.toExecutedGroupedSelectionSetState.executeRootSelectionSet_eq_spec

theorem visitSubfieldsResult_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : RecursiveGroupedSelectionSetState schema resolvers variableValues depth
          parentType source selectionSet)
    : ExecutionWindow.visitSubfieldsResult schema resolvers variableValues
        (depth + 1) parentType source selectionSet (.object [])
      = match GraphQL.Execution.executeSelectionSet schema resolvers variableValues
                (depth + 1) parentType source selectionSet with
        | .error errors => .error errors
        | .ok (fields, errors) => .ok (.object fields, errors) :=
  state.toExecutedGroupedSelectionSetState.visitSubfieldsResult_eq_spec

theorem stateEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : RecursiveGroupedSelectionSetState schema resolvers variableValues depth
          parentType source selectionSet)
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
  state.toExecutedGroupedSelectionSetState.stateEquivalent

end RecursiveGroupedSelectionSetState

namespace CollectedFieldGroupRecursiveAppendState

def of_positiveRecursiveChildren
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hchildren
      : ∀ responseName field fields prefixTail,
          (responseName, field :: fields) ∈ groups
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> ∀ childDepth runtimeType identity,
              childDepth + 1 < depth
              -> schema.typeIncludesObjectBool
                    ((schema.fieldReturnType? field.parentType field.fieldName).getD
                      field.fieldName)
                    runtimeType
                  = true
              -> RecursiveGroupedSelectionSetState schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)))
    (hzeroChildren
      : ∀ responseName field fields prefixTail,
          (responseName, field :: fields) ∈ groups
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> ∀ runtimeType (identity : ObjectIdentity),
              0 < depth
              -> schema.typeIncludesObjectBool
                    ((schema.fieldReturnType? field.parentType field.fieldName).getD
                      field.fieldName)
                    runtimeType
                  = true
              -> CollectedSelectionSetGroupsSingleton schema variableValues
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)))
    (herrors
      : ∀ responseName field fields prefixTail later,
          (responseName, field :: fields) ∈ groups
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])).fst)
    : CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
        depth groups :=
  {
    prefixChildren := by
      intro responseName field fields prefixTail hgroup hprefix childDepth
        runtimeType identity hlt hincludes
      cases childDepth with
      | zero =>
          exact
            ExecutedGroupedSelectionSetState.depth_zero schema resolvers
              variableValues runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet
                (field :: prefixTail))
              (hzeroChildren responseName field fields prefixTail hgroup
                hprefix runtimeType identity hlt hincludes)
      | succ childDepth =>
          exact (hchildren responseName field fields prefixTail hgroup hprefix
                  childDepth runtimeType identity hlt
                  hincludes).toExecutedGroupedSelectionSetState
    errorNeutral := herrors
  }

end CollectedFieldGroupRecursiveAppendState

theorem executeRootSelectionSet_eq_spec_of_executedGroups
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hgroups
      : ExecutedFieldGroups schema resolvers variableValues depth parentType
          source groups)
    (hnodup : PairKeysNodup groups)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_executedGroups hcollect hflat hgroups
    hnodup).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_state_of_invariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hplanStates
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ExecutedFieldAppendPlanState schema resolvers variableValues depth
              field fields [] fields)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_collected_groups_state hcollect hflat
    hinvariant hlookups hcompatible hplanStates).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_appendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend : FieldGroupAppendInvariant schema resolvers variableValues depth)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_collected_groups_appendInvariant
    hcollect hflat hcollected hlookups hcompatible
    happend).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_collectedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupAppendInvariant schema resolvers variableValues depth groups)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_collected_groups_collectedAppendInvariant
    hcollect hflat hcollected hlookups hcompatible
    happend).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_collectedLocalAppendInvariant
    {ObjectIdentity : Type} {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity} {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
          depth groups)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_collected_groups_collectedLocalAppendInvariant
    hcollect hflat hcollected hlookups hcompatible
    happend).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_recursiveAppendState
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
          depth groups)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  (ExecutedGroupedSelectionSetState.of_collected_groups_recursiveAppendState
    hcollect hflat hcollected hlookups hcompatible
    happend).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_collected_groups_child_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hchildren
      : ∀ childDepth runtimeType identity childSelectionSet,
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
                    selectionSet := childSelectionSet
                  }
                initial := .object []
              })
    (herrors
      : ∀ responseName field fields prefixTail later,
          (responseName, field :: fields) ∈ groups
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])).fst)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_collected_groups_collectedLocalAppendInvariant
    hcollect hflat hcollected hlookups hcompatible
    (CollectedFieldGroupLocalAppendInvariant.of_child_state hchildren herrors)

theorem executeRootSelectionSet_eq_spec_of_collected_groups_depth_one
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues 1 parentType
          source selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := 0
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    : executeRootSelectionSet schema resolvers variableValues 1 parentType source
        selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues 1
          parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_collected_groups_collectedAppendInvariant
    hcollect hflat hcollected hlookups hcompatible
    (CollectedFieldGroupAppendInvariant.depth_zero schema resolvers variableValues groups)

structure ExecutedGroupedOperationState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    : Type where
  root : rootSourceAppliesBool schema operation source = true
  selectionSet
    : ExecutedGroupedSelectionSetState schema resolvers variableValues depth
        (operation.rootType schema) source operation.selectionSet

namespace ExecutedGroupedOperationState

theorem executeQueryWithFuel_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (state
      : ExecutedGroupedOperationState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          operation depth source)
    : executeQueryWithFuel schema resolvers variableValues operation depth source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation depth source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source state.root
  exact state.selectionSet.executeRootSelectionSet_eq_spec

theorem executeQuery_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {source : ResolverValue ObjectIdentity}
    (state
      : ExecutedGroupedOperationState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) operation
          (GraphQL.Execution.executeQueryFuelBound operation) source)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact state.executeQueryWithFuel_eq_spec

end ExecutedGroupedOperationState

def ExecutedGroupedOperationState.of_executedGroups
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues (operation.rootType schema)
          source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hgroups
      : ExecutedFieldGroups schema resolvers variableValues depth
          (operation.rootType schema) source groups)
    (hnodup : PairKeysNodup groups)
    : ExecutedGroupedOperationState schema resolvers variableValues operation
        (depth + 1) source :=
  {
    root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_executedGroups hcollect hflat hgroups hnodup
  }

def ExecutedGroupedOperationState.of_collected_groups_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues (operation.rootType schema)
          source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hplanStates
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ExecutedFieldAppendPlanState schema resolvers variableValues depth
              field fields [] fields)
    : ExecutedGroupedOperationState schema resolvers variableValues operation
        (depth + 1) source :=
  {
    root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_collected_groups_state hcollect
        hflat hinvariant hlookups hcompatible hplanStates
  }

def ExecutedGroupedOperationState.of_collected_groups_appendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues (operation.rootType schema)
          source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend : FieldGroupAppendInvariant schema resolvers variableValues depth)
    : ExecutedGroupedOperationState schema resolvers variableValues operation
        (depth + 1) source :=
  {
    root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_collected_groups_appendInvariant
        hcollect hflat hcollected hlookups hcompatible happend
  }

def ExecutedGroupedOperationState.of_collected_groups_collectedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues (operation.rootType schema)
          source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupAppendInvariant schema resolvers variableValues depth groups)
    : ExecutedGroupedOperationState schema resolvers variableValues operation
        (depth + 1) source :=
  {
    root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_collected_groups_collectedAppendInvariant
        hcollect hflat hcollected hlookups hcompatible happend
  }

def ExecutedGroupedOperationState.of_collected_groups_collectedLocalAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues (operation.rootType schema)
          source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
          depth groups)
    : ExecutedGroupedOperationState schema resolvers variableValues operation
        (depth + 1) source :=
  {
    root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_collected_groups_collectedLocalAppendInvariant
        hcollect hflat hcollected hlookups hcompatible happend
  }

def ExecutedGroupedOperationState.of_collected_groups_recursiveAppendState
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues (operation.rootType schema)
          source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupRecursiveAppendState schema resolvers variableValues
          depth groups)
    : ExecutedGroupedOperationState schema resolvers variableValues operation
        (depth + 1) source :=
  {
    root := hroot
    selectionSet :=
      ExecutedGroupedSelectionSetState.of_collected_groups_recursiveAppendState
        hcollect hflat hcollected hlookups hcompatible happend
  }

theorem executeQueryWithFuel_eq_spec_of_executedGroups
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hgroups
      : ExecutedFieldGroups schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth (operation.rootType schema) source groups)
    (hnodup : PairKeysNodup groups)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_executedGroups hroot hcollect hflat hgroups
    hnodup).executeQueryWithFuel_eq_spec

theorem executeQueryWithFuel_eq_spec_of_collected_groups_state_of_invariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hplanStates
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ExecutedFieldAppendPlanState schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              depth field fields [] fields)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_collected_groups_state hroot hcollect
    hflat hinvariant hlookups hcompatible
    hplanStates).executeQueryWithFuel_eq_spec

theorem executeQueryWithFuel_eq_spec_of_collected_groups_appendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : FieldGroupAppendInvariant schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_collected_groups_appendInvariant hroot
    hcollect hflat hcollected hlookups hcompatible
    happend).executeQueryWithFuel_eq_spec

theorem executeQueryWithFuel_eq_spec_of_collected_groups_collectedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupAppendInvariant schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth groups)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_collected_groups_collectedAppendInvariant
    hroot hcollect hflat hcollected hlookups hcompatible
    happend).executeQueryWithFuel_eq_spec

theorem executeQueryWithFuel_eq_spec_of_collected_groups_collectedLocalAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupLocalAppendInvariant schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth groups)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_collected_groups_collectedLocalAppendInvariant
    hroot hcollect hflat hcollected hlookups hcompatible
    happend).executeQueryWithFuel_eq_spec

theorem executeQueryWithFuel_eq_spec_of_collected_groups_recursiveAppendState
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupRecursiveAppendState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth groups)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source :=
  (ExecutedGroupedOperationState.of_collected_groups_recursiveAppendState
    hroot hcollect hflat hcollected hlookups hcompatible
    happend).executeQueryWithFuel_eq_spec

theorem executeQueryWithFuel_eq_spec_of_collected_groups_child_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hchildren
      : ∀ childDepth runtimeType identity childSelectionSet,
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
                    selectionSet := childSelectionSet
                  }
                initial := .object []
              })
    (herrors
      : ∀ responseName field fields prefixTail later,
          (responseName, field :: fields) ∈ groups
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])).fst)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source :=
  executeQueryWithFuel_eq_spec_of_collected_groups_collectedLocalAppendInvariant
    hroot hcollect hflat hcollected hlookups hcompatible
    (CollectedFieldGroupLocalAppendInvariant.of_child_state hchildren herrors)

theorem executeQueryWithFuel_eq_spec_of_collected_groups_depth_one
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) 1
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := 0
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    : executeQueryWithFuel schema resolvers variableValues operation 1 source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation 1 source :=
  executeQueryWithFuel_eq_spec_of_collected_groups_collectedAppendInvariant
    hroot hcollect hflat hcollected hlookups hcompatible
    (CollectedFieldGroupAppendInvariant.depth_zero schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues) groups)

theorem executeQuery_eq_spec_of_executedGroups
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hgroups
      : ExecutedFieldGroups schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth (operation.rootType schema) source groups)
    (hnodup : PairKeysNodup groups)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact executeQueryWithFuel_eq_spec_of_executedGroups hroot hcollect hflat
    hgroups hnodup

theorem executeQuery_eq_spec_of_collected_groups_state_of_invariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hplanStates
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ExecutedFieldAppendPlanState schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              depth field fields [] fields)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
      executeQueryWithFuel_eq_spec_of_collected_groups_state_of_invariant hroot
        hcollect hflat hinvariant hlookups hcompatible hplanStates

theorem executeQuery_eq_spec_of_collected_groups_appendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : FieldGroupAppendInvariant schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
      executeQueryWithFuel_eq_spec_of_collected_groups_appendInvariant hroot
        hcollect hflat hcollected hlookups hcompatible happend

theorem executeQuery_eq_spec_of_collected_groups_collectedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupAppendInvariant schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth groups)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
      executeQueryWithFuel_eq_spec_of_collected_groups_collectedAppendInvariant
        hroot hcollect hflat hcollected hlookups hcompatible happend

theorem executeQuery_eq_spec_of_collected_groups_collectedLocalAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupLocalAppendInvariant schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth groups)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
      executeQueryWithFuel_eq_spec_of_collected_groups_collectedLocalAppendInvariant
        hroot hcollect hflat hcollected hlookups hcompatible happend

theorem executeQuery_eq_spec_of_collected_groups_recursiveAppendState
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupRecursiveAppendState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth groups)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
      executeQueryWithFuel_eq_spec_of_collected_groups_recursiveAppendState hroot
        hcollect hflat hcollected hlookups hcompatible happend

theorem executeQuery_eq_spec_of_collected_groups_child_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hchildren
      : ∀ childDepth runtimeType identity childSelectionSet,
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
                    selectionSet := childSelectionSet
                  }
                initial := .object []
              })
    (herrors
      : ∀ responseName field fields prefixTail later,
          (responseName, field :: fields) ∈ groups
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])).fst)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_collected_groups_child_state hroot hcollect
      hflat hcollected hlookups hcompatible hchildren herrors

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
