import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Final

/-!
Recursive proof-facing constructors for the ungrouped execution equivalence.

These helpers separate the depth induction from the resolver and validation invariants
that supply collection flatness and collected-field invariants.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

structure RecursiveSelectionSetGlobalInvariants
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    : Prop where
  flat
    : ∀ (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
          (selectionSet : List Selection),
        VisitSubfieldsFlatCollects schema resolvers variableValues depth
          parentType source selectionSet (.object [])
  collected
    : ∀ (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
          (selectionSet : List Selection),
        ExecutionCollectedFieldInvariant
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
  compatible
    : ∀ (parentType : Name) (source : ResolverValue ObjectIdentity)
          (selectionSet : List Selection),
        CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet)
  lookups
    : ∀ (parentType : Name) (source : ResolverValue ObjectIdentity)
          (selectionSet : List Selection),
        CollectedGroupsFieldLookupValid schema parentType
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet)
  zeroChildrenSingletons
    : ∀ (depth : Nat) (parentType : Name)
          (source : ResolverValue ObjectIdentity) (selectionSet : List Selection)
          responseName field fields prefixTail,
        (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> ∀ runtimeType (identity : ObjectIdentity),
            0 < depth
            -> schema.typeIncludesObjectBool
                  ((schema.fieldReturnType? field.parentType field.fieldName).getD
                    field.fieldName)
                  runtimeType
                = true
            -> CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
                (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
  errorNeutral
    : ∀ (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
          (selectionSet : List Selection)
          responseName field fields prefixTail later,
        (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet
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

structure RecursiveSelectionSetGlobalFreshPrefixInvariants
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    : Prop where
  freshFlat
    : ∀ (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
          (selectionSet : List Selection),
        VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source selectionSet
  collected
    : ∀ (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
          (selectionSet : List Selection),
        ExecutionCollectedFieldInvariant
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
  compatible
    : ∀ (parentType : Name) (source : ResolverValue ObjectIdentity)
          (selectionSet : List Selection),
        CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet)
  lookups
    : ∀ (parentType : Name) (source : ResolverValue ObjectIdentity)
          (selectionSet : List Selection),
        CollectedGroupsFieldLookupValid schema parentType
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet)
  zeroChildrenSingletons
    : ∀ (depth : Nat) (parentType : Name)
          (source : ResolverValue ObjectIdentity) (selectionSet : List Selection)
          responseName field fields prefixTail,
        (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> ∀ runtimeType (identity : ObjectIdentity),
            0 < depth
            -> schema.typeIncludesObjectBool
                  ((schema.fieldReturnType? field.parentType field.fieldName).getD
                    field.fieldName)
                  runtimeType
                = true
            -> CollectedSelectionSetGroupsSingleton schema variableValues runtimeType
                (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
  errorNeutral
    : ∀ (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
          (selectionSet : List Selection)
          responseName field fields prefixTail later,
        (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet
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

namespace RecursiveSelectionSetGlobalFreshPrefixInvariants

theorem toGlobalInvariants
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    (invariants
      : RecursiveSelectionSetGlobalFreshPrefixInvariants schema resolvers variableValues)
    : RecursiveSelectionSetGlobalInvariants schema resolvers variableValues :=
  { flat := by
      intro depth parentType source selectionSet
      exact
        (invariants.freshFlat depth parentType source
          selectionSet).empty
    collected := invariants.collected
    compatible := invariants.compatible
    lookups := invariants.lookups
    zeroChildrenSingletons := invariants.zeroChildrenSingletons
    errorNeutral := invariants.errorNeutral }

end RecursiveSelectionSetGlobalFreshPrefixInvariants

structure SelectionSetLocalInvariants
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : Type where
  flat
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
  compatible
    : CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)
  lookups
    : CollectedGroupsFieldLookupValid schema parentType
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)
  errorNeutral
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet
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

structure SelectionSetLocalFreshPrefixInvariants
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : Type where
  freshFlat
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (depth + 1) parentType source selectionSet
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
  compatible
    : CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)
  lookups
    : CollectedGroupsFieldLookupValid schema parentType
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)
  errorNeutral
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet
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

namespace SelectionSetLocalFreshPrefixInvariants

def toLocalInvariants
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (invariants
      : SelectionSetLocalFreshPrefixInvariants schema resolvers variableValues
          depth parentType source selectionSet)
    : SelectionSetLocalInvariants schema resolvers variableValues depth parentType
        source selectionSet :=
  {
    flat := invariants.freshFlat.empty
    collected := invariants.collected
    compatible := invariants.compatible
    lookups := invariants.lookups
    errorNeutral := invariants.errorNeutral
  }

def of_freshPrefixPlan
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (plan
      : FreshPrefixSelectionPlan schema resolvers variableValues depth parentType
          source selectionSet)
    (collected
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
    (compatible
      : CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet))
    (lookups
      : CollectedGroupsFieldLookupValid schema parentType
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet))
    (errorNeutral
      : ∀ responseName field fields prefixTail later,
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues parentType source
                selectionSet
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
    : SelectionSetLocalFreshPrefixInvariants schema resolvers variableValues
        depth parentType source selectionSet :=
  {
    freshFlat := FreshPrefixSelectionPlan.freshFlat plan
    collected := collected
    compatible := compatible
    lookups := lookups
    errorNeutral := errorNeutral
  }

def of_freshPrefixDerivation
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (derivation
      : FreshPrefixSelectionDerivation schema variableValues parentType source
          selectionSet)
    (collected
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
    (compatible
      : CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet))
    (lookups
      : CollectedGroupsFieldLookupValid schema parentType
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet))
    (errorNeutral
      : ∀ responseName field fields prefixTail later,
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues parentType source
                selectionSet
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
    : SelectionSetLocalFreshPrefixInvariants schema resolvers variableValues
        depth parentType source selectionSet :=
  of_freshPrefixPlan
    (FreshPrefixSelectionPlan.of_derivation schema resolvers variableValues
      depth parentType source derivation)
    collected compatible lookups errorNeutral

end SelectionSetLocalFreshPrefixInvariants

namespace RecursiveGroupedSelectionSetState

def of_localInvariants
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (invariants
      : SelectionSetLocalInvariants schema resolvers variableValues depth
          parentType source selectionSet)
    (hchildren
      : ∀ responseName field fields prefixTail,
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues parentType source
                selectionSet
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> ∀ childDepth runtimeType (identity : ObjectIdentity),
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
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues parentType source
                selectionSet
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
    : RecursiveGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet :=
  {
    groups :=
      GraphQL.Execution.collectFields schema variableValues parentType source selectionSet
    collect_eq := rfl
    flatCollects := invariants.flat
    collected := invariants.collected
    compatible := invariants.compatible
    lookups := invariants.lookups
    recursiveAppend :=
      CollectedFieldGroupRecursiveAppendState.of_positiveRecursiveChildren
        hchildren hzeroChildren invariants.errorNeutral
  }

def of_localFreshPrefixInvariants
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (invariants
      : SelectionSetLocalFreshPrefixInvariants schema resolvers variableValues
          depth parentType source selectionSet)
    (hchildren
      : ∀ responseName field fields prefixTail,
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues parentType source
                selectionSet
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> ∀ childDepth runtimeType (identity : ObjectIdentity),
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
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues parentType source
                selectionSet
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
    : RecursiveGroupedSelectionSetState schema resolvers variableValues depth
        parentType source selectionSet :=
  of_localInvariants invariants.toLocalInvariants hchildren hzeroChildren

def of_globalInvariants
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    (invariants : RecursiveSelectionSetGlobalInvariants schema resolvers variableValues)
    : ∀ depth parentType source selectionSet,
        RecursiveGroupedSelectionSetState schema resolvers variableValues depth
          parentType source selectionSet
  | depth, parentType, source, selectionSet => by
      refine
          { groups :=
              GraphQL.Execution.collectFields schema variableValues parentType
                source selectionSet
            collect_eq := rfl
            flatCollects :=
              invariants.flat (depth + 1) parentType source selectionSet
            collected :=
              invariants.collected depth parentType source selectionSet
            compatible :=
              invariants.compatible parentType source selectionSet
            lookups :=
              invariants.lookups parentType source selectionSet
            recursiveAppend := ?_ }
      apply CollectedFieldGroupRecursiveAppendState.of_positiveRecursiveChildren
      · intro _responseName field _fields prefixTail _hgroup _hprefix
          childDepth runtimeType identity hlt _hincludes
        exact of_globalInvariants invariants childDepth runtimeType
          (.object runtimeType identity)
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
      · intro responseName field fields prefixTail hgroup hprefix runtimeType
          identity hlt hincludes
        exact
          invariants.zeroChildrenSingletons depth parentType source
            selectionSet responseName field fields prefixTail hgroup hprefix
            runtimeType identity hlt hincludes
      · intro responseName field fields prefixTail later hgroup hprefix hlater
          childDepth runtimeType identity hlt
        exact
          invariants.errorNeutral depth parentType source selectionSet
            responseName field fields prefixTail later hgroup hprefix hlater
            childDepth runtimeType identity hlt
termination_by depth _parentType _source _selectionSet => depth
decreasing_by exact Nat.lt_of_succ_lt hlt

def of_globalFreshPrefixInvariants
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    (invariants
      : RecursiveSelectionSetGlobalFreshPrefixInvariants schema resolvers variableValues)
    : ∀ depth parentType source selectionSet,
        RecursiveGroupedSelectionSetState schema resolvers variableValues depth
          parentType source selectionSet :=
  of_globalInvariants invariants.toGlobalInvariants

end RecursiveGroupedSelectionSetState

structure RecursiveGroupedOperationState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    : Type where
  root : rootSourceAppliesBool schema operation source = true
  selectionSet
    : RecursiveGroupedSelectionSetState schema resolvers variableValues depth
        operation.rootType source operation.selectionSet

namespace RecursiveGroupedOperationState

def toExecutedGroupedOperationState
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (state
      : RecursiveGroupedOperationState schema resolvers variableValues operation
          depth source)
    : ExecutedGroupedOperationState schema resolvers variableValues operation
        (depth + 1) source :=
  {
    root := state.root
    selectionSet := state.selectionSet.toExecutedGroupedSelectionSetState
  }

theorem executeQueryWithFuel_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (state
      : RecursiveGroupedOperationState schema resolvers variableValues operation
          depth source)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source :=
  state.toExecutedGroupedOperationState.executeQueryWithFuel_eq_spec

theorem executeQuery_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (state
      : RecursiveGroupedOperationState schema resolvers variableValues operation
          depth source)
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact state.executeQueryWithFuel_eq_spec

def of_localInvariants
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (invariants
      : SelectionSetLocalInvariants schema resolvers variableValues depth
          operation.rootType source operation.selectionSet)
    (hchildren
      : ∀ responseName field fields prefixTail,
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues
                operation.rootType source operation.selectionSet
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> ∀ childDepth runtimeType (identity : ObjectIdentity),
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
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues
                operation.rootType source operation.selectionSet
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
    : RecursiveGroupedOperationState schema resolvers variableValues operation
        depth source :=
  {
    root := hroot
    selectionSet :=
      RecursiveGroupedSelectionSetState.of_localInvariants invariants
        hchildren hzeroChildren
  }

def of_localFreshPrefixInvariants
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (invariants
      : SelectionSetLocalFreshPrefixInvariants schema resolvers variableValues
          depth operation.rootType source operation.selectionSet)
    (hchildren
      : ∀ responseName field fields prefixTail,
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues
                operation.rootType source operation.selectionSet
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> ∀ childDepth runtimeType (identity : ObjectIdentity),
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
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues
                operation.rootType source operation.selectionSet
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
    : RecursiveGroupedOperationState schema resolvers variableValues operation
        depth source :=
  of_localInvariants hroot invariants.toLocalInvariants hchildren hzeroChildren

def of_globalInvariants
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (invariants : RecursiveSelectionSetGlobalInvariants schema resolvers variableValues)
    : RecursiveGroupedOperationState schema resolvers variableValues operation
        depth source :=
  {
    root := hroot
    selectionSet :=
      RecursiveGroupedSelectionSetState.of_globalInvariants invariants depth
        operation.rootType source operation.selectionSet
  }

def of_globalFreshPrefixInvariants
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (invariants
      : RecursiveSelectionSetGlobalFreshPrefixInvariants schema resolvers variableValues)
    : RecursiveGroupedOperationState schema resolvers variableValues operation
        depth source :=
  of_globalInvariants hroot invariants.toGlobalInvariants

end RecursiveGroupedOperationState

theorem executeQueryWithFuel_eq_spec_of_recursiveGroupedOperationState
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (state
      : RecursiveGroupedOperationState schema resolvers variableValues operation
          depth source)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source :=
  state.executeQueryWithFuel_eq_spec

theorem executeQuery_eq_spec_of_recursiveGroupedOperationState
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (state
      : RecursiveGroupedOperationState schema resolvers variableValues operation
          depth source)
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation source :=
  state.executeQuery_eq_spec hdepth

end ExecutionUngrouped
end Algorithms

end GraphQL
