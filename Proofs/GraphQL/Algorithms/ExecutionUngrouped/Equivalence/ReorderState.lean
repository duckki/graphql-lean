import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Final
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Reorder

/-!
Main proof-boundary constructors for reorder-normalized ungrouped execution.

These lemmas lift the local reorder theorem into the final grouped-state proof
API.  A normalized order that already proves grouped/spec equivalence can be
transported back to the original order when a later duplicate field is moved
left across a response-name-fresh middle block after its response key is already
populated by the prefix.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

theorem visitFieldSliceFold_succ_single_empty_eq_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    : visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source [field] (.object [])
      = .object
          [(
            field.responseName,
            responseFieldSlice schema resolvers variableValues completionDepth
              source field
          )] := by
    simp [visitFieldSliceFold, visitFieldSlice, visitFieldSliceResult,
      responseFieldSlice, mergeResponseFieldResult, mergeResponseFieldIntoObject,
      mergeResponseField, responseObjectField?, lookupResponseField?]

namespace ExecutedGroupedSelectionSetState

def of_middle_existing_last_swap_after_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity}
    {pre middle : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    {fields : List (Name × ResponseValue)}
    (normalized
      : ExecutedGroupedSelectionSetState schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    (hprefix
      : visitFieldSliceFold schema resolvers variableValues
          (completionDepth + 1) source pre (.object [])
        = .object fields)
    (hparents
      : ∀ field,
          field ∈ pre ++ ((middle ++ [later]) ++ rest) -> field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    : ExecutedGroupedSelectionSetState schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest))) :=
  { groups := normalized.groups
    collect_eq := by
      rw [hcollect]
      exact normalized.collect_eq
    flatCollects :=
      VisitSubfieldsFlatCollects_middle_existing_last_swap_after_prefix_of_traces
        schema resolvers variableValues completionDepth parentType source pre
        middle later rest fields hprefix hparents hlater hnotMiddle hleftTrace
        hrightTrace hcollect normalized.flatCollects
    flatSpec := normalized.flatSpec }

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity}
    {pre middle : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    {fields : List (Name × ResponseValue)}
    (normalized
      : ExecutedGroupedSelectionSetState schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    (hprefix
      : visitFieldSliceFold schema resolvers variableValues
          (completionDepth + 1) source pre (.object [])
        = .object fields)
    (hparents
      : ∀ field,
          field ∈ pre ++ ((middle ++ [later]) ++ rest) -> field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    : executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest))) :=
  (of_middle_existing_last_swap_after_prefix normalized hprefix hparents hlater
    hnotMiddle hleftTrace hrightTrace hcollect).executeRootSelectionSet_eq_spec

def of_middle_existing_last_swap_after_single_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity}
    {first later : ExecutableField} {middle rest : List ExecutableField}
    (normalized
      : ExecutedGroupedSelectionSetState schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections ([first] ++ ((later :: middle) ++ rest))))
    (hsameResponse : later.responseName = first.responseName)
    (hparents
      : ∀ field,
          field ∈ [first] ++ ((middle ++ [later]) ++ rest)
          -> field.parentType = parentType)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest)
          (.object
            [(
              first.responseName,
              responseFieldSlice schema resolvers variableValues completionDepth
                source first
            )]))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest)
          (.object
            [(
              first.responseName,
              responseFieldSlice schema resolvers variableValues completionDepth
                source first
            )]))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections ([first] ++ ((middle ++ [later]) ++ rest)))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections ([first] ++ ((later :: middle) ++ rest))))
    : ExecutedGroupedSelectionSetState schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections ([first] ++ ((middle ++ [later]) ++ rest))) :=
  of_middle_existing_last_swap_after_prefix normalized
    (visitFieldSliceFold_succ_single_empty_eq_object schema resolvers
      variableValues completionDepth source first)
    hparents
    (by simp [hsameResponse])
    hnotMiddle hleftTrace hrightTrace hcollect

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_single_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity}
    {first later : ExecutableField} {middle rest : List ExecutableField}
    (normalized
      : ExecutedGroupedSelectionSetState schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections ([first] ++ ((later :: middle) ++ rest))))
    (hsameResponse : later.responseName = first.responseName)
    (hparents
      : ∀ field,
          field ∈ [first] ++ ((middle ++ [later]) ++ rest)
          -> field.parentType = parentType)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest)
          (.object
            [(
              first.responseName,
              responseFieldSlice schema resolvers variableValues completionDepth
                source first
            )]))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest)
          (.object
            [(
              first.responseName,
              responseFieldSlice schema resolvers variableValues completionDepth
                source first
            )]))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections ([first] ++ ((middle ++ [later]) ++ rest)))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections ([first] ++ ((later :: middle) ++ rest))))
    : executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections ([first] ++ ((middle ++ [later]) ++ rest)))
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections ([first] ++ ((middle ++ [later]) ++ rest))) :=
  (of_middle_existing_last_swap_after_single_prefix normalized hsameResponse
    hparents hnotMiddle hleftTrace hrightTrace
    hcollect).executeRootSelectionSet_eq_spec

end ExecutedGroupedSelectionSetState

namespace RecursiveGroupedSelectionSetState

def of_middle_existing_last_swap_after_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity}
    {pre middle : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    {fields : List (Name × ResponseValue)}
    (normalized
      : RecursiveGroupedSelectionSetState schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    (hprefix
      : visitFieldSliceFold schema resolvers variableValues
          (completionDepth + 1) source pre (.object [])
        = .object fields)
    (hparents
      : ∀ field,
          field ∈ pre ++ ((middle ++ [later]) ++ rest) -> field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    : RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest))) :=
  { groups := normalized.groups
    collect_eq := by
      rw [hcollect]
      exact normalized.collect_eq
    flatCollects :=
      VisitSubfieldsFlatCollects_middle_existing_last_swap_after_prefix_of_traces
        schema resolvers variableValues completionDepth parentType source pre
        middle later rest fields hprefix hparents hlater hnotMiddle hleftTrace
        hrightTrace hcollect normalized.flatCollects
    collected :=
      { groupedResponseKeysUnique := by
          rw [hcollect]
          exact normalized.collected.groupedResponseKeysUnique
        groupedFieldsResolveStable := by
          rw [hcollect]
          exact normalized.collected.groupedFieldsResolveStable }
    lookups := normalized.lookups
    compatible := normalized.compatible
    recursiveAppend := normalized.recursiveAppend }

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity}
    {pre middle : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    {fields : List (Name × ResponseValue)}
    (normalized
      : RecursiveGroupedSelectionSetState schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    (hprefix
      : visitFieldSliceFold schema resolvers variableValues
          (completionDepth + 1) source pre (.object [])
        = .object fields)
    (hparents
      : ∀ field,
          field ∈ pre ++ ((middle ++ [later]) ++ rest) -> field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    : executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest))) :=
  (of_middle_existing_last_swap_after_prefix normalized hprefix hparents hlater
    hnotMiddle hleftTrace hrightTrace hcollect).executeRootSelectionSet_eq_spec

def of_middle_existing_last_swap_after_single_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity}
    {first later : ExecutableField} {middle rest : List ExecutableField}
    (normalized
      : RecursiveGroupedSelectionSetState schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections ([first] ++ ((later :: middle) ++ rest))))
    (hsameResponse : later.responseName = first.responseName)
    (hparents
      : ∀ field,
          field ∈ [first] ++ ((middle ++ [later]) ++ rest)
          -> field.parentType = parentType)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest)
          (.object
            [(
              first.responseName,
              responseFieldSlice schema resolvers variableValues completionDepth
                source first
            )]))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest)
          (.object
            [(
              first.responseName,
              responseFieldSlice schema resolvers variableValues completionDepth
                source first
            )]))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections ([first] ++ ((middle ++ [later]) ++ rest)))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections ([first] ++ ((later :: middle) ++ rest))))
    : RecursiveGroupedSelectionSetState schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections ([first] ++ ((middle ++ [later]) ++ rest))) :=
  of_middle_existing_last_swap_after_prefix normalized
    (visitFieldSliceFold_succ_single_empty_eq_object schema resolvers
      variableValues completionDepth source first)
    hparents
    (by simp [hsameResponse])
    hnotMiddle hleftTrace hrightTrace hcollect

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_single_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity}
    {first later : ExecutableField} {middle rest : List ExecutableField}
    (normalized
      : RecursiveGroupedSelectionSetState schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections ([first] ++ ((later :: middle) ++ rest))))
    (hsameResponse : later.responseName = first.responseName)
    (hparents
      : ∀ field,
          field ∈ [first] ++ ((middle ++ [later]) ++ rest)
          -> field.parentType = parentType)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest)
          (.object
            [(
              first.responseName,
              responseFieldSlice schema resolvers variableValues completionDepth
                source first
            )]))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest)
          (.object
            [(
              first.responseName,
              responseFieldSlice schema resolvers variableValues completionDepth
                source first
            )]))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections ([first] ++ ((middle ++ [later]) ++ rest)))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections ([first] ++ ((later :: middle) ++ rest))))
    : executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections ([first] ++ ((middle ++ [later]) ++ rest)))
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections ([first] ++ ((middle ++ [later]) ++ rest))) :=
  (of_middle_existing_last_swap_after_single_prefix normalized hsameResponse
    hparents hnotMiddle hleftTrace hrightTrace
    hcollect).executeRootSelectionSet_eq_spec

end RecursiveGroupedSelectionSetState

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
