import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Absorption

/-!
Depth-zero facts for ungrouped execution.

At zero completion depth, fresh response names write sentinel `null` values into the
response object and contribute one execution error. Later visits to the same response
name see the sentinel and contribute no new error. The proofs in this file therefore
separate status counting from intermediate response-object shape.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

def depthZeroVisitStatus : Nat -> VisitStatus
  | 0 => visitOk
  | n + 1 => .error (n + 1)

theorem combineVisitStatus_depthZeroVisitStatus (left right : Nat)
    : combineVisitStatus (depthZeroVisitStatus left) (depthZeroVisitStatus right)
      = depthZeroVisitStatus (left + right) := by
  cases left <;> cases right <;>
    simp [depthZeroVisitStatus, visitOk, combineVisitStatus,
      GraphQL.Execution.Result.combine,
      Nat.add_comm, Nat.add_left_comm]

def zeroDepthResponseNameResult
    (responseName : Name) (fields : List (Name × ResponseValue))
    : ResponseValue × VisitStatus :=
  let fieldResult : GraphQL.Execution.Result ResponseValue :=
    match responseObjectField? responseName (.object fields) with
    | some previous => .ok (previous, 0)
    | none => GraphQL.Execution.outOfFuel
  mergeResponseFieldResult responseName fieldResult (.object fields)

def zeroDepthExecutableFieldsResult (responseName : Name)
    : List ExecutableField -> List (Name × ResponseValue) -> ResponseValue × VisitStatus
  | [], fields => (.object fields, visitOk)
  | _field :: rest, fields =>
      let head := zeroDepthResponseNameResult responseName fields
      let tailFields :=
        match head.fst with
        | .object fields => fields
        | _ => []
      let tail := zeroDepthExecutableFieldsResult responseName rest tailFields
      (tail.fst, combineVisitStatus head.snd tail.snd)

theorem zeroDepthResponseNameResult_eq_visitSelection_executableField
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List (Name × ResponseValue))
    : visitSelection schema resolvers variableValues 0 parentType source
        (executableFieldSelection responseName field) (.object fields)
      = zeroDepthResponseNameResult responseName fields := by
  cases hprevious : responseObjectField? responseName (.object fields) with
  | none =>
      cases field
      simp [visitSelection, executableFieldSelection,
        selectionDirectivesAllowBool_empty, zeroDepthResponseNameResult,
        hprevious, mergeResponseFieldResult, GraphQL.Execution.outOfFuel,
        resultValueOrNull, resultStatus]
  | some previous =>
      cases field
      simp [visitSelection, executableFieldSelection,
        selectionDirectivesAllowBool_empty, zeroDepthResponseNameResult,
        hprevious, mergeResponseFieldResult, resultValueOrNull, resultStatus]

theorem
    visitSubfields_executableFieldSelections_depth_zero_eq_zeroDepthExecutableFieldsResult
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (responseName : Name)
    : ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
        visitSubfields schema resolvers variableValues 0 parentType source
          (executableFieldSelections responseName fields) (.object outputFields)
        = zeroDepthExecutableFieldsResult responseName fields outputFields
  | [], outputFields => by
      simp [visitSubfields, executableFieldSelections,
        zeroDepthExecutableFieldsResult]
  | field :: rest, outputFields => by
      rw [show
          executableFieldSelections responseName (field :: rest) =
            executableFieldSelection responseName field ::
              executableFieldSelections responseName rest by
        simp [executableFieldSelections]]
      rw [visitSubfields]
      rw [zeroDepthResponseNameResult_eq_visitSelection_executableField
        schema resolvers variableValues parentType source responseName field
          outputFields]
      cases hprevious :
          responseObjectField? responseName (.object outputFields) with
      | none =>
          simp [zeroDepthExecutableFieldsResult, zeroDepthResponseNameResult,
            hprevious, mergeResponseFieldResult, GraphQL.Execution.outOfFuel,
            resultValueOrNull, resultStatus]
          have htail :=
            visitSubfields_executableFieldSelections_depth_zero_eq_zeroDepthExecutableFieldsResult
              schema resolvers variableValues parentType source responseName rest
              (mergeResponseField responseName .null outputFields)
          simp [mergeResponseFieldIntoObject] at htail ⊢
          constructor
          · exact congrArg Prod.fst htail
          · rw [congrArg Prod.snd htail]
      | some previous =>
          simp [zeroDepthExecutableFieldsResult, zeroDepthResponseNameResult,
            hprevious, mergeResponseFieldResult, resultValueOrNull,
            resultStatus]
          have htail :=
            visitSubfields_executableFieldSelections_depth_zero_eq_zeroDepthExecutableFieldsResult
              schema resolvers variableValues parentType source responseName rest
              (mergeResponseField responseName previous outputFields)
          simp [mergeResponseFieldIntoObject] at htail ⊢
          constructor
          · exact congrArg Prod.fst htail
          · rw [congrArg Prod.snd htail]

theorem executeCollectedFields_depth_zero_nonempty
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    : ∀ groups,
        CollectedGroupsFieldsNonempty groups
        -> GraphQL.Execution.executeCollectedFields schema resolvers variableValues
              0 parentType source groups
            = match groups with
              | [] => .ok ([], 0)
              | _group :: _rest => .error groups.length
  | [], _hnonempty => by
      simp [GraphQL.Execution.executeCollectedFields]
  | (_responseName, fields) :: rest, hnonempty => by
      have hfields : fields ≠ [] :=
        hnonempty _responseName fields (by simp)
      have hrest :=
        executeCollectedFields_depth_zero_nonempty schema resolvers
          variableValues parentType source rest
          (CollectedGroupsFieldsNonempty_tail hnonempty)
      cases fields with
      | nil =>
          exact False.elim (hfields rfl)
      | cons _field _tail =>
          cases rest with
          | nil =>
                simp [GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine, GraphQL.Execution.outOfFuel]
          | cons _next _more =>
              simp [GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine, GraphQL.Execution.outOfFuel]
                at hrest ⊢
              rw [hrest]
              simp [Nat.add_comm, Nat.add_left_comm]

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
