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
namespace ExecutionUngrouped
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

def zeroDepthExecutableFieldsResult
    : List ExecutableField -> List (Name × ResponseValue) -> ResponseValue × VisitStatus
  | [], fields => (.object fields, visitOk)
  | field :: rest, fields =>
      let head := zeroDepthResponseNameResult field.responseName fields
      let tailFields :=
        match head.fst with
        | .object fields => fields
        | _ => []
      let tail := zeroDepthExecutableFieldsResult rest tailFields
      (tail.fst, combineVisitStatus head.snd tail.snd)

theorem zeroDepthResponseNameResult_eq_visitSelection_executableField
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (fields : List (Name × ResponseValue))
    : visitSelection schema resolvers variableValues 0 parentType source
        (executableFieldSelection field) (.object fields)
      = zeroDepthResponseNameResult field.responseName fields := by
  cases hprevious :
      responseObjectField? field.responseName (.object fields) with
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
    : ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
        visitSubfields schema resolvers variableValues 0 parentType source
          (executableFieldSelections fields) (.object outputFields)
        = zeroDepthExecutableFieldsResult fields outputFields
  | [], outputFields => by
      simp [visitSubfields, executableFieldSelections,
        zeroDepthExecutableFieldsResult]
  | field :: rest, outputFields => by
      rw [show
          executableFieldSelections (field :: rest) =
            executableFieldSelection field :: executableFieldSelections rest by
        simp [executableFieldSelections]]
      rw [visitSubfields]
      rw [zeroDepthResponseNameResult_eq_visitSelection_executableField
        schema resolvers variableValues parentType source field outputFields]
      cases hprevious :
          responseObjectField? field.responseName (.object outputFields) with
      | none =>
          simp [zeroDepthExecutableFieldsResult, zeroDepthResponseNameResult,
            hprevious, mergeResponseFieldResult, GraphQL.Execution.outOfFuel,
            resultValueOrNull, resultStatus]
          have htail :=
            visitSubfields_executableFieldSelections_depth_zero_eq_zeroDepthExecutableFieldsResult
              schema resolvers variableValues parentType source rest
              (mergeResponseField field.responseName .null outputFields)
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
              schema resolvers variableValues parentType source rest
              (mergeResponseField field.responseName previous outputFields)
          simp [mergeResponseFieldIntoObject] at htail ⊢
          constructor
          · exact congrArg Prod.fst htail
          · rw [congrArg Prod.snd htail]

theorem collectedExecutableFields_length_eq_groups_length_of_singletons
    : ∀ groups : List (Name × List ExecutableField),
        (∀ responseName fields, (responseName, fields) ∈ groups -> fields.length = 1)
        -> (collectedExecutableFields groups).length = groups.length
  | [], _hsingletons => by
      simp [collectedExecutableFields]
  | (responseName, fields) :: rest, hsingletons => by
      have hfields : fields.length = 1 :=
        hsingletons responseName fields (by simp)
      have hrest :
          (collectedExecutableFields rest).length = rest.length :=
        collectedExecutableFields_length_eq_groups_length_of_singletons rest
          (by
            intro restResponseName restFields hmem
            exact hsingletons restResponseName restFields (by simp [hmem]))
      simp [collectedExecutableFields, List.length_append, hfields, hrest]
      omega

theorem executeCollectedFields_depth_zero_equivalence
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (source : ResolverValue ObjectIdentity)
    : ∀ groups,
        GraphQL.Execution.executeCollectedFieldsData schema resolvers variableValues
          0 source groups
        = []
  | [] => by
      simp [GraphQL.Execution.executeCollectedFieldsData,
        GraphQL.Execution.executeCollectedFields,
        GraphQL.Execution.Result.getD]
  | (_responseName, fields) :: rest => by
      cases fields with
      | nil =>
          have hrest :=
            executeCollectedFields_depth_zero_equivalence schema resolvers
              variableValues source rest
          cases hresult :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues 0 source rest with
          | error errors =>
                simp [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.getD, hresult]
          | ok result =>
              rcases result with ⟨fields, errors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hresult] at hrest ⊢
      | cons _head _tail =>
          cases hresult :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues 0 source rest with
          | error errors =>
                simp [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.getD, GraphQL.Execution.outOfFuel,
                  hresult]
          | ok result =>
              rcases result with ⟨fields, errors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, GraphQL.Execution.outOfFuel,
                hresult]

theorem executeCollectedFields_depth_zero_nonempty
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (source : ResolverValue ObjectIdentity)
    : ∀ groups,
        CollectedGroupsFieldsNonempty groups
        -> GraphQL.Execution.executeCollectedFields schema resolvers variableValues
              0 source groups
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
          variableValues source rest
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

theorem visitSubfields_executableFieldSelections_depth_zero_status_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
        (fields.map (fun field => field.responseName)).Nodup
        -> (∀ field, field ∈ fields -> field.responseName ∉ outputFields.map Prod.fst)
        -> (visitSubfields schema resolvers variableValues 0 parentType source
              (executableFieldSelections fields) (.object outputFields)).snd
            = depthZeroVisitStatus fields.length
  | [], outputFields, _hnodup, _hfresh => by
      simp [visitSubfields, executableFieldSelections, depthZeroVisitStatus,
        visitOk]
  | field :: rest, outputFields, hnodup, hfresh => by
      have hfieldFresh :
          field.responseName ∉ outputFields.map Prod.fst :=
        hfresh field (by simp)
      have hlookup :
          responseObjectField? field.responseName (.object outputFields) =
            none :=
        responseObjectField?_none_of_not_mem field.responseName outputFields
          hfieldFresh
      have hrestNodup :
          (rest.map (fun field => field.responseName)).Nodup := by
        simpa using (List.nodup_cons.mp hnodup).2
      have hrestFresh :
          ∀ restField, restField ∈ rest ->
            restField.responseName ∉
              (mergeResponseField field.responseName .null outputFields).map
                Prod.fst := by
        intro restField hrestField hmem
        have hrestNameNe :
            restField.responseName ≠ field.responseName := by
          intro heq
          exact (List.nodup_cons.mp hnodup).1
            (List.mem_map.mpr ⟨restField, hrestField, heq⟩)
        rcases
          mergeResponseField_key_mem field.responseName
            restField.responseName .null outputFields hmem
        with hinserted | hold
        · exact hrestNameNe hinserted
        · exact hfresh restField (by simp [hrestField]) hold
      have htail :=
        visitSubfields_executableFieldSelections_depth_zero_status_fresh
          schema resolvers variableValues parentType source rest
          (mergeResponseField field.responseName .null outputFields)
          hrestNodup hrestFresh
      simp [visitSubfields, visitSelection, executableFieldSelections,
        executableFieldSelection, selectionDirectivesAllowBool_empty,
        mergeResponseFieldResult, mergeResponseFieldIntoObject, hlookup,
        outOfFuel, resultValueOrNull, resultStatus]
      have htail' :
          (visitSubfields schema resolvers variableValues 0 parentType source
            (List.map executableFieldSelection rest)
            (.object (mergeResponseField field.responseName .null outputFields))).snd =
          depthZeroVisitStatus rest.length := by
        simpa [executableFieldSelections] using htail
      rw [htail']
      cases rest <;>
        simp [depthZeroVisitStatus, visitOk, combineVisitStatus,
          GraphQL.Execution.Result.combine]
      omega

theorem collectedExecutableFields_responseName_key_mem
    (groups : List (Name × List ExecutableField))
    (hresponses : CollectedGroupsResponseName groups)
    (responseName : Name)
    : responseName
        ∈ (collectedExecutableFields groups).map (fun field => field.responseName)
      -> responseName ∈ groups.map Prod.fst := by
  induction groups with
  | nil =>
      intro hmem
      simp [collectedExecutableFields] at hmem
  | cons group rest ih =>
      rcases group with ⟨groupResponseName, fields⟩
      intro hmem
      simp [collectedExecutableFields] at hmem
      rcases hmem with hfield | hrest
      · rcases hfield with ⟨field, hfieldMem, hfieldResponse⟩
        have hresponse :
            field.responseName = groupResponseName :=
          hresponses groupResponseName fields (by simp) field hfieldMem
        simp [hresponse] at hfieldResponse
        simp [hfieldResponse]
      · have hrestResponses : CollectedGroupsResponseName rest :=
          CollectedGroupsResponseName_tail hresponses
        have hkey :
            responseName ∈ rest.map Prod.fst :=
          ih hrestResponses (by simpa [List.mem_map] using hrest)
        simp [hkey]

theorem collectedExecutableFields_responseNames_nodup_of_singletons
    (groups : List (Name × List ExecutableField))
    (hnodup : PairKeysNodup groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hsingletons
      : ∀ responseName fields, (responseName, fields) ∈ groups -> fields.length = 1)
    : (collectedExecutableFields groups).map (fun field => field.responseName)
      |>.Nodup := by
  induction groups with
  | nil =>
      simp [collectedExecutableFields]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      have hfieldsLength : fields.length = 1 :=
        hsingletons responseName fields (by simp)
      cases fields with
      | nil =>
          simp at hfieldsLength
      | cons field tail =>
          cases tail with
          | nil =>
              have hfieldResponse :
                  field.responseName = responseName :=
                hresponses responseName [field] (by simp) field (by simp)
              have hrestNodup : PairKeysNodup rest :=
                PairKeysNodup.tail hnodup
              have hrestResponses : CollectedGroupsResponseName rest :=
                CollectedGroupsResponseName_tail hresponses
              have hrestSingletons :
                  ∀ restResponseName restFields,
                    (restResponseName, restFields) ∈ rest ->
                      restFields.length = 1 := by
                intro restResponseName restFields hmem
                exact hsingletons restResponseName restFields (by simp [hmem])
              have htailNodup :=
                ih hrestNodup hrestResponses hrestSingletons
              have hnot :
                  field.responseName ∉
                    (collectedExecutableFields rest).map
                      (fun field => field.responseName) := by
                intro hmem
                have hkey :
                    field.responseName ∈ rest.map Prod.fst :=
                  collectedExecutableFields_responseName_key_mem rest
                    hrestResponses field.responseName hmem
                have hheadNot :
                    responseName ∉ rest.map Prod.fst :=
                  PairKeysNodup.head_not_mem_tail hnodup
                exact hheadNot (by simpa [hfieldResponse] using hkey)
              simpa [collectedExecutableFields, hfieldResponse] using
                List.nodup_cons.mpr ⟨hnot, htailNodup⟩
          | cons second tailTail =>
              simp at hfieldsLength

theorem ExecutableGroupsFlatSpecEquivalent_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnodup : PairKeysNodup groups)
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hsingletons
      : ∀ responseName fields, (responseName, fields) ∈ groups -> fields.length = 1)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues 0
        parentType source groups := by
  unfold ExecutableGroupsFlatSpecEquivalent
  unfold ExecutableFieldsFlatSpecEquivalent
  have hspec :=
    specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
      schema resolvers variableValues 0 parentType source groups hnodup
      hnonempty hresponses hparents
  have hcollected :=
    executeCollectedFields_depth_zero_nonempty schema resolvers variableValues
      source groups hnonempty
  have hlength :
      (collectedExecutableFields groups).length = groups.length :=
    collectedExecutableFields_length_eq_groups_length_of_singletons groups
      hsingletons
  cases groups with
  | nil =>
      simp [executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
        executableFieldSelections, collectedExecutableFields,
        GraphQL.Execution.collectFields, GraphQL.Execution.executeCollectedFields,
        visitSubfields, visitOk]
  | cons group rest =>
      have hflatNodup :
          ((collectedExecutableFields (group :: rest)).map
            (fun field => field.responseName)).Nodup :=
        collectedExecutableFields_responseNames_nodup_of_singletons
          (group :: rest) hnodup hresponses hsingletons
      have hvisitStatus :=
        visitSubfields_executableFieldSelections_depth_zero_status_fresh
          schema resolvers variableValues parentType source
          (collectedExecutableFields (group :: rest)) [] hflatNodup
          (by
            intro field hmem
            simp)
      unfold executeRootSelectionSet
      rw [hspec]
      rw [hcollected]
      rw [hlength] at hvisitStatus
      simp [hvisitStatus, depthZeroVisitStatus]

end Eager
end ExecutionUngrouped
end Algorithms

end GraphQL
