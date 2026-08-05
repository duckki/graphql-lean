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

open GraphQL.Execution
open Eager

def depthZeroVisitStatus : Nat -> VisitStatus
  | 0 => visitOk
  | _n + 1 => .error 1

theorem combineVisitStatus_depthZeroVisitStatus_zero_left (right : Nat)
    : combineVisitStatus (depthZeroVisitStatus 0) (depthZeroVisitStatus right)
      = depthZeroVisitStatus right := by
  cases right <;>
    simp [depthZeroVisitStatus, visitOk, combineVisitStatus,
      GraphQL.Execution.Result.combine]

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
      match head.snd with
      | .error errors => (head.fst, .error errors)
      | .ok _ok =>
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
  cases hprevious : responseObjectField? field.responseName (.object fields) with
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
      | some previous =>
          simp [zeroDepthExecutableFieldsResult, zeroDepthResponseNameResult,
            hprevious, mergeResponseFieldResult, resultValueOrNull,
            resultStatus]
          have htail :=
            visitSubfields_executableFieldSelections_depth_zero_eq_zeroDepthExecutableFieldsResult
              schema resolvers variableValues parentType source rest
              (mergeResponseField field.responseName previous outputFields)
          simp [mergeResponseFieldIntoObject, visitOk]
          exact ⟨congrArg Prod.fst htail, congrArg Prod.snd htail⟩

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
        outOfFuel, resultValueOrNull, resultStatus, depthZeroVisitStatus]

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

private theorem addExecutableGroup_ne_nil
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : GraphQL.Execution.addExecutableGroup group groups ≠ [] := by
  cases groups with
  | nil =>
      simp [GraphQL.Execution.addExecutableGroup]
  | cons head tail =>
      rcases head with ⟨responseName, fields⟩
      simp only [GraphQL.Execution.addExecutableGroup]
      split <;> simp

private theorem mergeExecutableGroups_eq_nil_iff
    (left right : List (Name × List ExecutableField))
    : GraphQL.Execution.mergeExecutableGroups left right = []
      ↔ left = [] ∧ right = [] := by
  induction right generalizing left with
  | nil =>
      simp [GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      change
        GraphQL.Execution.mergeExecutableGroups
            (GraphQL.Execution.addExecutableGroup group left) rest = []
          ↔ left = [] ∧ group :: rest = []
      rw [ih]
      constructor
      · intro h
        exact False.elim
          (addExecutableGroup_ne_nil group left h.1)
      · intro h
        simp at h

private def DepthZeroVisitMatchesCollection
    (groups : List (Name × List ExecutableField))
    (visited : ResponseValue × VisitStatus)
    : Prop :=
  (groups = [] ∧ visited = (.object [], visitOk))
  ∨ (groups ≠ [] ∧ ∃ output, visited = (output, .error 1))

mutual
  private theorem visitSelection_depth_zero_matches_collectSelection
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ selection,
          DepthZeroVisitMatchesCollection
            (GraphQL.Execution.collectSelection schema variableValues parentType
              source selection)
            (visitSelection schema resolvers variableValues 0 parentType source
              selection (.object []))
    | .field responseName fieldName arguments directives selectionSet => by
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · right
          constructor
          · simp [GraphQL.Execution.collectSelection, hallowed]
          · refine ⟨.object [(responseName, .null)], ?_⟩
            simp [visitSelection, hallowed, responseObjectField?,
              lookupResponseField?, mergeResponseFieldResult,
              mergeResponseFieldIntoObject, mergeResponseField,
              GraphQL.Execution.outOfFuel, resultValueOrNull, resultStatus]
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · exact False.elim (hallowed h)
          left
          simp [GraphQL.Execution.collectSelection, visitSelection, hblocked,
            visitOk]
    | .inlineFragment none directives selectionSet => by
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · simpa [GraphQL.Execution.collectSelection, visitSelection, hallowed]
            using
              visitSubfields_depth_zero_matches_collectFields schema resolvers
                variableValues parentType source selectionSet
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · exact False.elim (hallowed h)
          left
          simp [GraphQL.Execution.collectSelection, visitSelection, hblocked,
            visitOk]
    | .inlineFragment (some typeCondition) directives selectionSet => by
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · by_cases happly :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                true
          · simpa [GraphQL.Execution.collectSelection, visitSelection, hallowed,
              happly]
              using
                visitSubfields_depth_zero_matches_collectFields schema resolvers
                  variableValues parentType source selectionSet
          · have hnotApply :
                doesFragmentTypeApplyBool schema parentType source typeCondition =
                  false := by
              cases h :
                  doesFragmentTypeApplyBool schema parentType source typeCondition
              · rfl
              · exact False.elim (happly h)
            left
            simp [GraphQL.Execution.collectSelection, visitSelection, hallowed,
              hnotApply, visitOk]
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · exact False.elim (hallowed h)
          left
          simp [GraphQL.Execution.collectSelection, visitSelection, hblocked,
            visitOk]

  private theorem visitSubfields_depth_zero_matches_collectFields
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ selectionSet,
          DepthZeroVisitMatchesCollection
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)
            (visitSubfields schema resolvers variableValues 0 parentType source
              selectionSet (.object []))
    | [] => by
        left
        simp [GraphQL.Execution.collectFields, visitSubfields, visitOk]
    | selection :: rest => by
        have hhead :=
          visitSelection_depth_zero_matches_collectSelection schema resolvers
            variableValues parentType source selection
        rcases hhead with ⟨hheadCollect, hheadVisit⟩
          | ⟨hheadCollect, output, hheadVisit⟩
        · have htail :=
            visitSubfields_depth_zero_matches_collectFields schema resolvers
              variableValues parentType source rest
          rcases htail with ⟨htailCollect, htailVisit⟩
            | ⟨htailCollect, output, htailVisit⟩
          · left
            constructor
            · simp [GraphQL.Execution.collectFields, hheadCollect, htailCollect,
                GraphQL.Execution.mergeExecutableGroups]
            · simp [visitSubfields, hheadVisit, htailVisit, combineVisitStatus,
                visitOk, GraphQL.Execution.Result.combine]
          · right
            constructor
            · intro hcollect
              have hnil :=
                (mergeExecutableGroups_eq_nil_iff
                  (GraphQL.Execution.collectSelection schema variableValues
                    parentType source selection)
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest)).mp
                  (by simpa [GraphQL.Execution.collectFields] using hcollect)
              exact htailCollect hnil.2
            · refine ⟨output, ?_⟩
              simp [visitSubfields, hheadVisit, htailVisit, combineVisitStatus,
                visitOk, GraphQL.Execution.Result.combine]
        · right
          constructor
          · intro hcollect
            have hnil :=
              (mergeExecutableGroups_eq_nil_iff
                (GraphQL.Execution.collectSelection schema variableValues
                  parentType source selection)
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rest)).mp
                (by simpa [GraphQL.Execution.collectFields] using hcollect)
            exact hheadCollect hnil.1
          · refine ⟨output, ?_⟩
            simp [visitSubfields, hheadVisit]
end

theorem executeRootSelectionSet_depth_zero_aligned
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues 0 parentType
          source selectionSet)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues 0 parentType source selectionSet) := by
  have hvisit :=
    visitSubfields_depth_zero_matches_collectFields schema resolvers
      variableValues parentType source selectionSet
  rcases hvisit with ⟨hcollect, hvisit⟩
    | ⟨hcollect, output, hvisit⟩
  · simp [executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
      hcollect, hvisit, GraphQL.Execution.executeCollectedFields, visitOk,
      RootSelectionResultAlignedEquivalent, ErrorPresenceEquivalent]
  · have hnonempty :
        CollectedGroupsFieldsNonempty
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet) :=
      collectFields_fieldsNonempty schema variableValues parentType source
        selectionSet
    have hspec :=
      executeCollectedFields_depth_zero_nonempty schema resolvers variableValues
        source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)
        hnonempty
    cases hgroups :
        GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet with
    | nil =>
        exact False.elim (hcollect hgroups)
    | cons group rest =>
        simp [executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
          hvisit, hgroups] at hspec ⊢
        rw [hspec]
        simp [RootSelectionResultAlignedEquivalent, ErrorPresenceEquivalent]

end ExecutionUngroupedUncached
end Algorithms

end GraphQL
