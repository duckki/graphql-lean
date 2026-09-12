import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList.FreshPlanNormalizes
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.EagerDepthZero

/-!
Depth-zero group-list execution helpers.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance groupListDepthZeroResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem mergeResponseField_self_of_lookup_some_ready (responseName : Name)
    : ∀ (fields : List (Name × ResponseValue)) (existing : ResponseValue),
        ResponseMergeReady (.object fields)
        -> lookupResponseField? responseName fields = some existing
        -> mergeResponseField responseName existing fields = fields
  | [], existing, _hready, hlookup => by
      simp [lookupResponseField?] at hlookup
  | (fieldResponseName, response) :: rest, existing, hready, hlookup => by
      by_cases hname : fieldResponseName == responseName
      · simp [lookupResponseField?, hname] at hlookup
        subst existing
        have hresponseReady :
            ResponseMergeReady response :=
          ResponseMergeReady_object_field
            ((fieldResponseName, response) :: rest) fieldResponseName response
            hready (by simp)
        simpa [mergeResponseField, hname, ResponseAbsorbs] using
          ResponseAbsorbs_refl_of_ready response hresponseReady
      · simp [lookupResponseField?, mergeResponseField, hname] at hlookup ⊢
        have hrestReady :
            ResponseMergeReady (.object rest) := by
          apply ResponseMergeReady.object
          · exact PairKeysNodup.tail
              (ResponseMergeReady_object_pairKeysNodup
                ((fieldResponseName, response) :: rest) hready)
          · intro restResponseName restResponse hmem
            exact ResponseMergeReady_object_field
              ((fieldResponseName, response) :: rest) restResponseName
              restResponse hready (by simp [hmem])
        exact mergeResponseField_self_of_lookup_some_ready responseName rest
          existing hrestReady hlookup

theorem zeroDepthResponseNameResult_of_lookup_some_merge
    (responseName : Name) (fields : List (Name × ResponseValue))
    (existing : ResponseValue)
    : lookupResponseField? responseName fields = some existing
      -> zeroDepthResponseNameResult responseName fields
          = (.object (mergeResponseField responseName existing fields), visitOk) := by
  intro hlookup
  have hprevious :
      responseObjectField? responseName (.object fields) = some existing := by
    simpa [responseObjectField?] using hlookup
  simp [zeroDepthResponseNameResult, hprevious, mergeResponseFieldResult,
    mergeResponseFieldIntoObject, resultValueOrNull, resultStatus, visitOk]

theorem zeroDepthResponseNameResult_of_lookup_some_ready
    (responseName : Name) (fields : List (Name × ResponseValue))
    (existing : ResponseValue)
    : ResponseMergeReady (.object fields)
      -> lookupResponseField? responseName fields = some existing
      -> zeroDepthResponseNameResult responseName fields = (.object fields, visitOk) := by
  intro hready hlookup
  have hresult :=
    zeroDepthResponseNameResult_of_lookup_some_merge responseName fields existing
      hlookup
  have hmerge :
      mergeResponseField responseName existing fields = fields :=
    mergeResponseField_self_of_lookup_some_ready responseName fields existing
      hready hlookup
  simpa [hmerge] using hresult

theorem zeroDepthResponseNameResult_of_lookup_some
    (responseName : Name) (fields : List (Name × ResponseValue))
    (existing : ResponseValue)
    : ResponseMergeReady (.object fields)
      -> lookupResponseField? responseName fields = some existing
      -> zeroDepthResponseNameResult responseName fields = (.object fields, visitOk) :=
  zeroDepthResponseNameResult_of_lookup_some_ready responseName fields existing

theorem zeroDepthResponseNameResult_of_lookup_none
    (responseName : Name) (fields : List (Name × ResponseValue))
    : lookupResponseField? responseName fields = none
      -> zeroDepthResponseNameResult responseName fields
          = (.object (mergeResponseField responseName .null fields), .error 1) := by
  intro hlookup
  have hprevious :
      responseObjectField? responseName (.object fields) = none := by
    simpa [responseObjectField?] using hlookup
  simp [zeroDepthResponseNameResult, hprevious, mergeResponseFieldResult,
    mergeResponseFieldIntoObject, GraphQL.Execution.outOfFuel,
    resultValueOrNull, resultStatus]

theorem lookupResponseField?_mergeResponseField_null_same
    (responseName : Name) (fields : List (Name × ResponseValue))
    : lookupResponseField? responseName (mergeResponseField responseName .null fields)
      = some .null := by
  rw [lookupResponseField?_mergeResponseField_same]
  cases lookupResponseField? responseName fields with
  | none => simp
  | some existing =>
      cases existing <;> simp [mergeResponse]

theorem zeroDepthResponseNameResult_of_lookup_null
    (responseName : Name) (fields : List (Name × ResponseValue))
    : lookupResponseField? responseName fields = some .null
      -> zeroDepthResponseNameResult responseName fields = (.object fields, visitOk) := by
  intro hlookup
  have hresult :=
    zeroDepthResponseNameResult_of_lookup_some_merge responseName fields .null
      hlookup
  have hmerge :
      mergeResponseField responseName .null fields = fields :=
    mergeResponseField_null_of_lookup_null responseName fields hlookup
  simpa [hmerge] using hresult

def zeroDepthExecutableGroupsResult
    : List (Name × List ExecutableField) -> List (Name × ResponseValue)
      -> ResponseValue × VisitStatus
  | [], fields => (.object fields, visitOk)
  | (responseName, _fields) :: rest, fields =>
      let head := zeroDepthResponseNameResult responseName fields
      let tailFields :=
        match head.fst with
        | .object fields => fields
        | _ => []
      let tail := zeroDepthExecutableGroupsResult rest tailFields
      (tail.fst, combineVisitStatus head.snd tail.snd)

def ZeroDepthGroupsNullCompatible
    (groups : List (Name × List ExecutableField))
    (outputFields : List (Name × ResponseValue))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> lookupResponseField? responseName outputFields = none
        ∨ lookupResponseField? responseName outputFields = some .null

theorem zeroDepthResponseNameResult_preserves_lookup_null_or_none
    (target responseName : Name) (fields : List (Name × ResponseValue))
    : lookupResponseField? target fields = none
        ∨ lookupResponseField? target fields = some .null
      -> ∃ outputFields,
          (zeroDepthResponseNameResult responseName fields).fst = .object outputFields
          ∧ (lookupResponseField? target outputFields = none
              ∨ lookupResponseField? target outputFields = some .null) := by
  intro hcompat
  by_cases hsame : target = responseName
  · subst target
    cases hcompat with
    | inl hlookup =>
        refine ⟨mergeResponseField responseName .null fields, ?_, ?_⟩
        · simp [zeroDepthResponseNameResult_of_lookup_none responseName fields
            hlookup]
        · right
          simpa [hlookup] using
            lookupResponseField?_mergeResponseField_null_same responseName fields
    | inr hlookup =>
        refine ⟨fields, ?_, ?_⟩
        · simp [zeroDepthResponseNameResult_of_lookup_null responseName fields
            hlookup]
        · exact Or.inr hlookup
  · cases hresponseLookup : lookupResponseField? responseName fields with
    | none =>
        refine ⟨mergeResponseField responseName .null fields, ?_, ?_⟩
        · simp [zeroDepthResponseNameResult_of_lookup_none responseName fields
            hresponseLookup]
        · cases hcompat with
          | inl htargetNone =>
              left
              rw [lookupResponseField?_mergeResponseField_other target
                responseName .null fields hsame]
              exact htargetNone
          | inr htargetNull =>
              right
              rw [lookupResponseField?_mergeResponseField_other target
                responseName .null fields hsame]
              exact htargetNull
    | some existing =>
        have hhead :=
          zeroDepthResponseNameResult_of_lookup_some_merge responseName fields
            existing hresponseLookup
        refine ⟨mergeResponseField responseName existing fields, ?_, ?_⟩
        · simp [hhead]
        · cases hcompat with
          | inl htargetNone =>
              left
              rw [lookupResponseField?_mergeResponseField_other target
                responseName existing fields hsame]
              exact htargetNone
          | inr htargetNull =>
              right
              rw [lookupResponseField?_mergeResponseField_other target
                responseName existing fields hsame]
              exact htargetNull

theorem zeroDepthExecutableGroupsResult_preserves_lookup_null_or_none (target : Name)
    : ∀ (groups : List (Name × List ExecutableField))
        (fields : List (Name × ResponseValue)),
        lookupResponseField? target fields = none
          ∨ lookupResponseField? target fields = some .null
        -> ∃ outputFields,
            (zeroDepthExecutableGroupsResult groups fields).fst = .object outputFields
            ∧ (lookupResponseField? target outputFields = none
                ∨ lookupResponseField? target outputFields = some .null)
  | [], fields, hcompat => by
      exact ⟨fields, by simp [zeroDepthExecutableGroupsResult], hcompat⟩
  | (responseName, groupFields) :: rest, fields, hcompat => by
      rcases
        zeroDepthResponseNameResult_preserves_lookup_null_or_none target
          responseName fields hcompat
      with ⟨headFields, hheadFst, hheadCompat⟩
      rcases
        zeroDepthExecutableGroupsResult_preserves_lookup_null_or_none target
          rest headFields hheadCompat
      with ⟨tailFields, htailFst, htailCompat⟩
      refine ⟨tailFields, ?_, htailCompat⟩
      simp [zeroDepthExecutableGroupsResult]
      cases hhead : zeroDepthResponseNameResult responseName fields with
      | mk headOutput headStatus =>
          have hheadObject : headOutput = .object headFields := by
            simpa [hhead] using hheadFst
          subst headOutput
          simp [htailFst]

theorem zeroDepthResponseNameResult_preserves_lookup_null
    (target responseName : Name) (fields : List (Name × ResponseValue))
    : lookupResponseField? target fields = some .null
      -> ∃ outputFields,
          (zeroDepthResponseNameResult responseName fields).fst = .object outputFields
          ∧ lookupResponseField? target outputFields = some .null := by
  intro hlookup
  by_cases hsame : target = responseName
  · subst target
    exact ⟨fields,
      by simp [zeroDepthResponseNameResult_of_lookup_null responseName fields
        hlookup],
      hlookup⟩
  · cases hresponseLookup : lookupResponseField? responseName fields with
    | none =>
        refine ⟨mergeResponseField responseName .null fields, ?_, ?_⟩
        · simp [zeroDepthResponseNameResult_of_lookup_none responseName fields
            hresponseLookup]
        · rw [lookupResponseField?_mergeResponseField_other target responseName
            .null fields hsame]
          exact hlookup
    | some existing =>
        have hhead :=
          zeroDepthResponseNameResult_of_lookup_some_merge responseName fields
            existing hresponseLookup
        refine ⟨mergeResponseField responseName existing fields, ?_, ?_⟩
        · simp [hhead]
        · rw [lookupResponseField?_mergeResponseField_other target responseName
            existing fields hsame]
          exact hlookup

theorem zeroDepthExecutableGroupsResult_preserves_lookup_null (target : Name)
    : ∀ (groups : List (Name × List ExecutableField))
        (fields : List (Name × ResponseValue)),
        lookupResponseField? target fields = some .null
        -> ∃ outputFields,
            (zeroDepthExecutableGroupsResult groups fields).fst = .object outputFields
            ∧ lookupResponseField? target outputFields = some .null
  | [], fields, hlookup => by
      exact ⟨fields, by simp [zeroDepthExecutableGroupsResult], hlookup⟩
  | (responseName, groupFields) :: rest, fields, hlookup => by
      rcases
        zeroDepthResponseNameResult_preserves_lookup_null target responseName
          fields hlookup
      with ⟨headFields, hheadFst, hheadLookup⟩
      rcases
        zeroDepthExecutableGroupsResult_preserves_lookup_null target rest
          headFields hheadLookup
      with ⟨tailFields, htailFst, htailLookup⟩
      refine ⟨tailFields, ?_, htailLookup⟩
      simp [zeroDepthExecutableGroupsResult]
      cases hhead : zeroDepthResponseNameResult responseName fields with
      | mk headOutput headStatus =>
          have hheadObject : headOutput = .object headFields := by
            simpa [hhead] using hheadFst
          subst headOutput
          simp [htailFst]

theorem zeroDepthExecutableGroupsResult_key_mem_lookup_null (target : Name)
    : ∀ (groups : List (Name × List ExecutableField))
        (outputFields : List (Name × ResponseValue)),
        PairKeysNodup groups
        -> ZeroDepthGroupsNullCompatible groups outputFields
        -> target ∈ groups.map Prod.fst
        -> ∃ resultFields,
            (zeroDepthExecutableGroupsResult groups outputFields).fst
              = .object resultFields
            ∧ lookupResponseField? target resultFields = some .null
  | [], outputFields, _hnodup, _hcompat, hmem => by
      simp at hmem
  | (responseName, fields) :: rest, outputFields, hnodup, hcompat, hmem => by
      simp at hmem
      rcases hmem with hhead | htail
      · subst responseName
        have hheadCompat := hcompat target fields (by simp)
        cases hheadCompat with
        | inl hlookupNone =>
            have hhead :=
              zeroDepthResponseNameResult_of_lookup_none target outputFields
                hlookupNone
            have htailLookup :
                lookupResponseField? target
                    (mergeResponseField target .null outputFields) =
                  some .null := by
              simpa [hlookupNone] using
                lookupResponseField?_mergeResponseField_null_same target
                  outputFields
            rcases
              zeroDepthExecutableGroupsResult_preserves_lookup_null target rest
                (mergeResponseField target .null outputFields) htailLookup
            with ⟨resultFields, hresultFst, hresultLookup⟩
            exact ⟨resultFields, by
              simp [zeroDepthExecutableGroupsResult, hhead, hresultFst],
              hresultLookup⟩
        | inr hlookupNull =>
            have hhead :=
              zeroDepthResponseNameResult_of_lookup_null target outputFields
                hlookupNull
            rcases
              zeroDepthExecutableGroupsResult_preserves_lookup_null target rest
                outputFields hlookupNull
            with ⟨resultFields, hresultFst, hresultLookup⟩
            exact ⟨resultFields, by
              simp [zeroDepthExecutableGroupsResult, hhead, hresultFst],
              hresultLookup⟩
      · have hrestCompat :
            ZeroDepthGroupsNullCompatible rest
              (match (zeroDepthResponseNameResult responseName outputFields).fst with
              | .object fields => fields
              | _ => []) := by
          intro restResponseName restFields hrestMem
          have hrestInitial :=
            hcompat restResponseName restFields (by simp [hrestMem])
          rcases
            zeroDepthResponseNameResult_preserves_lookup_null_or_none
              restResponseName responseName outputFields hrestInitial
          with ⟨headFields, hheadFst, hheadCompat⟩
          cases hhead : zeroDepthResponseNameResult responseName outputFields with
          | mk headOutput headStatus =>
              have hheadObject : headOutput = .object headFields := by
                simpa [hhead] using hheadFst
              subst headOutput
              simpa using hheadCompat
        rcases
          zeroDepthExecutableGroupsResult_key_mem_lookup_null target rest
            (match (zeroDepthResponseNameResult responseName outputFields).fst with
              | .object fields => fields
              | _ => [])
            (PairKeysNodup.tail hnodup) hrestCompat
            (by simpa [List.mem_map] using htail)
        with ⟨resultFields, hresultFst, hresultLookup⟩
        exact ⟨resultFields, by
          simp [zeroDepthExecutableGroupsResult, hresultFst],
          hresultLookup⟩

theorem zeroDepthExecutableGroupsResult_status_fresh
    : ∀ (groups : List (Name × List ExecutableField))
        (outputFields : List (Name × ResponseValue)),
        PairKeysNodup groups
        -> (∀ responseName fields,
              (responseName, fields) ∈ groups -> responseName ∉ outputFields.map Prod.fst)
        -> (zeroDepthExecutableGroupsResult groups outputFields).snd
            = depthZeroVisitStatus groups.length
  | [], outputFields, _hnodup, _hfresh => by
      simp [zeroDepthExecutableGroupsResult, depthZeroVisitStatus, visitOk]
  | (responseName, fields) :: rest, outputFields, hnodup, hfresh => by
      have hlookup :
          lookupResponseField? responseName outputFields = none :=
        lookupResponseField?_none_of_not_mem responseName outputFields
          (hfresh responseName fields (by simp))
      have hhead :=
        zeroDepthResponseNameResult_of_lookup_none responseName outputFields
          hlookup
      have hrestNodup : PairKeysNodup rest := PairKeysNodup.tail hnodup
      have hrestFresh :
          ∀ restResponseName restFields,
            (restResponseName, restFields) ∈ rest ->
              restResponseName ∉
                (mergeResponseField responseName .null outputFields).map
                  Prod.fst := by
        intro restResponseName restFields hmem hkey
        rcases
          mergeResponseField_key_mem responseName restResponseName .null
            outputFields hkey
        with hsame | hold
        · have htailKey : restResponseName ∈ rest.map Prod.fst :=
            List.mem_map.mpr ⟨(restResponseName, restFields), hmem, rfl⟩
          exact PairKeysNodup.head_not_mem_tail hnodup
            (by simpa [hsame] using htailKey)
        · exact hfresh restResponseName restFields (by simp [hmem]) hold
      have htail :=
        zeroDepthExecutableGroupsResult_status_fresh rest
          (mergeResponseField responseName .null outputFields)
          hrestNodup hrestFresh
      simp [zeroDepthExecutableGroupsResult, hhead]
      rw [htail]
      simpa [depthZeroVisitStatus, Nat.add_comm, Nat.add_left_comm] using
        combineVisitStatus_depthZeroVisitStatus 1 rest.length

theorem zeroDepthResponseNameResult_preserves_lookup_some
    (target responseName : Name) (fields : List (Name × ResponseValue))
    (existing : ResponseValue)
    : ResponseMergeReady (.object fields)
      -> lookupResponseField? target fields = some existing
      -> ∃ outputFields,
          (zeroDepthResponseNameResult responseName fields).fst = .object outputFields
          ∧ lookupResponseField? target outputFields = some existing
          ∧ ResponseMergeReady (.object outputFields) := by
  intro hready hlookup
  by_cases hsame : target = responseName
  · subst target
    have hresult :=
      zeroDepthResponseNameResult_of_lookup_some responseName fields existing
        hready hlookup
    exact ⟨fields, by simp [hresult], hlookup, hready⟩
  · cases hresponseLookup : lookupResponseField? responseName fields with
    | none =>
        have hresult :=
          zeroDepthResponseNameResult_of_lookup_none responseName fields
            hresponseLookup
        refine ⟨mergeResponseField responseName .null fields, ?_, ?_⟩
        · simp [hresult]
        · constructor
          · rw [lookupResponseField?_mergeResponseField_other target responseName
              .null fields hsame]
            exact hlookup
          · exact mergeResponseField_object_ready_of_ready responseName .null
              fields hready ResponseMergeReady.null
    | some responseExisting =>
        have hresult :=
          zeroDepthResponseNameResult_of_lookup_some responseName fields
            responseExisting hready hresponseLookup
        exact ⟨fields, by simp [hresult], hlookup, hready⟩

theorem zeroDepthExecutableGroupsResult_preserves_lookup_some (target : Name)
    : ∀ (groups : List (Name × List ExecutableField))
        (fields : List (Name × ResponseValue)) (existing : ResponseValue),
        ResponseMergeReady (.object fields)
        -> lookupResponseField? target fields = some existing
        -> ∃ outputFields,
            (zeroDepthExecutableGroupsResult groups fields).fst = .object outputFields
            ∧ lookupResponseField? target outputFields = some existing
            ∧ ResponseMergeReady (.object outputFields)
  | [], fields, existing, hready, hlookup => by
      exact ⟨fields, by simp [zeroDepthExecutableGroupsResult], hlookup,
        hready⟩
  | (responseName, groupFields) :: rest, fields, existing, hready, hlookup => by
      rcases
        zeroDepthResponseNameResult_preserves_lookup_some target responseName
          fields existing hready hlookup
      with ⟨headFields, hheadFst, hheadLookup, hheadReady⟩
      rcases
        zeroDepthExecutableGroupsResult_preserves_lookup_some target rest
          headFields existing hheadReady hheadLookup
      with ⟨tailFields, htailFst, htailLookup, htailReady⟩
      refine ⟨tailFields, ?_, htailLookup, htailReady⟩
      simp [zeroDepthExecutableGroupsResult]
      cases hhead :
          zeroDepthResponseNameResult responseName fields with
      | mk headOutput headStatus =>
          have hheadObject : headOutput = .object headFields := by
            simpa [hhead] using hheadFst
          subst headOutput
          simp [htailFst]

theorem zeroDepthExecutableGroupsResult_append
    : ∀ (left right : List (Name × List ExecutableField))
        (outputFields : List (Name × ResponseValue)),
        zeroDepthExecutableGroupsResult (left ++ right) outputFields
        = let leftResult := zeroDepthExecutableGroupsResult left outputFields
          let rightFields :=
            match leftResult.fst with
            | .object fields => fields
            | _ => []
          let rightResult := zeroDepthExecutableGroupsResult right rightFields
          (rightResult.fst, combineVisitStatus leftResult.snd rightResult.snd)
  | [], right, outputFields => by
      simp [zeroDepthExecutableGroupsResult]
  | group :: rest, right, outputFields => by
      rcases group with ⟨responseName, fields⟩
      simp [zeroDepthExecutableGroupsResult,
        zeroDepthExecutableGroupsResult_append rest right,
        combineVisitStatus_assoc]

theorem zeroDepthExecutableGroupsResult_preserves_object
    : ∀ (groups : List (Name × List ExecutableField))
        (outputFields : List (Name × ResponseValue)),
        ∃ resultFields,
          (zeroDepthExecutableGroupsResult groups outputFields).fst = .object resultFields
  | [], outputFields => by
      exact ⟨outputFields, by simp [zeroDepthExecutableGroupsResult]⟩
  | (responseName, fields) :: rest, outputFields => by
      cases hlookup : lookupResponseField? responseName outputFields with
      | none =>
          have hhead :=
            zeroDepthResponseNameResult_of_lookup_none responseName
              outputFields hlookup
          obtain ⟨resultFields, hresultFields⟩ :=
            zeroDepthExecutableGroupsResult_preserves_object rest
              (mergeResponseField responseName .null outputFields)
          exact ⟨resultFields, by simp [zeroDepthExecutableGroupsResult,
            hhead, hresultFields]⟩
      | some existing =>
          have hhead :=
            zeroDepthResponseNameResult_of_lookup_some_merge responseName
              outputFields existing hlookup
          obtain ⟨resultFields, hresultFields⟩ :=
            zeroDepthExecutableGroupsResult_preserves_object rest
              (mergeResponseField responseName existing outputFields)
          exact ⟨resultFields, by simp [zeroDepthExecutableGroupsResult,
            hhead, hresultFields]⟩

theorem zeroDepthResponseNameResult_preserves_object_ready
    (responseName : Name) (fields : List (Name × ResponseValue))
    : ResponseMergeReady (.object fields)
      -> ∃ outputFields,
          (zeroDepthResponseNameResult responseName fields).fst = .object outputFields
          ∧ ResponseMergeReady (.object outputFields) := by
  intro hready
  cases hlookup : lookupResponseField? responseName fields with
  | none =>
      refine ⟨mergeResponseField responseName .null fields, ?_, ?_⟩
      · simp [zeroDepthResponseNameResult_of_lookup_none responseName fields
          hlookup]
      · exact mergeResponseField_object_ready_of_ready responseName .null fields
          hready ResponseMergeReady.null
  | some existing =>
      refine ⟨fields, ?_, hready⟩
      simp [zeroDepthResponseNameResult_of_lookup_some responseName fields
        existing hready hlookup]

theorem zeroDepthExecutableGroupsResult_preserves_object_ready
    : ∀ (groups : List (Name × List ExecutableField))
        (outputFields : List (Name × ResponseValue)),
        ResponseMergeReady (.object outputFields)
        -> ∃ resultFields,
            (zeroDepthExecutableGroupsResult groups outputFields).fst
              = .object resultFields
            ∧ ResponseMergeReady (.object resultFields)
  | [], outputFields, hready => by
      exact ⟨outputFields, by simp [zeroDepthExecutableGroupsResult], hready⟩
  | (responseName, fields) :: rest, outputFields, hready => by
      obtain ⟨headFields, hheadFields, hheadReady⟩ :=
        zeroDepthResponseNameResult_preserves_object_ready responseName
          outputFields hready
      obtain ⟨resultFields, hresultFields, hresultReady⟩ :=
        zeroDepthExecutableGroupsResult_preserves_object_ready rest headFields
          hheadReady
      refine ⟨resultFields, ?_, hresultReady⟩
      simp [zeroDepthExecutableGroupsResult]
      cases hhead : zeroDepthResponseNameResult responseName outputFields with
      | mk headOutput headStatus =>
          have hheadObject : headOutput = .object headFields := by
            simpa [hhead] using hheadFields
          subst headOutput
          simp [hresultFields]

theorem zeroDepthExecutableGroupsResult_key_mem_lookup_some (target : Name)
    : ∀ (groups : List (Name × List ExecutableField))
        (outputFields : List (Name × ResponseValue)),
        ResponseMergeReady (.object outputFields)
        -> target ∈ groups.map Prod.fst
        -> ∃ resultFields existing,
            (zeroDepthExecutableGroupsResult groups outputFields).fst
              = .object resultFields
            ∧ lookupResponseField? target resultFields = some existing
            ∧ ResponseMergeReady (.object resultFields)
  | [], outputFields, _hready, hmem => by
      simp at hmem
  | (responseName, fields) :: rest, outputFields, hready, hmem => by
      simp at hmem
      rcases hmem with hheadName | htailName
      · subst responseName
        cases hlookup : lookupResponseField? target outputFields with
        | none =>
            have hhead :=
              zeroDepthResponseNameResult_of_lookup_none target outputFields
                hlookup
            have htailLookup :
                lookupResponseField? target
                    (mergeResponseField target .null outputFields) =
                  some .null := by
              simpa [hlookup] using
                lookupResponseField?_mergeResponseField_null_same target
                  outputFields
            rcases
              zeroDepthExecutableGroupsResult_preserves_lookup_some target rest
                (mergeResponseField target .null outputFields) .null
                (mergeResponseField_object_ready_of_ready target .null
                  outputFields hready ResponseMergeReady.null)
                htailLookup
            with ⟨resultFields, hresultFields, hresultLookup, hresultReady⟩
            exact ⟨resultFields, .null, by
              simp [zeroDepthExecutableGroupsResult, hhead, hresultFields],
              hresultLookup, hresultReady⟩
        | some existing =>
            have hhead :=
              zeroDepthResponseNameResult_of_lookup_some target outputFields
                existing hready hlookup
            rcases
              zeroDepthExecutableGroupsResult_preserves_lookup_some target rest
                outputFields existing hready hlookup
            with ⟨resultFields, hresultFields, hresultLookup, hresultReady⟩
            exact ⟨resultFields, existing, by
              simp [zeroDepthExecutableGroupsResult, hhead, hresultFields],
              hresultLookup, hresultReady⟩
      · cases hlookup : lookupResponseField? responseName outputFields with
        | none =>
            have hhead :=
              zeroDepthResponseNameResult_of_lookup_none responseName
                outputFields hlookup
            rcases
              zeroDepthExecutableGroupsResult_key_mem_lookup_some target rest
                (mergeResponseField responseName .null outputFields)
                (mergeResponseField_object_ready_of_ready responseName .null
                  outputFields hready ResponseMergeReady.null)
                (by simpa [List.mem_map] using htailName)
            with ⟨resultFields, existing, hresultFields, hresultLookup,
              hresultReady⟩
            exact ⟨resultFields, existing, by
              simp [zeroDepthExecutableGroupsResult, hhead, hresultFields],
              hresultLookup, hresultReady⟩
        | some existingResponse =>
            have hhead :=
              zeroDepthResponseNameResult_of_lookup_some responseName
                outputFields existingResponse hready hlookup
            rcases
              zeroDepthExecutableGroupsResult_key_mem_lookup_some target rest
                outputFields hready (by simpa [List.mem_map] using htailName)
            with ⟨resultFields, existing, hresultFields, hresultLookup,
              hresultReady⟩
            exact ⟨resultFields, existing, by
              simp [zeroDepthExecutableGroupsResult, hhead, hresultFields],
              hresultLookup, hresultReady⟩

theorem zeroDepthExecutableGroupsResult_append_existing_key
    (target : Name) (groupFields : List ExecutableField)
    (groups : List (Name × List ExecutableField))
    (outputFields : List (Name × ResponseValue))
    : ResponseMergeReady (.object outputFields)
      -> target ∈ groups.map Prod.fst
      -> zeroDepthExecutableGroupsResult (groups ++ [(target, groupFields)]) outputFields
          = zeroDepthExecutableGroupsResult groups outputFields := by
  intro hready hmem
  obtain ⟨prefixFields, existing, hprefixFst, hlookup, hprefixReady⟩ :=
    zeroDepthExecutableGroupsResult_key_mem_lookup_some target groups
      outputFields hready hmem
  rw [zeroDepthExecutableGroupsResult_append]
  simp [hprefixFst]
  have hsingle :=
    zeroDepthResponseNameResult_of_lookup_some target prefixFields existing
      hprefixReady hlookup
  simp [zeroDepthExecutableGroupsResult, hsingle, visitOk,
    combineVisitStatus, GraphQL.Execution.Result.combine]
  apply Prod.ext
  · exact hprefixFst.symm
  · change
      combineVisitStatus (zeroDepthExecutableGroupsResult groups outputFields).snd
          visitOk =
        (zeroDepthExecutableGroupsResult groups outputFields).snd
    exact combineVisitStatus_visitOk_right
      (zeroDepthExecutableGroupsResult groups outputFields).snd

theorem zeroDepthExecutableGroupsResult_addExecutableGroup_eq_append
    (group : Name × List ExecutableField)
    : ∀ (groups : List (Name × List ExecutableField))
        (outputFields : List (Name × ResponseValue)),
        ResponseMergeReady (.object outputFields)
        -> zeroDepthExecutableGroupsResult
              (GraphQL.Execution.addExecutableGroup group groups) outputFields
            = zeroDepthExecutableGroupsResult (groups ++ [group]) outputFields
  | [], outputFields, _hready => by
      rcases group with ⟨groupName, groupFields⟩
      simp [GraphQL.Execution.addExecutableGroup]
  | (responseName, fields) :: rest, outputFields, hready => by
      rcases group with ⟨groupName, groupFields⟩
      by_cases hname : responseName == groupName
      · have hresponse : responseName = groupName := beq_iff_eq.mp hname
        subst responseName
        have hdup :=
          zeroDepthExecutableGroupsResult_append_existing_key groupName
            groupFields ((groupName, fields) :: rest) outputFields hready
            (by simp)
        simpa [GraphQL.Execution.addExecutableGroup, hname,
          zeroDepthExecutableGroupsResult] using hdup.symm
      · obtain ⟨headFields, hheadFields, hheadReady⟩ :=
          zeroDepthResponseNameResult_preserves_object_ready responseName
            outputFields hready
        simp [GraphQL.Execution.addExecutableGroup, hname,
          zeroDepthExecutableGroupsResult]
        cases hhead : zeroDepthResponseNameResult responseName outputFields with
        | mk headOutput headStatus =>
            have hheadObject : headOutput = .object headFields := by
              simpa [hhead] using hheadFields
            subst headOutput
            simp [zeroDepthExecutableGroupsResult_addExecutableGroup_eq_append
              (groupName, groupFields) rest headFields hheadReady]

theorem zeroDepthExecutableGroupsResult_addExecutableGroup_append_eq
    (group : Name × List ExecutableField)
    (groups suffix : List (Name × List ExecutableField))
    (outputFields : List (Name × ResponseValue))
    : ResponseMergeReady (.object outputFields)
      -> zeroDepthExecutableGroupsResult
            (GraphQL.Execution.addExecutableGroup group groups ++ suffix)
            outputFields
          = zeroDepthExecutableGroupsResult ((groups ++ [group]) ++ suffix)
              outputFields := by
  intro hready
  rw [zeroDepthExecutableGroupsResult_append]
  rw [zeroDepthExecutableGroupsResult_append]
  rw [zeroDepthExecutableGroupsResult_addExecutableGroup_eq_append group groups
    outputFields hready]

theorem zeroDepthExecutableGroupsResult_mergeExecutableGroups_eq_append
    : ∀ (left right : List (Name × List ExecutableField))
        (outputFields : List (Name × ResponseValue)),
        ResponseMergeReady (.object outputFields)
        -> zeroDepthExecutableGroupsResult
              (GraphQL.Execution.mergeExecutableGroups left right) outputFields
            = zeroDepthExecutableGroupsResult (left ++ right) outputFields
  | left, [], outputFields, _hready => by
      simp [GraphQL.Execution.mergeExecutableGroups]
  | left, group :: rest, outputFields, hready => by
      change
        zeroDepthExecutableGroupsResult
            (GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.addExecutableGroup group left) rest)
            outputFields =
          zeroDepthExecutableGroupsResult (left ++ group :: rest) outputFields
      rw [zeroDepthExecutableGroupsResult_mergeExecutableGroups_eq_append
        (GraphQL.Execution.addExecutableGroup group left) rest outputFields
        hready]
      rw [zeroDepthExecutableGroupsResult_addExecutableGroup_append_eq group
        left rest outputFields hready]
      simp [List.append_assoc]

mutual
  theorem visitSelection_depth_zero_eq_zeroDepthExecutableGroupsResult_collectSelection
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selection : Selection) (outputFields : List (Name × ResponseValue)),
          ResponseMergeReady (.object outputFields)
          -> visitSelection schema resolvers variableValues 0 parentType source
                selection (.object outputFields)
              = zeroDepthExecutableGroupsResult
                  (GraphQL.Execution.collectSelection schema variableValues
                    parentType source selection)
                  outputFields
    | .field responseName fieldName arguments directives selectionSet,
        outputFields, hready => by
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · cases hlookup : lookupResponseField? responseName outputFields with
          | none =>
              have hprevious :
                  responseObjectField? responseName (.object outputFields) =
                    none := by
                simpa [responseObjectField?] using hlookup
              simp [visitSelection, hallowed, GraphQL.Execution.collectSelection,
                zeroDepthExecutableGroupsResult,
                zeroDepthResponseNameResult_of_lookup_none responseName
                  outputFields hlookup,
                hprevious, mergeResponseFieldResult, mergeResponseFieldIntoObject,
                GraphQL.Execution.outOfFuel, resultValueOrNull, resultStatus]
          | some existing =>
              have hprevious :
                  responseObjectField? responseName (.object outputFields) =
                    some existing := by
                simpa [responseObjectField?] using hlookup
              have hmerge :
                  mergeResponseField responseName existing outputFields =
                    outputFields :=
                mergeResponseField_self_of_lookup_some_ready responseName
                  outputFields existing hready hlookup
              simp [visitSelection, hallowed, GraphQL.Execution.collectSelection,
                zeroDepthExecutableGroupsResult,
                zeroDepthResponseNameResult_of_lookup_some responseName
                  outputFields existing hready hlookup,
                hprevious, mergeResponseFieldResult, mergeResponseFieldIntoObject,
                hmerge, resultValueOrNull, resultStatus]
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [visitSelection, hblocked, GraphQL.Execution.collectSelection,
            zeroDepthExecutableGroupsResult]
    | .inlineFragment none directives selectionSet, outputFields, hready => by
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · simpa [visitSelection, hallowed, GraphQL.Execution.collectSelection]
            using
              visitSubfields_depth_zero_eq_zeroDepthExecutableGroupsResult_collectFields
                schema resolvers variableValues parentType source selectionSet
                outputFields hready
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [visitSelection, hblocked, GraphQL.Execution.collectSelection,
            zeroDepthExecutableGroupsResult]
    | .inlineFragment (some typeCondition) directives selectionSet,
        outputFields, hready => by
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · by_cases happly :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                true
          · simpa [visitSelection, hallowed, happly,
              GraphQL.Execution.collectSelection]
              using
                visitSubfields_depth_zero_eq_zeroDepthExecutableGroupsResult_collectFields
                  schema resolvers variableValues parentType source selectionSet
                  outputFields hready
          · have hnotApply :
                doesFragmentTypeApplyBool schema parentType source typeCondition =
                  false := by
              cases h :
                  doesFragmentTypeApplyBool schema parentType source typeCondition
              · rfl
              · contradiction
            simp [visitSelection, hallowed, hnotApply,
              GraphQL.Execution.collectSelection, zeroDepthExecutableGroupsResult]
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [visitSelection, hblocked, GraphQL.Execution.collectSelection,
            zeroDepthExecutableGroupsResult]

  theorem visitSubfields_depth_zero_eq_zeroDepthExecutableGroupsResult_collectFields
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selectionSet : List Selection) (outputFields : List (Name × ResponseValue)),
          ResponseMergeReady (.object outputFields)
          -> visitSubfields schema resolvers variableValues 0 parentType source
                selectionSet (.object outputFields)
              = zeroDepthExecutableGroupsResult
                  (GraphQL.Execution.collectFields schema variableValues parentType
                    source selectionSet)
                  outputFields
    | [], outputFields, _hready => by
        simp [visitSubfields, GraphQL.Execution.collectFields,
          zeroDepthExecutableGroupsResult]
    | selection :: rest, outputFields, hready => by
        let leftGroups :=
          GraphQL.Execution.collectSelection schema variableValues parentType
            source selection
        let rightGroups :=
          GraphQL.Execution.collectFields schema variableValues parentType source
            rest
        obtain ⟨leftFields, hleftFields, hleftReady⟩ :=
          zeroDepthExecutableGroupsResult_preserves_object_ready leftGroups
            outputFields hready
        let leftStatus :=
          (zeroDepthExecutableGroupsResult leftGroups outputFields).snd
        have hleft :
            zeroDepthExecutableGroupsResult leftGroups outputFields =
              (.object leftFields, leftStatus) :=
          Prod.ext hleftFields rfl
        have hselection :=
          visitSelection_depth_zero_eq_zeroDepthExecutableGroupsResult_collectSelection
            schema resolvers variableValues parentType source selection
            outputFields hready
        have hrest :=
          visitSubfields_depth_zero_eq_zeroDepthExecutableGroupsResult_collectFields
            schema resolvers variableValues parentType source rest leftFields
            hleftReady
        rw [visitSubfields]
        rw [hselection]
        rw [hleft]
        rw [hrest]
        simp [GraphQL.Execution.collectFields, leftGroups]
        rw [zeroDepthExecutableGroupsResult_mergeExecutableGroups_eq_append
          leftGroups rightGroups outputFields hready]
        rw [zeroDepthExecutableGroupsResult_append]
        simp [leftGroups, rightGroups, hleft]
end

theorem VisitSubfieldsFlatCollects_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (outputFields : List (Name × ResponseValue))
    : ResponseMergeReady (.object outputFields)
      -> VisitSubfieldsFlatCollects schema resolvers variableValues 0 parentType
          source selectionSet (.object outputFields) := by
  intro hready
  unfold VisitSubfieldsFlatCollects
  rw [visitSubfields_depth_zero_eq_zeroDepthExecutableGroupsResult_collectFields
    schema resolvers variableValues parentType source selectionSet
    outputFields hready]
  rw [visitSubfields_depth_zero_eq_zeroDepthExecutableGroupsResult_collectFields
    schema resolvers variableValues parentType source
    (collectedExecutableSelections
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet))
    outputFields hready]
  rw [collectFields_executableFieldSelections_collectedExecutableFields_collectFields
    schema variableValues parentType source selectionSet]

theorem ExecutableGroupsFlatSpecEquivalent_depth_zero_general
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnodup : PairKeysNodup groups)
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues 0
        parentType source groups := by
  unfold ExecutableGroupsFlatSpecEquivalent
  have hspec :=
    specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
      schema resolvers variableValues 0 parentType source groups hnodup
      hnonempty
  have hcollected :=
    executeCollectedFields_depth_zero_nonempty schema resolvers variableValues
      parentType source groups hnonempty
  cases groups with
  | nil =>
      simp [executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
        collectedExecutableSelections,
        GraphQL.Execution.collectFields, GraphQL.Execution.executeCollectedFields,
        visitSubfields, visitOk]
  | cons group rest =>
      have hstatus :=
        zeroDepthExecutableGroupsResult_status_fresh (group :: rest) []
          hnodup
          (by
            intro responseName fields hmem
            simp)
      unfold executeRootSelectionSet
      rw [visitSubfields_depth_zero_eq_zeroDepthExecutableGroupsResult_collectFields
        schema resolvers variableValues parentType source
        (collectedExecutableSelections (group :: rest)) []
        ResponseMergeReady_empty_object]
      rw [collectFields_executableFieldSelections_collectedExecutableFields
        schema variableValues parentType source (group :: rest) hnodup hnonempty]
      cases hzero : zeroDepthExecutableGroupsResult (group :: rest) [] with
      | mk output status =>
          have hstatus' :
              status = depthZeroVisitStatus (group :: rest).length := by
            simpa [hzero] using hstatus
          rw [hstatus']
          rw [hspec]
          rw [hcollected]
          simp [depthZeroVisitStatus]

theorem VisitSubfieldsFlatCollectsFreshPrefixes_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : ∀ fields,
        (∀ entry,
          entry
            ∈ collectedExecutableEntries
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source selectionSet)
          -> entry.1 ∉ fields.map Prod.fst)
        -> ResponseMergeReady (.object fields)
        -> VisitSubfieldsFlatCollects schema resolvers variableValues 0
            parentType source selectionSet (.object fields) := by
  intro fields _hfresh hready
  exact
    VisitSubfieldsFlatCollects_depth_zero schema resolvers variableValues
      parentType source selectionSet fields hready

theorem VisitSubfieldsFlatCollectsFreshPrefixes_all
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : executionSelectionSetLookupValid schema parentType selectionSet
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source selectionSet := by
  intro hlookupValid
  rcases
      SelectionSetFreshPlanNormalizes.executablePrefixRawNormalizes
        (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth) (parentType := parentType)
        (source := source)
        ([] : List FreshPrefixSelectionDerivation.KeyedExecutableField)
        (by
          intro field hfield
          simp at hfield)
        selectionSet hlookupValid with
    ⟨normalized, hnormalized⟩
  simpa [FreshPrefixSelectionDerivation.keyedExecutableFieldSelections] using
    hnormalized.rawFreshFlat

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
