import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Absorption
import Proofs.GraphQL.Execution.ResolverValue

/-!
Semantic slice/fold view of ungrouped execution.

The operational algorithm still visits selections directly. This module exposes a
proof-facing fold over field slices, so equivalence proofs can reason about
accumulating response slices and absorption instead of normalizing raw selection
order syntactically.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

def visitSelectionFold
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (output : ResponseValue)
    : ResponseValue :=
  selectionSet.foldl
    (fun output selection =>
      (visitSelection schema resolvers variableValues depth parentType source
        selection output).fst)
    output

theorem visitSelectionFold_eq_visitSubfields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ (selectionSet : List Selection) (output : ResponseValue),
        visitSelectionFold schema resolvers variableValues depth parentType
          source selectionSet output
        = (visitSubfields schema resolvers variableValues depth parentType source
            selectionSet output).fst
  | [], output => by
      simp [visitSelectionFold, visitSubfields]
  | selection :: rest, output => by
      simpa [visitSelectionFold, visitSubfields] using
        visitSelectionFold_eq_visitSubfields schema resolvers variableValues
          depth parentType source rest
          (visitSelection schema resolvers variableValues depth parentType
            source selection output).fst

def visitFieldSliceResult
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (output : ResponseValue)
    : ResponseValue × VisitStatus :=
  let previous? := responseObjectField? field.responseName output
  match selectionDepth with
  | 0 =>
      let fieldResult :=
        match previous? with
        | some previous => .ok (previous, 0)
        | none => outOfFuel
      mergeResponseFieldResult field.responseName fieldResult output
  | completionDepth + 1 =>
      let fieldResult :=
        executeField schema resolvers variableValues completionDepth source
          previous? field
      mergeResponseFieldResult field.responseName fieldResult output

def visitFieldSlice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (output : ResponseValue)
    : ResponseValue :=
  (visitFieldSliceResult schema resolvers variableValues selectionDepth source
    field output).fst

def visitFieldSliceFoldResult
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    : List ExecutableField -> ResponseValue -> ResponseValue × VisitStatus
  | [], output => (output, visitOk)
  | field :: rest, output =>
      let head :=
        visitFieldSliceResult schema resolvers variableValues selectionDepth
          source field output
      let tail :=
        visitFieldSliceFoldResult schema resolvers variableValues selectionDepth
          source rest head.fst
      (tail.fst, combineVisitStatus head.snd tail.snd)

def visitFieldSliceFold
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) (output : ResponseValue)
    : ResponseValue :=
  fields.foldl
    (fun output field =>
      visitFieldSlice schema resolvers variableValues selectionDepth source field output)
    output

theorem visitFieldSliceResult_fst_eq_visitFieldSlice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (output : ResponseValue)
    : (visitFieldSliceResult schema resolvers variableValues selectionDepth
        source field output).fst
      = visitFieldSlice schema resolvers variableValues selectionDepth source field
          output := by
  cases output <;> cases selectionDepth <;>
    simp [visitFieldSliceResult, visitFieldSlice, mergeResponseFieldResult]

theorem visitFieldSliceFoldResult_fst_eq_visitFieldSliceFold
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    : ∀ (fields : List ExecutableField) (output : ResponseValue),
        (visitFieldSliceFoldResult schema resolvers variableValues selectionDepth
          source fields output).fst
        = visitFieldSliceFold schema resolvers variableValues selectionDepth source
            fields output
  | [], output => by
      simp [visitFieldSliceFoldResult, visitFieldSliceFold]
  | field :: rest, output => by
      simp [visitFieldSliceFoldResult, visitFieldSliceFold,
        visitFieldSliceResult_fst_eq_visitFieldSlice schema resolvers
          variableValues selectionDepth source field output,
        visitFieldSliceFoldResult_fst_eq_visitFieldSliceFold schema resolvers
          variableValues selectionDepth source rest
          (visitFieldSlice schema resolvers variableValues selectionDepth
            source field output)]

theorem visitFieldSliceFoldResult_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    : ∀ (left right : List ExecutableField) (output : ResponseValue),
        visitFieldSliceFoldResult schema resolvers variableValues selectionDepth
          source (left ++ right) output
        = let leftResult :=
            visitFieldSliceFoldResult schema resolvers variableValues
              selectionDepth source left output
          let rightResult :=
            visitFieldSliceFoldResult schema resolvers variableValues
              selectionDepth source right leftResult.fst
          (rightResult.fst, combineVisitStatus leftResult.snd rightResult.snd)
  | [], _right, _output => by
      simp [visitFieldSliceFoldResult]
  | _field :: rest, right, output => by
      simp [visitFieldSliceFoldResult,
        visitFieldSliceFoldResult_append schema resolvers variableValues
          selectionDepth source rest right,
        combineVisitStatus_assoc]

theorem visitFieldSliceResult_snd_eq_of_responseObjectField_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (left right : ResponseValue)
    (hlookup
      : responseObjectField? field.responseName left
        = responseObjectField? field.responseName right)
    : (visitFieldSliceResult schema resolvers variableValues selectionDepth
        source field left).snd
      = (visitFieldSliceResult schema resolvers variableValues selectionDepth
          source field right).snd := by
  cases selectionDepth with
  | zero =>
      cases hright : responseObjectField? field.responseName right with
      | none =>
          have hleft :
              responseObjectField? field.responseName left = none := by
            simpa [hright] using hlookup
          simp [visitFieldSliceResult, mergeResponseFieldResult, hleft,
            hright, outOfFuel]
      | some previous =>
          have hleft :
              responseObjectField? field.responseName left =
                some previous := by
            simpa [hright] using hlookup
          simp [visitFieldSliceResult, mergeResponseFieldResult, hleft, hright]
  | succ completionDepth =>
      cases hright : responseObjectField? field.responseName right with
      | none =>
          have hleft :
              responseObjectField? field.responseName left = none := by
            simpa [hright] using hlookup
          simp [visitFieldSliceResult, mergeResponseFieldResult, hleft, hright]
      | some previous =>
          have hleft :
              responseObjectField? field.responseName left = some previous := by
            simpa [hright] using hlookup
          cases previous <;>
            simp [visitFieldSliceResult, mergeResponseFieldResult, hleft,
              hright]

theorem visitFieldSliceResult_snd_mergeResponseFieldIntoObject_other
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (responseName : Name)
    (incoming output : ResponseValue)
    (hne : field.responseName ≠ responseName)
    : (visitFieldSliceResult schema resolvers variableValues selectionDepth
        source field (mergeResponseFieldIntoObject responseName incoming output)).snd
      = (visitFieldSliceResult schema resolvers variableValues selectionDepth
          source field output).snd := by
  cases output with
  | null =>
      simp [mergeResponseFieldIntoObject]
  | scalar value =>
      simp [mergeResponseFieldIntoObject]
  | list values =>
      simp [mergeResponseFieldIntoObject]
  | object fields =>
      exact
        visitFieldSliceResult_snd_eq_of_responseObjectField_eq schema resolvers
          variableValues selectionDepth source field
          (mergeResponseFieldIntoObject responseName incoming (.object fields))
          (.object fields)
          (responseObjectField?_mergeResponseFieldIntoObject_other
            field.responseName responseName incoming fields hne)

theorem responseObjectField?_visitFieldSliceResult_object_fst_other
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (target : Name)
    (fields : List (Name × ResponseValue))
    (hne : target ≠ field.responseName)
    : responseObjectField? target
        (visitFieldSliceResult schema resolvers variableValues selectionDepth
          source field (.object fields)).fst
      = responseObjectField? target (.object fields) := by
  cases selectionDepth with
  | zero =>
      cases hfield :
          responseObjectField? field.responseName (.object fields) with
      | none =>
          simp [visitFieldSliceResult, mergeResponseFieldResult, hfield,
            outOfFuel,
            responseObjectField?_mergeResponseFieldIntoObject_other target
              field.responseName _ fields hne]
      | some previous =>
          simp [visitFieldSliceResult, mergeResponseFieldResult, hfield,
            responseObjectField?_mergeResponseFieldIntoObject_other target
              field.responseName _ fields hne]
  | succ completionDepth =>
      cases hfield :
          responseObjectField? field.responseName (.object fields) with
      | none =>
          simp [visitFieldSliceResult, mergeResponseFieldResult, hfield,
            responseObjectField?_mergeResponseFieldIntoObject_other target
              field.responseName _ fields hne]
      | some previous =>
          cases previous <;>
            simp [visitFieldSliceResult, mergeResponseFieldResult, hfield,
              responseObjectField?_mergeResponseFieldIntoObject_other target
                field.responseName _ fields hne]

theorem responseObjectField?_visitFieldSliceResult_object_fst_eq_of_lookup_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (target : Name)
    (leftFields rightFields : List (Name × ResponseValue))
    (htarget
      : responseObjectField? target (.object leftFields)
        = responseObjectField? target (.object rightFields))
    (hfield
      : responseObjectField? field.responseName (.object leftFields)
        = responseObjectField? field.responseName (.object rightFields))
    : responseObjectField? target
        (visitFieldSliceResult schema resolvers variableValues selectionDepth
          source field (.object leftFields)).fst
      = responseObjectField? target
          (visitFieldSliceResult schema resolvers variableValues selectionDepth
            source field (.object rightFields)).fst := by
  by_cases hsame : target = field.responseName
  · subst target
    cases selectionDepth with
    | zero =>
        cases hright :
            responseObjectField? field.responseName (.object rightFields) with
        | none =>
            have hleft :
                responseObjectField? field.responseName (.object leftFields) =
                  none := by
              simpa [hright] using hfield
            simp [visitFieldSliceResult, mergeResponseFieldResult, hleft,
              hright, outOfFuel,
              responseObjectField?_mergeResponseFieldIntoObject_same]
        | some previous =>
            have hleft :
                responseObjectField? field.responseName (.object leftFields) =
                  some previous := by
              simpa [hright] using hfield
            simp [visitFieldSliceResult, mergeResponseFieldResult, hleft,
              hright, responseObjectField?_mergeResponseFieldIntoObject_same]
    | succ completionDepth =>
        cases hright :
            responseObjectField? field.responseName (.object rightFields) with
        | none =>
            have hleft :
                responseObjectField? field.responseName (.object leftFields) =
                  none := by
              simpa [hright] using hfield
            simp [visitFieldSliceResult, mergeResponseFieldResult, hleft,
              hright, responseObjectField?_mergeResponseFieldIntoObject_same]
        | some previous =>
            have hleft :
                responseObjectField? field.responseName (.object leftFields) =
                  some previous := by
              simpa [hright] using hfield
            cases previous <;>
              simp [visitFieldSliceResult, mergeResponseFieldResult, hleft,
                hright, responseObjectField?_mergeResponseFieldIntoObject_same]
  · cases selectionDepth with
    | zero =>
        cases hright :
            responseObjectField? field.responseName (.object rightFields) with
        | none =>
            have hleft :
                responseObjectField? field.responseName (.object leftFields) =
                  none := by
              simpa [hright] using hfield
            simp [visitFieldSliceResult, mergeResponseFieldResult, hleft,
              hright, outOfFuel,
              responseObjectField?_mergeResponseFieldIntoObject_other target
                field.responseName _ leftFields hsame,
              responseObjectField?_mergeResponseFieldIntoObject_other target
                field.responseName _ rightFields hsame,
              htarget]
        | some previous =>
            have hleft :
                responseObjectField? field.responseName (.object leftFields) =
                  some previous := by
              simpa [hright] using hfield
            simp [visitFieldSliceResult, mergeResponseFieldResult, hleft,
              hright,
              responseObjectField?_mergeResponseFieldIntoObject_other target
                field.responseName _ leftFields hsame,
              responseObjectField?_mergeResponseFieldIntoObject_other target
                field.responseName _ rightFields hsame,
              htarget]
    | succ completionDepth =>
        cases hright :
            responseObjectField? field.responseName (.object rightFields) with
        | none =>
            have hleft :
                responseObjectField? field.responseName (.object leftFields) =
                  none := by
              simpa [hright] using hfield
            simp [visitFieldSliceResult, mergeResponseFieldResult, hleft,
              hright,
              responseObjectField?_mergeResponseFieldIntoObject_other target
                field.responseName _ leftFields hsame,
              responseObjectField?_mergeResponseFieldIntoObject_other target
                field.responseName _ rightFields hsame,
              htarget]
        | some previous =>
            have hleft :
                responseObjectField? field.responseName (.object leftFields) =
                  some previous := by
              simpa [hright] using hfield
            cases previous <;>
              simp [visitFieldSliceResult, mergeResponseFieldResult, hleft,
                hright,
                responseObjectField?_mergeResponseFieldIntoObject_other target
                  field.responseName _ leftFields hsame,
                responseObjectField?_mergeResponseFieldIntoObject_other target
                  field.responseName _ rightFields hsame,
                htarget]

theorem visitFieldSliceResult_object_fst
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (fields : List (Name × ResponseValue))
    : ∃ outputFields,
        (visitFieldSliceResult schema resolvers variableValues selectionDepth
          source field (.object fields)).fst
        = .object outputFields := by
  cases selectionDepth with
  | zero =>
      cases hfield :
        responseObjectField? field.responseName (.object fields) with
      | none =>
          simp [visitFieldSliceResult, mergeResponseFieldResult,
            mergeResponseFieldIntoObject, hfield, outOfFuel]
      | some previous =>
          simp [visitFieldSliceResult, mergeResponseFieldResult,
            mergeResponseFieldIntoObject, hfield]
  | succ completionDepth =>
      cases hfield :
        responseObjectField? field.responseName (.object fields) with
      | none =>
          simp [visitFieldSliceResult, mergeResponseFieldResult,
            mergeResponseFieldIntoObject, hfield]
      | some previous =>
          cases previous <;>
            simp [visitFieldSliceResult, mergeResponseFieldResult,
              mergeResponseFieldIntoObject, hfield]

theorem visitFieldSliceFoldResult_snd_eq_of_object_lookups
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    : ∀ (fields : List ExecutableField)
          (leftFields rightFields : List (Name × ResponseValue)),
        (∀ field,
          field ∈ fields
          -> responseObjectField? field.responseName (.object leftFields)
              = responseObjectField? field.responseName (.object rightFields))
        -> (visitFieldSliceFoldResult schema resolvers variableValues selectionDepth
              source fields (.object leftFields)).snd
            = (visitFieldSliceFoldResult schema resolvers variableValues selectionDepth
                source fields (.object rightFields)).snd
  | [], leftFields, rightFields, _hlookups => by
      simp [visitFieldSliceFoldResult]
  | field :: rest, leftFields, rightFields, hlookups => by
      have hheadLookup :
          responseObjectField? field.responseName (.object leftFields) =
          responseObjectField? field.responseName (.object rightFields) :=
        hlookups field (by simp)
      have hheadStatus :
          (visitFieldSliceResult schema resolvers variableValues selectionDepth
            source field (.object leftFields)).snd =
          (visitFieldSliceResult schema resolvers variableValues selectionDepth
            source field (.object rightFields)).snd :=
        visitFieldSliceResult_snd_eq_of_responseObjectField_eq schema
          resolvers variableValues selectionDepth source field
          (.object leftFields) (.object rightFields) hheadLookup
      rcases
        visitFieldSliceResult_object_fst schema resolvers variableValues
          selectionDepth source field leftFields with
        ⟨leftHeadFields, hleftHead⟩
      rcases
        visitFieldSliceResult_object_fst schema resolvers variableValues
          selectionDepth source field rightFields with
        ⟨rightHeadFields, hrightHead⟩
      have htailLookups :
          ∀ candidate, candidate ∈ rest ->
            responseObjectField? candidate.responseName
                (.object leftHeadFields) =
              responseObjectField? candidate.responseName
                (.object rightHeadFields) := by
        intro candidate hcandidate
        have hcandidateLookup :
            responseObjectField? candidate.responseName (.object leftFields) =
            responseObjectField? candidate.responseName (.object rightFields) :=
          hlookups candidate (by simp [hcandidate])
        have hpreserve :=
          responseObjectField?_visitFieldSliceResult_object_fst_eq_of_lookup_eq
            schema resolvers variableValues selectionDepth source field
            candidate.responseName leftFields rightFields hcandidateLookup
            hheadLookup
        rw [hleftHead, hrightHead] at hpreserve
        exact hpreserve
      have htailStatus :
          (visitFieldSliceFoldResult schema resolvers variableValues
            selectionDepth source rest (.object leftHeadFields)).snd =
          (visitFieldSliceFoldResult schema resolvers variableValues
            selectionDepth source rest (.object rightHeadFields)).snd :=
        visitFieldSliceFoldResult_snd_eq_of_object_lookups schema resolvers
          variableValues selectionDepth source rest leftHeadFields
          rightHeadFields htailLookups
      simp only [visitFieldSliceFoldResult]
      rw [hheadStatus, hleftHead, hrightHead, htailStatus]

theorem responseObjectField?_visitFieldSliceFoldResult_object_fst_eq_of_object_lookups
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (target : Name)
    : ∀ (fields : List ExecutableField)
          (leftFields rightFields : List (Name × ResponseValue)),
        responseObjectField? target (.object leftFields)
          = responseObjectField? target (.object rightFields)
        -> (∀ field,
              field ∈ fields
              -> responseObjectField? field.responseName (.object leftFields)
                  = responseObjectField? field.responseName (.object rightFields))
        -> responseObjectField? target
              (visitFieldSliceFoldResult schema resolvers variableValues
                selectionDepth source fields (.object leftFields)).fst
            = responseObjectField? target
                (visitFieldSliceFoldResult schema resolvers variableValues
                  selectionDepth source fields (.object rightFields)).fst
  | [], leftFields, rightFields, htarget, _hlookups => by
      simpa [visitFieldSliceFoldResult] using htarget
  | field :: rest, leftFields, rightFields, htarget, hlookups => by
      have hheadLookup :
          responseObjectField? field.responseName (.object leftFields) =
          responseObjectField? field.responseName (.object rightFields) :=
        hlookups field (by simp)
      rcases
        visitFieldSliceResult_object_fst schema resolvers variableValues
          selectionDepth source field leftFields with
        ⟨leftHeadFields, hleftHead⟩
      rcases
        visitFieldSliceResult_object_fst schema resolvers variableValues
          selectionDepth source field rightFields with
        ⟨rightHeadFields, hrightHead⟩
      have htargetAfterHead :
          responseObjectField? target (.object leftHeadFields) =
            responseObjectField? target (.object rightHeadFields) := by
        have hpreserve :=
          responseObjectField?_visitFieldSliceResult_object_fst_eq_of_lookup_eq
            schema resolvers variableValues selectionDepth source field target
            leftFields rightFields htarget hheadLookup
        rw [hleftHead, hrightHead] at hpreserve
        exact hpreserve
      have htailLookups :
          ∀ candidate, candidate ∈ rest ->
            responseObjectField? candidate.responseName
                (.object leftHeadFields) =
              responseObjectField? candidate.responseName
                (.object rightHeadFields) := by
        intro candidate hcandidate
        have hcandidateLookup :
            responseObjectField? candidate.responseName (.object leftFields) =
            responseObjectField? candidate.responseName (.object rightFields) :=
          hlookups candidate (by simp [hcandidate])
        have hpreserve :=
          responseObjectField?_visitFieldSliceResult_object_fst_eq_of_lookup_eq
            schema resolvers variableValues selectionDepth source field
            candidate.responseName leftFields rightFields hcandidateLookup
            hheadLookup
        rw [hleftHead, hrightHead] at hpreserve
        exact hpreserve
      simp only [visitFieldSliceFoldResult]
      rw [hleftHead, hrightHead]
      exact
        responseObjectField?_visitFieldSliceFoldResult_object_fst_eq_of_object_lookups
          schema resolvers variableValues selectionDepth source target rest
          leftHeadFields rightHeadFields htargetAfterHead htailLookups

theorem responseObjectField?_visitFieldSliceFoldResult_object_fst_of_not_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (target : Name)
    : ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
        target ∉ fields.map (fun field => field.responseName)
        -> responseObjectField? target
              (visitFieldSliceFoldResult schema resolvers variableValues
                selectionDepth source fields (.object outputFields)).fst
            = responseObjectField? target (.object outputFields)
  | [], outputFields, _hnot => by
      simp [visitFieldSliceFoldResult]
  | field :: rest, outputFields, hnot => by
      have hfield : target ≠ field.responseName := by
        intro heq
        exact hnot (by simp [heq])
      have hrest :
          target ∉ rest.map (fun field => field.responseName) := by
        intro hmem
        exact hnot (by simp [hmem])
      rcases
        visitFieldSliceResult_object_fst schema resolvers variableValues
          selectionDepth source field outputFields with
        ⟨headFields, hhead⟩
      simp only [visitFieldSliceFoldResult]
      rw [hhead]
      exact
        (responseObjectField?_visitFieldSliceFoldResult_object_fst_of_not_mem
          schema resolvers variableValues selectionDepth source target rest
          headFields hrest).trans
          (by
            rw [← hhead]
            exact
              responseObjectField?_visitFieldSliceResult_object_fst_other
                schema resolvers variableValues selectionDepth source field
                target outputFields hfield)

theorem visitFieldSliceFoldResult_object_fst
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    : ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
        ∃ resultFields,
          (visitFieldSliceFoldResult schema resolvers variableValues
            selectionDepth source fields (.object outputFields)).fst
          = .object resultFields
  | [], outputFields => by
      exact ⟨outputFields, by simp [visitFieldSliceFoldResult]⟩
  | field :: rest, outputFields => by
      rcases
        visitFieldSliceResult_object_fst schema resolvers variableValues
          selectionDepth source field outputFields with
        ⟨headFields, hhead⟩
      rcases
        visitFieldSliceFoldResult_object_fst schema resolvers variableValues
          selectionDepth source rest headFields with
        ⟨resultFields, hresult⟩
      exact ⟨resultFields, by simp [visitFieldSliceFoldResult, hhead, hresult]⟩

theorem visitFieldSliceFoldResult_snd_middle_existing_last_swap
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (middle : List ExecutableField) (later : ExecutableField)
    (fields : List (Name × ResponseValue))
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    : (visitFieldSliceFoldResult schema resolvers variableValues selectionDepth
        source (middle ++ [later]) (.object fields)).snd
      = (visitFieldSliceFoldResult schema resolvers variableValues selectionDepth
          source (later :: middle) (.object fields)).snd := by
  have hmiddleLaterLookup :
      responseObjectField? later.responseName
          (visitFieldSliceFoldResult schema resolvers variableValues
            selectionDepth source middle (.object fields)).fst =
        responseObjectField? later.responseName (.object fields) :=
    responseObjectField?_visitFieldSliceFoldResult_object_fst_of_not_mem
      schema resolvers variableValues selectionDepth source later.responseName
      middle fields hnotMiddle
  rcases
    visitFieldSliceFoldResult_object_fst schema resolvers variableValues
      selectionDepth source middle fields with
    ⟨middleFields, hmiddleFields⟩
  have hmiddleLaterLookupObject :
      responseObjectField? later.responseName (.object middleFields) =
        responseObjectField? later.responseName (.object fields) := by
    simpa [hmiddleFields] using hmiddleLaterLookup
  have hlaterStatusAfterMiddle :
      (visitFieldSliceFoldResult schema resolvers variableValues
        selectionDepth source [later] (.object middleFields)).snd =
      (visitFieldSliceFoldResult schema resolvers variableValues
        selectionDepth source [later] (.object fields)).snd := by
    apply
      visitFieldSliceFoldResult_snd_eq_of_object_lookups schema resolvers
        variableValues selectionDepth source [later] middleFields fields
    intro field hfield
    simp only [List.mem_singleton] at hfield
    subst field
    exact hmiddleLaterLookupObject
  rcases
    visitFieldSliceResult_object_fst schema resolvers variableValues
      selectionDepth source later fields with
    ⟨laterFields, hlaterFields⟩
  have hmiddleLookupsAfterLater :
      ∀ field, field ∈ middle ->
        responseObjectField? field.responseName (.object laterFields) =
          responseObjectField? field.responseName (.object fields) := by
    intro field hfield
    have hne : field.responseName ≠ later.responseName := by
      intro heq
      exact hnotMiddle (List.mem_map.mpr ⟨field, hfield, heq⟩)
    rw [← hlaterFields]
    exact
      responseObjectField?_visitFieldSliceResult_object_fst_other schema
        resolvers variableValues selectionDepth source later
        field.responseName fields hne
  have hmiddleStatusAfterLater :
      (visitFieldSliceFoldResult schema resolvers variableValues
        selectionDepth source middle (.object laterFields)).snd =
      (visitFieldSliceFoldResult schema resolvers variableValues
        selectionDepth source middle (.object fields)).snd :=
    visitFieldSliceFoldResult_snd_eq_of_object_lookups schema resolvers
      variableValues selectionDepth source middle laterFields fields
      hmiddleLookupsAfterLater
  rw [visitFieldSliceFoldResult_append schema resolvers variableValues
    selectionDepth source middle [later] (.object fields)]
  simp only
  rw [hmiddleFields]
  simp only [visitFieldSliceFoldResult]
  have hlaterStepStatusAfterMiddle :
      (visitFieldSliceResult schema resolvers variableValues selectionDepth
        source later (.object middleFields)).snd =
      (visitFieldSliceResult schema resolvers variableValues selectionDepth
        source later (.object fields)).snd := by
    simpa [visitFieldSliceFoldResult] using hlaterStatusAfterMiddle
  rw [hlaterFields, hlaterStepStatusAfterMiddle,
    hmiddleStatusAfterLater]
  simp [combineVisitStatus_comm]

theorem responseObjectField?_visitFieldSliceFoldResult_middle_existing_last_swap
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (middle : List ExecutableField) (later : ExecutableField)
    (fields : List (Name × ResponseValue)) (target : Name)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    : responseObjectField? target
        (visitFieldSliceFoldResult schema resolvers variableValues
          selectionDepth source (middle ++ [later]) (.object fields)).fst
      = responseObjectField? target
          (visitFieldSliceFoldResult schema resolvers variableValues
            selectionDepth source (later :: middle) (.object fields)).fst := by
  have hmiddleLaterLookup :
      responseObjectField? later.responseName
          (visitFieldSliceFoldResult schema resolvers variableValues
            selectionDepth source middle (.object fields)).fst =
        responseObjectField? later.responseName (.object fields) :=
    responseObjectField?_visitFieldSliceFoldResult_object_fst_of_not_mem
      schema resolvers variableValues selectionDepth source later.responseName
      middle fields hnotMiddle
  rcases
    visitFieldSliceFoldResult_object_fst schema resolvers variableValues
      selectionDepth source middle fields with
    ⟨middleFields, hmiddleFields⟩
  have hmiddleLaterLookupObject :
      responseObjectField? later.responseName (.object middleFields) =
        responseObjectField? later.responseName (.object fields) := by
    simpa [hmiddleFields] using hmiddleLaterLookup
  rcases
    visitFieldSliceResult_object_fst schema resolvers variableValues
      selectionDepth source later fields with
    ⟨laterFields, hlaterFields⟩
  have hmiddleLookupsAfterLater :
      ∀ field, field ∈ middle ->
        responseObjectField? field.responseName (.object laterFields) =
          responseObjectField? field.responseName (.object fields) := by
    intro field hfield
    have hne : field.responseName ≠ later.responseName := by
      intro heq
      exact hnotMiddle (List.mem_map.mpr ⟨field, hfield, heq⟩)
    rw [← hlaterFields]
    exact
      responseObjectField?_visitFieldSliceResult_object_fst_other schema
        resolvers variableValues selectionDepth source later
        field.responseName fields hne
  rw [visitFieldSliceFoldResult_append schema resolvers variableValues
    selectionDepth source middle [later] (.object fields)]
  simp only
  rw [hmiddleFields]
  simp only [visitFieldSliceFoldResult]
  rw [hlaterFields]
  by_cases htarget : target = later.responseName
  · subst target
    have hleft :
        responseObjectField? later.responseName
            (visitFieldSliceResult schema resolvers variableValues
              selectionDepth source later (.object middleFields)).fst =
          responseObjectField? later.responseName (.object laterFields) := by
      have hstep :=
        responseObjectField?_visitFieldSliceResult_object_fst_eq_of_lookup_eq
          schema resolvers variableValues selectionDepth source later
          later.responseName middleFields fields hmiddleLaterLookupObject
          hmiddleLaterLookupObject
      rw [hlaterFields] at hstep
      exact hstep
    have hright :
        responseObjectField? later.responseName
            (visitFieldSliceFoldResult schema resolvers variableValues
              selectionDepth source middle (.object laterFields)).fst =
          responseObjectField? later.responseName (.object laterFields) :=
      responseObjectField?_visitFieldSliceFoldResult_object_fst_of_not_mem
        schema resolvers variableValues selectionDepth source
        later.responseName middle laterFields hnotMiddle
    rw [hleft, hright]
  · have hleft :
        responseObjectField? target
            (visitFieldSliceResult schema resolvers variableValues
              selectionDepth source later (.object middleFields)).fst =
          responseObjectField? target (.object middleFields) :=
      responseObjectField?_visitFieldSliceResult_object_fst_other schema
        resolvers variableValues selectionDepth source later target
        middleFields htarget
    have htargetAfterLater :
        responseObjectField? target (.object laterFields) =
          responseObjectField? target (.object fields) := by
      rw [← hlaterFields]
      exact
        responseObjectField?_visitFieldSliceResult_object_fst_other schema
          resolvers variableValues selectionDepth source later target fields
          htarget
    have hright :
        responseObjectField? target
            (visitFieldSliceFoldResult schema resolvers variableValues
              selectionDepth source middle (.object laterFields)).fst =
          responseObjectField? target
            (visitFieldSliceFoldResult schema resolvers variableValues
              selectionDepth source middle (.object fields)).fst :=
      responseObjectField?_visitFieldSliceFoldResult_object_fst_eq_of_object_lookups
        schema resolvers variableValues selectionDepth source target middle
        laterFields fields htargetAfterLater hmiddleLookupsAfterLater
    rw [hleft, hright]
    simp [hmiddleFields]

theorem visitFieldSliceFoldResult_snd_middle_existing_last_swap_cons
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (middle : List ExecutableField) (later : ExecutableField)
    (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    : (visitFieldSliceFoldResult schema resolvers variableValues selectionDepth
        source ((middle ++ [later]) ++ rest) (.object fields)).snd
      = (visitFieldSliceFoldResult schema resolvers variableValues selectionDepth
          source ((later :: middle) ++ rest) (.object fields)).snd := by
  have hprefixStatus :
      (visitFieldSliceFoldResult schema resolvers variableValues
        selectionDepth source (middle ++ [later]) (.object fields)).snd =
      (visitFieldSliceFoldResult schema resolvers variableValues
        selectionDepth source (later :: middle) (.object fields)).snd :=
    visitFieldSliceFoldResult_snd_middle_existing_last_swap schema resolvers
      variableValues selectionDepth source middle later fields hnotMiddle
  rcases
    visitFieldSliceFoldResult_object_fst schema resolvers variableValues
      selectionDepth source (middle ++ [later]) fields with
    ⟨leftPrefixFields, hleftPrefix⟩
  rcases
    visitFieldSliceFoldResult_object_fst schema resolvers variableValues
      selectionDepth source (later :: middle) fields with
    ⟨rightPrefixFields, hrightPrefix⟩
  have hrestLookups :
      ∀ field, field ∈ rest ->
        responseObjectField? field.responseName (.object leftPrefixFields) =
          responseObjectField? field.responseName (.object rightPrefixFields) := by
    intro field _hfield
    have hlookup :=
      responseObjectField?_visitFieldSliceFoldResult_middle_existing_last_swap
        schema resolvers variableValues selectionDepth source middle later
        fields field.responseName hnotMiddle
    rw [hleftPrefix, hrightPrefix] at hlookup
    exact hlookup
  have hrestStatus :
      (visitFieldSliceFoldResult schema resolvers variableValues
        selectionDepth source rest (.object leftPrefixFields)).snd =
      (visitFieldSliceFoldResult schema resolvers variableValues
        selectionDepth source rest (.object rightPrefixFields)).snd :=
    visitFieldSliceFoldResult_snd_eq_of_object_lookups schema resolvers
      variableValues selectionDepth source rest leftPrefixFields
      rightPrefixFields hrestLookups
  rw [visitFieldSliceFoldResult_append schema resolvers variableValues
    selectionDepth source (middle ++ [later]) rest (.object fields)]
  rw [visitFieldSliceFoldResult_append schema resolvers variableValues
    selectionDepth source (later :: middle) rest (.object fields)]
  simp only
  rw [hleftPrefix, hrightPrefix, hprefixStatus, hrestStatus]

theorem visitFieldSliceResult_eq_visitSelection_executableFieldSelection
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (output : ResponseValue)
    : field.parentType = parentType
      -> visitFieldSliceResult schema resolvers variableValues selectionDepth
            source field output
          = visitSelection schema resolvers variableValues selectionDepth parentType
              source (executableFieldSelection field) output := by
  intro hparent
  rcases field with ⟨fieldParent, responseName, fieldName, arguments, selectionSet⟩
  subst parentType
  cases selectionDepth with
  | zero =>
      simp [visitFieldSliceResult, visitSelection, executableFieldSelection,
        selectionDirectivesAllowBool_empty, outOfFuel]
      rfl
  | succ completionDepth =>
      simp [visitFieldSliceResult, visitSelection, executableFieldSelection,
        executableField, mergeResponseFieldResult, resultValueOrNull,
        resultStatus, selectionDirectivesAllowBool_empty]

theorem visitFieldSlice_eq_visitSelection_executableFieldSelection
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (output : ResponseValue)
    : field.parentType = parentType
      -> visitFieldSlice schema resolvers variableValues selectionDepth source
            field output
          = (visitSelection schema resolvers variableValues selectionDepth parentType
              source (executableFieldSelection field) output).fst := by
  intro hparent
  rcases field with ⟨fieldParent, responseName, fieldName, arguments, selectionSet⟩
  subst parentType
  cases selectionDepth with
  | zero =>
      simp [visitFieldSlice, visitSelection, executableFieldSelection,
        selectionDirectivesAllowBool_empty]
      rfl
  | succ completionDepth =>
      simp [visitFieldSlice, visitSelection, executableFieldSelection,
        executableField, mergeResponseFieldResult, resultValueOrNull, resultStatus,
        selectionDirectivesAllowBool_empty]
      rfl

theorem visitFieldSliceFold_eq_visitSubfields_executableFieldSelections
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    : ∀ (fields : List ExecutableField) (output : ResponseValue),
        (∀ field, field ∈ fields -> field.parentType = parentType)
        -> visitFieldSliceFold schema resolvers variableValues selectionDepth
              source fields output
            = (visitSubfields schema resolvers variableValues selectionDepth parentType
                source (executableFieldSelections fields) output).fst
  | [], output, _hparents => by
      simp [visitFieldSliceFold, executableFieldSelections, visitSubfields]
  | field :: rest, output, hparents => by
      have hfield : field.parentType = parentType :=
        hparents field (by simp)
      have hrest :
          ∀ candidate, candidate ∈ rest ->
            candidate.parentType = parentType := by
        intro candidate hcandidate
        exact hparents candidate (by simp [hcandidate])
      have hstep :
          visitFieldSlice schema resolvers variableValues selectionDepth source
            field output =
          (visitSelection schema resolvers variableValues selectionDepth
            parentType source (executableFieldSelection field) output).fst :=
        visitFieldSlice_eq_visitSelection_executableFieldSelection schema
          resolvers variableValues selectionDepth parentType source field output
          hfield
      simp only [visitFieldSliceFold, executableFieldSelections, List.map_cons,
        List.foldl_cons, visitSubfields]
      rw [hstep]
      simpa [visitFieldSliceFold, executableFieldSelections]
        using
          visitFieldSliceFold_eq_visitSubfields_executableFieldSelections
            schema resolvers variableValues selectionDepth parentType source
            rest
            (visitSelection schema resolvers variableValues selectionDepth
              parentType source (executableFieldSelection field) output).fst
            hrest

theorem visitFieldSliceFoldResult_eq_visitSubfields_executableFieldSelections
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (selectionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    : ∀ (fields : List ExecutableField) (output : ResponseValue),
        (∀ field, field ∈ fields -> field.parentType = parentType)
        -> visitFieldSliceFoldResult schema resolvers variableValues selectionDepth
              source fields output
            = visitSubfields schema resolvers variableValues selectionDepth parentType
                source (executableFieldSelections fields) output
  | [], output, _hparents => by
      simp [visitFieldSliceFoldResult, executableFieldSelections, visitSubfields,
        visitOk]
  | field :: rest, output, hparents => by
      have hfield : field.parentType = parentType :=
        hparents field (by simp)
      have hrest :
          ∀ candidate, candidate ∈ rest ->
            candidate.parentType = parentType := by
        intro candidate hcandidate
        exact hparents candidate (by simp [hcandidate])
      have hstep :
          visitFieldSliceResult schema resolvers variableValues selectionDepth
            source field output =
          visitSelection schema resolvers variableValues selectionDepth
            parentType source (executableFieldSelection field) output :=
        visitFieldSliceResult_eq_visitSelection_executableFieldSelection schema
          resolvers variableValues selectionDepth parentType source field output
          hfield
      simp only [visitFieldSliceFoldResult, executableFieldSelections,
        List.map_cons, visitSubfields]
      rw [hstep]
      have hrec :=
        visitFieldSliceFoldResult_eq_visitSubfields_executableFieldSelections
          schema resolvers variableValues selectionDepth parentType source
          rest
          (visitSelection schema resolvers variableValues selectionDepth
            parentType source (executableFieldSelection field) output).fst
          hrest
      rw [hrec]
      simp [executableFieldSelections]

def responseFieldSlice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    : ResponseValue :=
  resultValueOrNull
    (executeField schema resolvers variableValues completionDepth source none field)

def responseObjectSlice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    : ResponseValue :=
  .object
    [(
      field.responseName,
      responseFieldSlice schema resolvers variableValues completionDepth source field
    )]

theorem ResponseMergeReady_responseFieldSlice
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    : ResponseMergeReady
        (responseFieldSlice schema resolvers variableValues completionDepth source
          field) := by
  simpa [responseFieldSlice] using
    executeField_response_ready_of_previous schema resolvers variableValues
      completionDepth source none field
      (by intro previous h; cases h)

def responseObjectSlices
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    : List (Name × ResponseValue) :=
  fields.map
    (fun field =>
      (
        field.responseName,
        responseFieldSlice schema resolvers variableValues completionDepth source field
      ))

theorem responseObjectSlices_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) (responseName : Name)
    : responseName
        ∈ (responseObjectSlices schema resolvers variableValues completionDepth
            source fields).map
            Prod.fst
      ↔ responseName ∈ fields.map (fun field => field.responseName) := by
  simp [responseObjectSlices]

theorem responseObjectSlices_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    : (fields.map (fun field => field.responseName)).Nodup
      -> PairKeysNodup
          (responseObjectSlices schema resolvers variableValues completionDepth
            source fields) := by
  intro hnodup
  unfold PairKeysNodup
  simpa [responseObjectSlices, Function.comp_def] using hnodup

def mergeResponseSliceFold
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) (output : ResponseValue)
    : ResponseValue :=
  fields.foldl
    (fun output field =>
      mergeResponse output
        (responseObjectSlice schema resolvers variableValues completionDepth
          source field))
    output

def VisitSubfieldsPopulates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (previous : ResponseValue)
    : Prop :=
  (visitSubfields schema resolvers variableValues depth parentType source
    selectionSet previous).fst
  = mergeResponse previous
      (visitSubfields schema resolvers variableValues depth parentType source
        selectionSet (.object [])).fst

namespace VisitSubfieldsPopulates

theorem nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    (previous : ResponseValue)
    : VisitSubfieldsPopulates schema resolvers variableValues depth parentType
        source [] previous := by
  simp [VisitSubfieldsPopulates, visitSubfields,
    mergeResponse_empty_object_right]

end VisitSubfieldsPopulates

def FieldSliceMergeFoldPopulates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) (previous : ResponseValue)
    : Prop :=
  mergeResponseSliceFold schema resolvers variableValues completionDepth source
    fields previous
  = mergeResponse previous
      (mergeResponseSliceFold schema resolvers variableValues completionDepth
        source fields (.object []))

namespace FieldSliceMergeFoldPopulates

theorem mergeResponseSliceFold_object_append_of_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    : ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
        (fields.map (fun field => field.responseName)).Nodup
        -> (∀ field, field ∈ fields -> field.responseName ∉ outputFields.map Prod.fst)
        -> mergeResponseSliceFold schema resolvers variableValues completionDepth
              source fields (.object outputFields)
            = .object
                (outputFields
                  ++ responseObjectSlices schema resolvers variableValues
                      completionDepth source fields)
  | [], outputFields, _hnodup, _hdisjoint => by
      simp [mergeResponseSliceFold, responseObjectSlices]
  | field :: rest, outputFields, hnodup, hdisjoint => by
      let incoming :=
        responseFieldSlice schema resolvers variableValues completionDepth source
          field
      have hfresh : field.responseName ∉ outputFields.map Prod.fst :=
        hdisjoint field (by simp)
      have hparts :
          field.responseName ∉ rest.map (fun field => field.responseName) ∧
          (rest.map (fun field => field.responseName)).Nodup := by
        simpa using List.nodup_cons.mp hnodup
      have hheadMerge :
          mergeResponse (.object outputFields)
            (responseObjectSlice schema resolvers variableValues completionDepth
              source field) =
          .object (outputFields ++ [(field.responseName, incoming)]) := by
        simpa [responseObjectSlice, incoming] using
          mergeResponse_object_append_of_disjoint outputFields
            [(field.responseName, incoming)]
            (by simp [PairKeysNodup])
            (by
              intro responseName hmem
              simp only [List.map_cons, List.map_nil, List.mem_singleton] at hmem
              subst responseName
              exact hfresh)
      have hrestDisjoint :
          ∀ candidate, candidate ∈ rest ->
            candidate.responseName ∉
              (outputFields ++ [(field.responseName, incoming)]).map
                Prod.fst := by
        intro candidate hcandidate
        simp only [List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_singleton]
        intro hmem
        rcases hmem with houtput | hhead
        · exact hdisjoint candidate (by simp [hcandidate]) houtput
        · have hcandidateNotHead :
              candidate.responseName ≠ field.responseName := by
            intro heq
            exact hparts.1
              (List.mem_map.mpr ⟨candidate, hcandidate, heq⟩)
          exact hcandidateNotHead hhead
      have hrestFold :=
        mergeResponseSliceFold_object_append_of_responseNamesNodup schema
          resolvers variableValues completionDepth source rest
          (outputFields ++ [(field.responseName, incoming)]) hparts.2
          hrestDisjoint
      simpa [mergeResponseSliceFold, hheadMerge, responseObjectSlices,
        incoming, List.append_assoc] using hrestFold

theorem of_responseNamesNodup_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) (outputFields : List (Name × ResponseValue))
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hdisjoint
      : ∀ field, field ∈ fields -> field.responseName ∉ outputFields.map Prod.fst)
    : FieldSliceMergeFoldPopulates schema resolvers variableValues
        completionDepth source fields (.object outputFields) := by
  have hleft :
      mergeResponseSliceFold schema resolvers variableValues completionDepth
        source fields (.object outputFields) =
      .object
        (outputFields ++
          responseObjectSlices schema resolvers variableValues completionDepth
            source fields) :=
    mergeResponseSliceFold_object_append_of_responseNamesNodup schema resolvers
      variableValues completionDepth source fields outputFields hnodup
      hdisjoint
  have hempty :
      mergeResponseSliceFold schema resolvers variableValues completionDepth
        source fields (.object []) =
      .object
        (responseObjectSlices schema resolvers variableValues completionDepth
          source fields) := by
    simpa using
      mergeResponseSliceFold_object_append_of_responseNamesNodup schema
        resolvers variableValues completionDepth source fields [] hnodup
        (by intro field _hmem; simp)
  have hslicesNodup :
      PairKeysNodup
        (responseObjectSlices schema resolvers variableValues completionDepth
          source fields) :=
    responseObjectSlices_pairKeysNodup schema resolvers variableValues
      completionDepth source fields hnodup
  have hslicesDisjoint :
      ∀ responseName,
        responseName ∈
          (responseObjectSlices schema resolvers variableValues
            completionDepth source fields).map Prod.fst ->
        responseName ∉ outputFields.map Prod.fst := by
    intro responseName hmem
    rw [responseObjectSlices_key_mem schema resolvers variableValues
      completionDepth source fields responseName] at hmem
    rcases List.mem_map.mp hmem with ⟨field, hfield, hresponse⟩
    rw [← hresponse]
    exact hdisjoint field hfield
  unfold FieldSliceMergeFoldPopulates
  rw [hleft, hempty]
  rw [mergeResponse_object_append_of_disjoint outputFields
    (responseObjectSlices schema resolvers variableValues completionDepth
      source fields)
    hslicesNodup hslicesDisjoint]

theorem nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (previous : ResponseValue)
    : FieldSliceMergeFoldPopulates schema resolvers variableValues
        completionDepth source [] previous := by
  simp [FieldSliceMergeFoldPopulates, mergeResponseSliceFold,
    mergeResponse_empty_object_right]

theorem singleton
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (previous : ResponseValue)
    : FieldSliceMergeFoldPopulates schema resolvers variableValues
        completionDepth source [field] previous := by
  simp [FieldSliceMergeFoldPopulates, mergeResponseSliceFold,
    responseObjectSlice, mergeResponse, mergeResponseFields,
    mergeResponseField]

theorem cons_of_tail_merge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (rest : List ExecutableField)
    (previous : ResponseValue)
    (hmerge
      : mergeResponseSliceFold schema resolvers variableValues completionDepth
          source rest
          (mergeResponse previous
            (responseObjectSlice schema resolvers variableValues completionDepth
              source field))
        = mergeResponse previous
            (mergeResponseSliceFold schema resolvers variableValues completionDepth
              source rest
              (mergeResponse (.object [])
                (responseObjectSlice schema resolvers variableValues
                  completionDepth source field))))
    : FieldSliceMergeFoldPopulates schema resolvers variableValues
        completionDepth source (field :: rest) previous := by
  simpa [FieldSliceMergeFoldPopulates, mergeResponseSliceFold] using hmerge

end FieldSliceMergeFoldPopulates

def CompleteValuePopulates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (selectionSet : List Selection) (value : ResolverValue ObjectIdentity)
    (previous : ResponseValue)
    : Prop :=
  resultValueOrNull
    (completeResolvedValue schema resolvers variableValues completionDepth parentType
      selectionSet value (some previous))
  = mergeResponse previous
      (resultValueOrNull
        (completeResolvedValue schema resolvers variableValues completionDepth
          parentType selectionSet value none))

theorem resultValueOrNull_nonNullCompletion_eq_null
    (completed : Result ResponseValue)
    (hnull : resultValueOrNull completed = .null)
    : resultValueOrNull (nonNullCompletion completed) = .null := by
  cases completed with
  | error errors =>
      rfl
  | ok completed =>
      rcases completed with ⟨value, errors⟩
      cases value <;> simp [resultValueOrNull] at hnull
      cases errors <;> simp [nonNullCompletion, resultValueOrNull]

theorem resultValueOrNull_nonNullCompletion_eq_scalar
    (completed : Result ResponseValue) (value : String)
    (hscalar : resultValueOrNull completed = .scalar value)
    : resultValueOrNull (nonNullCompletion completed) = .scalar value := by
  cases completed with
  | error errors =>
      simp [resultValueOrNull] at hscalar
  | ok completed =>
      rcases completed with ⟨response, errors⟩
      cases response <;> simp [resultValueOrNull] at hscalar
      simpa [nonNullCompletion, resultValueOrNull] using hscalar

theorem completeValue_null_resultValueOrNull
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    : ∀ (fieldType : TypeRef) (completionDepth : Nat)
          (selectionSet : List Selection) (previous? : Option ResponseValue),
        resultValueOrNull
          (completeValue schema resolvers variableValues completionDepth
            fieldType selectionSet (.null : ResolverValue ObjectIdentity)
            previous?)
        = .null
  | .named _typeName, completionDepth, selectionSet, previous? => by
      cases previous? with
      | none =>
          cases completionDepth <;>
            simp [completeValue, outOfFuel, resultValueOrNull]
      | some previous =>
          cases previous <;> cases completionDepth <;>
            simp [completeValue, outOfFuel, resultValueOrNull]
  | .list _inner, completionDepth, selectionSet, previous? => by
      cases previous? with
      | none =>
          cases completionDepth <;>
            simp [completeValue, outOfFuel, resultValueOrNull]
      | some previous =>
          cases previous <;> cases completionDepth <;>
            simp [completeValue, outOfFuel, resultValueOrNull]
  | .nonNull inner, completionDepth, selectionSet, previous? => by
      cases previous? with
      | none =>
          cases completionDepth with
          | zero =>
              simp [completeValue, outOfFuel, resultValueOrNull]
          | succ depth =>
              simpa [completeValue, nonNullCompletion] using
                resultValueOrNull_nonNullCompletion_eq_null
                (completeValue schema resolvers variableValues (depth + 1)
                  inner selectionSet (.null : ResolverValue ObjectIdentity)
                  none)
                (completeValue_null_resultValueOrNull schema resolvers
                  variableValues inner (depth + 1) selectionSet none)
      | some previous =>
        cases previous with
        | null =>
          cases completionDepth with
          | zero =>
              simp [completeValue, resultValueOrNull, outOfFuel]
          | succ depth =>
              simp [completeValue, resultValueOrNull]
        | scalar previousValue =>
          cases completionDepth with
          | zero =>
              simp [completeValue, resultValueOrNull, outOfFuel]
          | succ depth =>
              simp [completeValue, resultValueOrNull]
        | object previousFields =>
          cases completionDepth with
          | zero =>
              simp [completeValue, outOfFuel, resultValueOrNull]
          | succ depth =>
              simpa [completeValue] using
                resultValueOrNull_nonNullCompletion_eq_null
                (completeValue schema resolvers variableValues (depth + 1)
                  inner selectionSet (.null : ResolverValue ObjectIdentity)
                  (some (.object previousFields)))
                (completeValue_null_resultValueOrNull schema resolvers
                  variableValues inner (depth + 1) selectionSet
                  (some (.object previousFields)))
        | list previousValues =>
          cases completionDepth with
          | zero =>
              simp [completeValue, outOfFuel, resultValueOrNull]
          | succ depth =>
              simpa [completeValue] using
                resultValueOrNull_nonNullCompletion_eq_null
                (completeValue schema resolvers variableValues (depth + 1)
                  inner selectionSet (.null : ResolverValue ObjectIdentity)
                  (some (.list previousValues)))
                (completeValue_null_resultValueOrNull schema resolvers
                  variableValues inner (depth + 1) selectionSet
                  (some (.list previousValues)))

theorem completeValue_scalar_object_empty_resultValueOrNull
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    : ∀ (fieldType : TypeRef) (completionDepth : Nat)
          (selectionSet : List Selection) (value : String),
        resultValueOrNull
            (completeValue schema resolvers variableValues completionDepth
              fieldType selectionSet (.scalar value : ResolverValue ObjectIdentity)
              none)
          = .null
        ∨ resultValueOrNull
            (completeValue schema resolvers variableValues completionDepth
              fieldType selectionSet (.scalar value : ResolverValue ObjectIdentity)
              none)
          = scalarCompletionAtDepth schema fieldType.namedType completionDepth value
  | .named _typeName, completionDepth, selectionSet, value => by
      right
      cases completionDepth with
      | zero =>
          simp [completeValue, outOfFuel, resultValueOrNull,
            scalarCompletionAtDepth]
      | succ depth =>
          cases hcomposite :
              (TypeRef.named _typeName).isCompositeBool schema <;>
            simp [completeValue, resultValueOrNull, scalarCompletionAtDepth,
              TypeRef.namedType, hcomposite]
  | .list _inner, completionDepth, selectionSet, value => by
      cases completionDepth with
      | zero =>
          right
          simp [completeValue, outOfFuel, resultValueOrNull,
            scalarCompletionAtDepth]
      | succ depth =>
          left
          simp [completeValue, resultValueOrNull]
  | .nonNull inner, completionDepth, selectionSet, value => by
      cases completionDepth with
      | zero =>
          right
          simp [completeValue, outOfFuel, resultValueOrNull,
            scalarCompletionAtDepth]
      | succ depth =>
          have hinner :=
            completeValue_scalar_object_empty_resultValueOrNull schema
              resolvers variableValues inner (depth + 1) selectionSet value
          rcases hinner with hnull | hscalar
          · left
            simpa [completeValue] using
              resultValueOrNull_nonNullCompletion_eq_null
                (completeValue schema resolvers variableValues (depth + 1)
                  inner selectionSet
                  (.scalar value : ResolverValue ObjectIdentity) none)
                hnull
          · cases hcomposite :
                (TypeRef.named inner.namedType).isCompositeBool schema with
            | true =>
              left
              have hinnerNull :
                  resultValueOrNull
                    (completeValue schema resolvers variableValues (depth + 1)
                      inner selectionSet
                      (.scalar value : ResolverValue ObjectIdentity) none) =
                  .null := by
                simpa [scalarCompletionAtDepth, hcomposite] using hscalar
              simpa [completeValue] using
                resultValueOrNull_nonNullCompletion_eq_null
                  (completeValue schema resolvers variableValues (depth + 1)
                    inner selectionSet
                    (.scalar value : ResolverValue ObjectIdentity) none)
                  hinnerNull
            | false =>
              right
              have hinnerScalar :
                  resultValueOrNull
                    (completeValue schema resolvers variableValues (depth + 1)
                      inner selectionSet
                      (.scalar value : ResolverValue ObjectIdentity) none) =
                  .scalar value := by
                simpa [scalarCompletionAtDepth, hcomposite] using hscalar
              simpa [completeValue, scalarCompletionAtDepth, TypeRef.namedType,
                hcomposite] using
                resultValueOrNull_nonNullCompletion_eq_scalar
                  (completeValue schema resolvers variableValues (depth + 1)
                    inner selectionSet
                    (.scalar value : ResolverValue ObjectIdentity) none)
                  value hinnerScalar

theorem responseFieldSlice_eq_null_of_resolve_null
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : ResolverValue ObjectIdentity}
    {field : ExecutableField}
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = some .null)
    : responseFieldSlice schema resolvers variableValues completionDepth source field
      = .null := by
  unfold responseFieldSlice
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      simp [executeField, hlookup, resultValueOrNull]
  | some fieldDefinition =>
      have hreuse :
          reusablePreviousValue? schema fieldDefinition.outputType none =
        none :=
        reusablePreviousValue?_none schema fieldDefinition.outputType
      simp [executeField, hlookup, hresolve, hreuse,
        completeValue_null_resultValueOrNull]

theorem responseFieldSlice_eq_null_or_scalar_of_resolve_scalar
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : ResolverValue ObjectIdentity}
    {field : ExecutableField} {value : String}
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = some (.scalar value))
    : responseFieldSlice schema resolvers variableValues completionDepth source field
        = .null
      ∨ responseFieldSlice schema resolvers variableValues completionDepth source field
        = scalarCompletionAtDepth schema
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            completionDepth value := by
  unfold responseFieldSlice
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      left
      simp [executeField, hlookup, resultValueOrNull]
  | some fieldDefinition =>
      have hreuse :
          reusablePreviousValue? schema fieldDefinition.outputType none =
        none :=
        reusablePreviousValue?_none schema fieldDefinition.outputType
      have hreturn :
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName) =
          fieldDefinition.outputType.namedType := by
        simp [Schema.fieldReturnType?, hlookup]
      simpa [executeField, hlookup, hresolve, hreuse, hreturn] using
        completeValue_scalar_object_empty_resultValueOrNull schema resolvers
          variableValues fieldDefinition.outputType completionDepth
          field.selectionSet value

namespace CompleteValuePopulates

theorem null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (selectionSet : List Selection)
    : CompleteValuePopulates schema resolvers variableValues completionDepth
        parentType selectionSet (.null : ResolverValue ObjectIdentity) .null := by
  simp [CompleteValuePopulates, completeResolvedValue,
    reusablePreviousValue?_null, reusablePreviousValue?_none,
    resultValueOrNull, mergeResponse]

theorem null_responseFieldSlice
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : ResolverValue ObjectIdentity}
    {first later : ExecutableField}
    (hfirstResolve
      : resolvers.resolve first.parentType first.fieldName first.arguments source
        = some .null)
    (hlaterResolve
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = some .null)
    : CompleteValuePopulates schema resolvers variableValues completionDepth
        ((schema.fieldReturnType? later.parentType later.fieldName).getD later.fieldName)
        later.selectionSet
        (resolvers.resolve later.parentType later.fieldName later.arguments source)
        (responseFieldSlice schema resolvers variableValues completionDepth source
          first) := by
  rw [hlaterResolve]
  rw [responseFieldSlice_eq_null_of_resolve_null (schema := schema)
    (resolvers := resolvers) (variableValues := variableValues)
    (completionDepth := completionDepth) (source := source)
    (field := first) hfirstResolve]
  simpa using
    CompleteValuePopulates.null schema resolvers variableValues completionDepth
      ((schema.fieldReturnType? later.parentType later.fieldName).getD
        later.fieldName)
      later.selectionSet

theorem scalar_self
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (selectionSet : List Selection) (value : String)
    : CompleteValuePopulates schema resolvers variableValues completionDepth
        parentType selectionSet (.scalar value : ResolverValue ObjectIdentity)
        (scalarCompletionAtDepth schema parentType completionDepth value) := by
  cases completionDepth with
  | zero =>
      simp [CompleteValuePopulates, completeResolvedValue,
        reusablePreviousValue?_null, reusablePreviousValue?_none,
        completeValue, resultValueOrNull, scalarCompletionAtDepth,
        mergeResponse]
  | succ depth =>
      cases hcomposite :
          (TypeRef.named parentType).isCompositeBool schema with
      | true =>
        simp [CompleteValuePopulates, completeResolvedValue,
          reusablePreviousValue?_null, reusablePreviousValue?_none,
          completeValue, resultValueOrNull, scalarCompletionAtDepth,
          mergeResponse, hcomposite]
      | false =>
        simp [CompleteValuePopulates, completeResolvedValue,
          reusablePreviousValue?_scalar, reusablePreviousValue?_none,
          completeValue, resultValueOrNull, scalarCompletionAtDepth,
          mergeResponse, hcomposite]

theorem scalar_responseFieldSlice
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : ResolverValue ObjectIdentity}
    {first later : ExecutableField} {value : String}
    (hfirstResolve
      : resolvers.resolve first.parentType first.fieldName first.arguments source
        = some (.scalar value))
    (hlaterResolve
      : resolvers.resolve later.parentType later.fieldName later.arguments source
        = some (.scalar value))
    (hcompletion
      : scalarCompletionAtDepth schema
          ((schema.fieldReturnType? first.parentType first.fieldName).getD
            first.fieldName)
          completionDepth value
        = scalarCompletionAtDepth schema
            ((schema.fieldReturnType? later.parentType later.fieldName).getD
              later.fieldName)
            completionDepth value)
    : CompleteValuePopulates schema resolvers variableValues completionDepth
        ((schema.fieldReturnType? later.parentType later.fieldName).getD later.fieldName)
        later.selectionSet
        (resolvers.resolve later.parentType later.fieldName later.arguments source)
        (responseFieldSlice schema resolvers variableValues completionDepth source
          first) := by
  rw [hlaterResolve]
  rcases responseFieldSlice_eq_null_or_scalar_of_resolve_scalar
      (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues)
      (completionDepth := completionDepth) (source := source)
      (field := first) hfirstResolve with hslice | hslice
  · rw [hslice]
    simp [CompleteValuePopulates, completeResolvedValue,
      reusablePreviousValue?_null, reusablePreviousValue?_none,
      resultValueOrNull, mergeResponse]
  · rw [hslice]
    rw [hcompletion]
    simpa using
      CompleteValuePopulates.scalar_self schema resolvers variableValues
        completionDepth
        ((schema.fieldReturnType? later.parentType later.fieldName).getD
          later.fieldName)
        later.selectionSet value

end CompleteValuePopulates

theorem mergeResponseField_null_of_lookup_null_slice (responseName : Name)
    : ∀ (fields : List (Name × ResponseValue)),
        lookupResponseField? responseName fields = some .null
        -> mergeResponseField responseName .null fields = fields
  | [], hlookup => by
      simp [lookupResponseField?] at hlookup
  | (fieldResponseName, fieldResponse) :: rest, hlookup => by
      by_cases hname : fieldResponseName == responseName
      · simp [lookupResponseField?, hname] at hlookup
        simp [mergeResponseField, mergeResponse, hname, hlookup]
      · simp [lookupResponseField?, hname] at hlookup
        simp [mergeResponseField, hname,
          mergeResponseField_null_of_lookup_null_slice responseName rest
            hlookup]

theorem mergeResponseField_eq_of_lookup_absorbs
    (responseName : Name) (existing incomingSlice incomingFull : ResponseValue)
    (fields : List (Name × ResponseValue))
    : lookupResponseField? responseName fields = some existing
      -> ResponseAbsorbs existing incomingFull
      -> incomingFull = mergeResponse existing incomingSlice
      -> mergeResponseField responseName incomingFull fields
          = mergeResponseField responseName incomingSlice fields := by
  intro hlookup habsorbs hincomingFull
  induction fields with
  | nil =>
      simp [lookupResponseField?] at hlookup
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, fieldResponse⟩
      by_cases hname : fieldResponseName == responseName
      · have hfield : fieldResponseName = responseName := beq_iff_eq.mp hname
        simp [lookupResponseField?, hname] at hlookup
        subst existing
        have hincomingAbsorbed :
            mergeResponse fieldResponse incomingFull = incomingFull := by
          simpa [ResponseAbsorbs] using habsorbs
        simp [mergeResponseField, hname]
        exact hincomingAbsorbed.trans hincomingFull
      · simp [lookupResponseField?, hname] at hlookup
        simp [mergeResponseField, hname, ih hlookup]

theorem visitFieldSlice_succ_object_eq_mergeResponseSlice_of_step
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (fields : List (Name × ResponseValue))
    (hstep
      : resultValueOrNull
          (executeField schema resolvers variableValues completionDepth source
            (responseObjectField? field.responseName (.object fields)) field)
        = match responseObjectField? field.responseName (.object fields) with
          | some existing =>
              mergeResponse existing
                (responseFieldSlice schema resolvers variableValues
                  completionDepth source field)
          | none =>
              responseFieldSlice schema resolvers variableValues completionDepth
                source field)
    (habsorbs
      : ∀ existing,
          responseObjectField? field.responseName (.object fields) = some existing
          -> ResponseAbsorbs existing
              (resultValueOrNull
                (executeField schema resolvers variableValues completionDepth source
                  (responseObjectField? field.responseName (.object fields))
                  field)))
    : visitFieldSlice schema resolvers variableValues (completionDepth + 1)
        source field (.object fields)
      = mergeResponse (.object fields)
          (responseObjectSlice schema resolvers variableValues completionDepth
            source field) := by
  cases hlookup :
      responseObjectField? field.responseName (.object fields) with
  | none =>
      have hstep' :
          resultValueOrNull
            (executeField schema resolvers variableValues completionDepth source
              none field) =
          responseFieldSlice schema resolvers variableValues completionDepth
            source field := by
        simpa [hlookup] using hstep
      simpa [visitFieldSlice, visitFieldSliceResult, responseObjectSlice,
        mergeResponse, mergeResponseFields, mergeResponseFieldResult,
        mergeResponseFieldIntoObject, hlookup] using
          congrArg
            (fun incoming =>
              ResponseValue.object
                (mergeResponseField field.responseName incoming fields))
            hstep'
  | some existing =>
      have hstep' :
          resultValueOrNull
            (executeField schema resolvers variableValues completionDepth source
              (some existing) field) =
          mergeResponse existing
            (responseFieldSlice schema resolvers variableValues
              completionDepth source field) := by
        simpa [hlookup] using hstep
      have habsorbs' :
          ResponseAbsorbs existing
            (resultValueOrNull
              (executeField schema resolvers variableValues completionDepth
                source (some existing) field)) := by
        simpa [hlookup] using habsorbs existing hlookup
      have hlookupField :
          lookupResponseField? field.responseName fields = some existing := by
        simpa [responseObjectField?] using hlookup
      have hmergeEq :
          mergeResponseField field.responseName
              (resultValueOrNull
              (executeField schema resolvers variableValues completionDepth
                  source (some existing) field))
              fields =
            mergeResponseField field.responseName
              (responseFieldSlice schema resolvers variableValues
                completionDepth source field)
              fields :=
        mergeResponseField_eq_of_lookup_absorbs field.responseName existing
          (responseFieldSlice schema resolvers variableValues completionDepth
            source field)
            (resultValueOrNull
              (executeField schema resolvers variableValues completionDepth source
                (some existing) field))
            fields hlookupField habsorbs' hstep'
      cases existing with
      | null =>
          simpa [visitFieldSlice, visitFieldSliceResult, responseObjectSlice,
            mergeResponse, mergeResponseFields, mergeResponseFieldResult,
            mergeResponseFieldIntoObject, hlookup] using
              congrArg ResponseValue.object hmergeEq
      | scalar value =>
          simpa [visitFieldSlice, visitFieldSliceResult, responseObjectSlice,
            mergeResponse, mergeResponseFields, mergeResponseFieldResult,
            mergeResponseFieldIntoObject, hlookup] using
              congrArg ResponseValue.object hmergeEq
      | object objectFields =>
          simpa [visitFieldSlice, visitFieldSliceResult, responseObjectSlice,
            mergeResponse, mergeResponseFields, mergeResponseFieldResult,
            mergeResponseFieldIntoObject, hlookup] using
              congrArg ResponseValue.object hmergeEq
      | list values =>
          simpa [visitFieldSlice, visitFieldSliceResult, responseObjectSlice,
            mergeResponse, mergeResponseFields, mergeResponseFieldResult,
            mergeResponseFieldIntoObject, hlookup] using
              congrArg ResponseValue.object hmergeEq

structure FieldSliceMergeStep
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (fields : List (Name × ResponseValue))
    : Prop where
  step_eq
    : resultValueOrNull
        (executeField schema resolvers variableValues completionDepth source
          (responseObjectField? field.responseName (.object fields)) field)
      = match responseObjectField? field.responseName (.object fields) with
        | some existing =>
            mergeResponse existing
              (responseFieldSlice schema resolvers variableValues completionDepth
                source field)
        | none =>
            responseFieldSlice schema resolvers variableValues completionDepth
              source field
  absorbs
    : ∀ existing,
        responseObjectField? field.responseName (.object fields) = some existing
        -> ResponseAbsorbs existing
            (resultValueOrNull
              (executeField schema resolvers variableValues completionDepth source
                (responseObjectField? field.responseName (.object fields)) field))

namespace FieldSliceMergeStep

theorem of_fresh
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : ResolverValue ObjectIdentity}
    {field : ExecutableField} {fields : List (Name × ResponseValue)}
    (hfresh : field.responseName ∉ fields.map Prod.fst)
    : FieldSliceMergeStep schema resolvers variableValues completionDepth source
        field fields := by
  have hlookup :
      responseObjectField? field.responseName (.object fields) = none :=
    responseObjectField?_none_of_not_mem field.responseName fields hfresh
  constructor
  · simp [hlookup, responseFieldSlice]
  · intro existing hexisting
    rw [hlookup] at hexisting
    cases hexisting

theorem of_reentry
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {completionDepth : Nat} {source : ResolverValue ObjectIdentity}
    {field : ExecutableField} {fields : List (Name × ResponseValue)}
    {existing : ResponseValue}
    (hlookup : responseObjectField? field.responseName (.object fields) = some existing)
    (hstep
      : resultValueOrNull
          (executeField schema resolvers variableValues completionDepth source
            (some existing) field)
        = mergeResponse existing
            (responseFieldSlice schema resolvers variableValues completionDepth
              source field))
    (habsorbs
      : ResponseAbsorbs existing
          (resultValueOrNull
            (executeField schema resolvers variableValues completionDepth source
              (some existing) field)))
    : FieldSliceMergeStep schema resolvers variableValues completionDepth source
        field fields := by
  constructor
  · rw [hlookup]
    exact hstep
  · intro candidate hcandidate
    rw [hlookup] at hcandidate
    cases hcandidate
    simpa [hlookup] using habsorbs

end FieldSliceMergeStep

def FieldSliceMergeTrace
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    : List ExecutableField -> ResponseValue -> Prop
  | [], _output => True
  | field :: rest, .object fields =>
      FieldSliceMergeStep schema resolvers variableValues completionDepth
        source field fields
      ∧ FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source rest
          (mergeResponse (.object fields)
            (responseObjectSlice schema resolvers variableValues completionDepth
              source field))
  | _field :: _rest, _output => False

namespace FieldSliceMergeTrace

theorem nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (output : ResponseValue)
    : FieldSliceMergeTrace schema resolvers variableValues completionDepth source
        [] output := by
  simp [FieldSliceMergeTrace]

theorem cons_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hstep
      : FieldSliceMergeStep schema resolvers variableValues completionDepth
          source field fields)
    (hrest
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source rest
          (mergeResponse (.object fields)
            (responseObjectSlice schema resolvers variableValues completionDepth
              source field)))
    : FieldSliceMergeTrace schema resolvers variableValues completionDepth source
        (field :: rest) (.object fields) := by
  exact ⟨hstep, hrest⟩

theorem cons_fresh_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hfresh : field.responseName ∉ fields.map Prod.fst)
    (hrest
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source rest
          (mergeResponse (.object fields)
            (responseObjectSlice schema resolvers variableValues completionDepth
              source field)))
    : FieldSliceMergeTrace schema resolvers variableValues completionDepth source
        (field :: rest) (.object fields) :=
  cons_object schema resolvers variableValues completionDepth source field rest
    fields (FieldSliceMergeStep.of_fresh hfresh) hrest

theorem of_responseNamesNodup_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    : ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
        (fields.map (fun field => field.responseName)).Nodup
        -> (∀ field, field ∈ fields -> field.responseName ∉ outputFields.map Prod.fst)
        -> FieldSliceMergeTrace schema resolvers variableValues completionDepth
            source fields (.object outputFields)
  | [], outputFields, _hnodup, _hdisjoint => by
      simp [FieldSliceMergeTrace]
  | field :: rest, outputFields, hnodup, hdisjoint => by
      have hfresh : field.responseName ∉ outputFields.map Prod.fst :=
        hdisjoint field (by simp)
      have hparts :
          field.responseName ∉ rest.map (fun field => field.responseName) ∧
          (rest.map (fun field => field.responseName)).Nodup := by
        simpa using List.nodup_cons.mp hnodup
      let incoming :=
        responseFieldSlice schema resolvers variableValues completionDepth source
          field
      have hmerge :
          mergeResponseFields outputFields [(field.responseName, incoming)] =
          outputFields ++ [(field.responseName, incoming)] := by
        apply mergeResponseFields_append_of_disjoint
        · simp [PairKeysNodup]
        · intro responseName hmem
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hmem
          subst responseName
          exact hfresh
      have hrestDisjoint :
          ∀ candidate, candidate ∈ rest ->
            candidate.responseName ∉
              (mergeResponseFields outputFields
                [(field.responseName, incoming)]).map Prod.fst := by
        intro candidate hcandidate
        rw [hmerge]
        simp only [List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_singleton]
        intro hmem
        rcases hmem with houtput | hfield
        · exact hdisjoint candidate (by simp [hcandidate]) houtput
        · have hcandidateNotHead :
              candidate.responseName ≠ field.responseName := by
            intro heq
            exact hparts.1
              (List.mem_map.mpr ⟨candidate, hcandidate, heq⟩)
          exact hcandidateNotHead hfield
      refine
        FieldSliceMergeTrace.cons_object schema resolvers variableValues
          completionDepth source field rest outputFields
          (FieldSliceMergeStep.of_fresh hfresh) ?_
      simpa [responseObjectSlice, responseFieldSlice, incoming, mergeResponse]
        using
          of_responseNamesNodup_object schema resolvers variableValues
            completionDepth source rest
            (mergeResponseFields outputFields
              [(field.responseName, incoming)])
            hparts.2 hrestDisjoint

theorem of_responseNamesNodup_empty
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    : FieldSliceMergeTrace schema resolvers variableValues completionDepth source
        fields (.object []) :=
  of_responseNamesNodup_object schema resolvers variableValues completionDepth
    source fields [] hnodup (by intro field _hmem; simp)

end FieldSliceMergeTrace

theorem visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    : ∀ (fields : List ExecutableField) (output : ResponseValue),
        FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source fields output
        -> visitFieldSliceFold schema resolvers variableValues
              (completionDepth + 1) source fields output
            = mergeResponseSliceFold schema resolvers variableValues completionDepth
                source fields output
  | [], output, _htrace => by
      simp [visitFieldSliceFold, mergeResponseSliceFold]
  | field :: rest, output, htrace => by
      cases output with
      | null =>
          simp [FieldSliceMergeTrace] at htrace
      | scalar value =>
          simp [FieldSliceMergeTrace] at htrace
      | list values =>
          simp [FieldSliceMergeTrace] at htrace
      | object fields =>
          rcases htrace with ⟨hstep, hrest⟩
          have hone :
              visitFieldSlice schema resolvers variableValues
                (completionDepth + 1) source field (.object fields) =
              mergeResponse (.object fields)
                (responseObjectSlice schema resolvers variableValues
                  completionDepth source field) :=
            visitFieldSlice_succ_object_eq_mergeResponseSlice_of_step schema
              resolvers variableValues completionDepth source field fields
              hstep.step_eq hstep.absorbs
          simp [visitFieldSliceFold, mergeResponseSliceFold, hone]
          exact
            visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema
              resolvers variableValues completionDepth source rest
              (mergeResponse (.object fields)
                (responseObjectSlice schema resolvers variableValues
                  completionDepth source field))
              hrest

theorem visitFieldSliceFold_succ_empty_eq_mergeResponseSliceFold_of_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    : visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source fields (.object [])
      = mergeResponseSliceFold schema resolvers variableValues completionDepth
          source fields (.object []) :=
  visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema resolvers
    variableValues completionDepth source fields (.object [])
    (FieldSliceMergeTrace.of_responseNamesNodup_empty schema resolvers
      variableValues completionDepth source fields hnodup)

theorem
    visitSubfields_executableFieldSelections_succ_empty_eq_mergeResponseSliceFold_of_responseNamesNodup
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (fields : List ExecutableField)
    (hparents : ∀ field, field ∈ fields -> field.parentType = parentType)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    : (visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections fields) (.object [])).fst
      = mergeResponseSliceFold schema resolvers variableValues completionDepth
          source fields (.object []) := by
  have hvisit :
      visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source fields (.object []) =
      (visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections fields) (.object [])).fst :=
    visitFieldSliceFold_eq_visitSubfields_executableFieldSelections schema
      resolvers variableValues (completionDepth + 1) parentType source fields
      (.object []) hparents
  exact hvisit.symm.trans
    (visitFieldSliceFold_succ_empty_eq_mergeResponseSliceFold_of_responseNamesNodup
      schema resolvers variableValues completionDepth source fields hnodup)

theorem VisitSubfieldsPopulates.of_executableFieldSelections_trace_fold
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) (previous : ResponseValue)
    (hparents : ∀ field, field ∈ fields -> field.parentType = parentType)
    (htracePrevious
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source fields previous)
    (htraceEmpty
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source fields (.object []))
    (hfold
      : FieldSliceMergeFoldPopulates schema resolvers variableValues
          completionDepth source fields previous)
    : VisitSubfieldsPopulates schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections fields) previous := by
  unfold VisitSubfieldsPopulates
  rw [← visitFieldSliceFold_eq_visitSubfields_executableFieldSelections
      schema resolvers variableValues (completionDepth + 1) parentType source
      fields previous hparents]
  rw [← visitFieldSliceFold_eq_visitSubfields_executableFieldSelections
      schema resolvers variableValues (completionDepth + 1) parentType source
      fields (.object []) hparents]
  rw [visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema
    resolvers variableValues completionDepth source fields previous
    htracePrevious]
  rw [visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema
    resolvers variableValues completionDepth source fields (.object [])
    htraceEmpty]
  exact hfold

theorem VisitSubfieldsPopulates.of_executableFieldSelections_responseNamesNodup_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (previousFields : List (Name × ResponseValue))
    (hparents : ∀ field, field ∈ fields -> field.parentType = parentType)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hdisjoint
      : ∀ field, field ∈ fields -> field.responseName ∉ previousFields.map Prod.fst)
    : VisitSubfieldsPopulates schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections fields) (.object previousFields) :=
  VisitSubfieldsPopulates.of_executableFieldSelections_trace_fold schema
    resolvers variableValues completionDepth parentType source fields
    (.object previousFields) hparents
    (FieldSliceMergeTrace.of_responseNamesNodup_object schema resolvers
      variableValues completionDepth source fields previousFields hnodup
      hdisjoint)
    (FieldSliceMergeTrace.of_responseNamesNodup_empty schema resolvers
      variableValues completionDepth source fields hnodup)
    (FieldSliceMergeFoldPopulates.of_responseNamesNodup_object schema resolvers
      variableValues completionDepth source fields previousFields hnodup
      hdisjoint)

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
