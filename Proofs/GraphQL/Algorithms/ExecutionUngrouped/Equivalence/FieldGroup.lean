import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection.SingleFieldGroup
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.ErrorPresence
import Proofs.GraphQL.Execution.ResolverValue

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped
namespace Eager

open GraphQL.Execution

local instance : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem mergeResponseField_null_of_lookup_null (responseName : Name)
    : ∀ fields : List (Name × ResponseValue),
        lookupResponseField? responseName fields = some .null
        -> mergeResponseField responseName .null fields = fields
  | [], hlookup => by
      simp [lookupResponseField?] at hlookup
  | (fieldResponseName, response) :: rest, hlookup => by
      by_cases h : fieldResponseName == responseName
      · simp [lookupResponseField?, h] at hlookup
        subst response
        simp [mergeResponseField, mergeResponse, h]
      · simp [lookupResponseField?, mergeResponseField, h] at hlookup ⊢
        exact mergeResponseField_null_of_lookup_null responseName rest hlookup

theorem responseObjectField?_append_singleton_null_of_not_mem (responseName : Name)
    : ∀ fields : List (Name × ResponseValue),
        responseName ∉ fields.map Prod.fst
        -> responseObjectField? responseName (.object (fields ++ [(responseName, .null)]))
            = some .null
  | [], _hfresh => by
      simp [responseObjectField?, lookupResponseField?]
  | (fieldResponseName, response) :: rest, hfresh => by
      have hhead : (fieldResponseName == responseName) = false := by
        cases h : fieldResponseName == responseName
        · exact rfl
        · exfalso
          exact hfresh (by simp [beq_iff_eq.mp h])
      have hrest : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hfresh (by simp [hmem])
      have htail :
          lookupResponseField? responseName
              (rest ++ [(responseName, .null)]) =
            some .null := by
        simpa [responseObjectField?] using
          responseObjectField?_append_singleton_null_of_not_mem responseName
            rest hrest
      simp [responseObjectField?, lookupResponseField?, hhead, htail]

def groupedFieldVisitResult (responseName : Name)
    : Result (List (Name × ResponseValue)) -> ResponseValue × VisitStatus
  | .error errors => (.object [(responseName, .null)], .error errors)
  | .ok (fields, errors) => (.object fields, visitOk errors)

def rootSelectionResultOfVisit (visited : ResponseValue × VisitStatus)
    : Result (List (Name × ResponseValue)) :=
  match visited.snd with
  | .error errors => .error errors
  | .ok (_unit, errors) =>
      match visited.fst with
      | .object fields => .ok (fields, errors)
      | _ => .error (errors + 1)

def VisitStatusAlignedEquivalent (ungrouped spec : VisitStatus) : Prop :=
  match ungrouped, spec with
  | .error ungroupedErrors, .error specErrors =>
      ErrorPresenceEquivalent ungroupedErrors specErrors
  | .ok ((), ungroupedErrors), .ok ((), specErrors) =>
      ErrorPresenceEquivalent ungroupedErrors specErrors
  | _, _ => False

theorem VisitStatusAlignedEquivalent.refl (status : VisitStatus)
    : VisitStatusAlignedEquivalent status status := by
  cases status with
  | error errors =>
      exact ErrorPresenceEquivalent.refl errors
  | ok result =>
      rcases result with ⟨unitValue, errors⟩
      cases unitValue
      exact ErrorPresenceEquivalent.refl errors

def GroupedFieldVisitAlignedEquivalent
    (responseName : Name)
    (ungrouped : ResponseValue × VisitStatus)
    (spec : Result (List (Name × ResponseValue)))
    : Prop :=
  ungrouped.fst = (groupedFieldVisitResult responseName spec).fst
  ∧ VisitStatusAlignedEquivalent ungrouped.snd
      (groupedFieldVisitResult responseName spec).snd

theorem GroupedFieldVisitAlignedEquivalent.of_eq
    (responseName : Name)
    {ungrouped : ResponseValue × VisitStatus}
    {spec : Result (List (Name × ResponseValue))}
    (h : ungrouped = groupedFieldVisitResult responseName spec)
    : GroupedFieldVisitAlignedEquivalent responseName ungrouped spec := by
  subst ungrouped
  exact ⟨rfl, VisitStatusAlignedEquivalent.refl _⟩

theorem GroupedFieldVisitAlignedEquivalent.to_rootSelectionResult
    (responseName : Name)
    {ungrouped : ResponseValue × VisitStatus}
    {spec : Result (List (Name × ResponseValue))}
    : GroupedFieldVisitAlignedEquivalent responseName ungrouped spec
      -> RootSelectionResultAlignedEquivalent
          (rootSelectionResultOfVisit ungrouped)
          spec := by
  intro h
  rcases h with ⟨hvalue, hstatus⟩
  cases spec with
  | error specErrors =>
      cases ungrouped with
      | mk output status =>
          cases status with
          | error ungroupedErrors =>
              simpa [rootSelectionResultOfVisit, groupedFieldVisitResult,
                RootSelectionResultAlignedEquivalent,
                GroupedFieldVisitAlignedEquivalent,
                VisitStatusAlignedEquivalent] using hstatus
          | ok statusResult =>
              rcases statusResult with ⟨unitValue, ungroupedErrors⟩
              cases unitValue
              simp [groupedFieldVisitResult, VisitStatusAlignedEquivalent]
                at hstatus
  | ok specResult =>
      rcases specResult with ⟨specFields, specErrors⟩
      cases ungrouped with
      | mk output status =>
          cases status with
          | error ungroupedErrors =>
              cases hstatus
          | ok statusResult =>
              rcases statusResult with ⟨unitValue, ungroupedErrors⟩
              cases unitValue
              cases output with
              | object fields =>
                  simp [rootSelectionResultOfVisit, groupedFieldVisitResult,
                    RootSelectionResultAlignedEquivalent,
                    VisitStatusAlignedEquivalent] at hvalue hstatus ⊢
                  exact ⟨hvalue, hstatus⟩
              | null =>
                  simp [groupedFieldVisitResult] at hvalue
              | scalar value =>
                  simp [groupedFieldVisitResult] at hvalue
              | list values =>
                  simp [groupedFieldVisitResult] at hvalue

theorem ErrorPresenceEquivalent.add_left_congr
    {ungroupedLeft specLeft right spec : Nat}
    (hleft : ErrorPresenceEquivalent ungroupedLeft specLeft)
    (hcombined : ErrorPresenceEquivalent (specLeft + right) spec)
    : ErrorPresenceEquivalent (ungroupedLeft + right) spec :=
  ErrorPresenceEquivalent.trans
    (ErrorPresenceEquivalent.add hleft (ErrorPresenceEquivalent.refl right))
    hcombined

theorem mergeResponse_null_right (value : ResponseValue)
    : mergeResponse value .null = .null := by
  cases value <;> simp [mergeResponse]

def ExecutableFieldsMergedRaw
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (_resolved : Option (ResolverValue ObjectIdentity))
    : Prop :=
  visitSubfields schema resolvers variableValues (depth + 1)
    parentType source (executableFieldSelections (field :: fields))
    (.object [])
  = groupedFieldVisitResult responseName
      (GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields))

theorem ExecutableFieldsMergedResponse_of_raw
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    : ExecutableFieldsMergedRaw schema resolvers variableValues depth
        parentType source responseName field fields resolved
      -> ExecutableFieldsMergedResponse schema resolvers variableValues depth
          parentType source responseName field fields resolved := by
  intro hraw
  unfold ExecutableFieldsMergedRaw at hraw
  unfold ExecutableFieldsMergedResponse executeRootSelectionSet
  rw [hraw]
  cases hspec :
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields) with
  | error errors =>
      simp [groupedFieldVisitResult]
  | ok result =>
      rcases result with ⟨completedFields, errors⟩
      simp [groupedFieldVisitResult, visitOk]

theorem mergeResponseFieldResult_empty_eq_groupedFieldVisitResult_singleFieldResult
    (responseName : Name) (completed : Result ResponseValue)
    : mergeResponseFieldResult responseName completed (.object [])
      = groupedFieldVisitResult responseName
          (GraphQL.Execution.singleFieldResult responseName completed) := by
  cases completed with
  | error errors =>
      simp [mergeResponseFieldResult, groupedFieldVisitResult,
        GraphQL.Execution.singleFieldResult, resultValueOrNull, resultStatus,
        mergeResponseFieldIntoObject, mergeResponseField]
  | ok result =>
      rcases result with ⟨value, errors⟩
      simp [mergeResponseFieldResult, groupedFieldVisitResult,
        GraphQL.Execution.singleFieldResult, resultValueOrNull, resultStatus,
        mergeResponseFieldIntoObject, mergeResponseField, visitOk]

theorem mergeResponseFieldResult_empty_aligned_singleFieldResult
    (responseName : Name)
    {ungrouped spec : Result ResponseValue}
    (h : ResponseValueResultAlignedEquivalent ungrouped spec)
    : GroupedFieldVisitAlignedEquivalent responseName
        (mergeResponseFieldResult responseName ungrouped (.object []))
        (GraphQL.Execution.singleFieldResult responseName spec) := by
  cases ungrouped <;> cases spec <;>
    simp [ResponseValueResultAlignedEquivalent,
      GroupedFieldVisitAlignedEquivalent,
      VisitStatusAlignedEquivalent, groupedFieldVisitResult,
      GraphQL.Execution.singleFieldResult, mergeResponseFieldResult,
      mergeResponseFieldIntoObject, mergeResponseField,
      resultValueOrNull, resultStatus, visitOk] at h ⊢
  · exact h
  · rcases h with ⟨hvalue, herrors⟩
    exact ⟨by simp [hvalue], herrors⟩

theorem groupedFieldVisitResult_singleFieldResult_combine_neutral
    (responseName : Name)
    (leftCompleted rightCompleted combinedCompleted : Result ResponseValue)
    (hright : resultStatus rightCompleted = visitOk)
    (hcombine
      : GraphQL.Execution.Result.combine mergeResponse leftCompleted rightCompleted
        = combinedCompleted)
    : let left :=
        groupedFieldVisitResult responseName
          (GraphQL.Execution.singleFieldResult responseName leftCompleted)
      let right := mergeResponseFieldResult responseName rightCompleted left.fst
      (right.fst, combineVisitStatus left.snd right.snd)
      = groupedFieldVisitResult responseName
          (GraphQL.Execution.singleFieldResult responseName combinedCompleted) := by
  cases leftCompleted with
  | error prefixErrors =>
      cases rightCompleted with
      | error laterErrors =>
          simp [resultStatus, visitOk] at hright
      | ok laterResult =>
          rcases laterResult with ⟨laterValue, laterErrors⟩
          cases laterErrors with
          | zero =>
              cases hcombine
              cases laterValue <;> dsimp <;> simp [groupedFieldVisitResult,
                GraphQL.Execution.singleFieldResult,
                mergeResponseFieldResult, mergeResponseFieldIntoObject,
                mergeResponseField, mergeResponse, resultValueOrNull, resultStatus,
                combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine, visitOk]
          | succ laterErrors =>
              simp [resultStatus, visitOk] at hright
  | ok prefixResult =>
      rcases prefixResult with ⟨prefixValue, prefixErrors⟩
      cases rightCompleted with
      | error laterErrors =>
          simp [resultStatus, visitOk] at hright
      | ok laterResult =>
          rcases laterResult with ⟨laterValue, laterErrors⟩
          cases laterErrors with
          | zero =>
              cases hcombine
              dsimp
              simp [groupedFieldVisitResult, GraphQL.Execution.singleFieldResult, mergeResponseFieldResult, mergeResponseFieldIntoObject, mergeResponseField, resultValueOrNull, resultStatus, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk]
          | succ laterErrors =>
              simp [resultStatus, visitOk] at hright

theorem groupedFieldVisitResult_singleFieldResult_combine_aligned
    (responseName : Name)
    (leftCompleted rightCompleted combinedCompleted : Result ResponseValue)
    (hcombine
      : ResponseValueResultAlignedEquivalent
          (GraphQL.Execution.Result.combine mergeResponse leftCompleted rightCompleted)
          combinedCompleted)
    : let left :=
        groupedFieldVisitResult responseName
          (GraphQL.Execution.singleFieldResult responseName leftCompleted)
      let right := mergeResponseFieldResult responseName rightCompleted left.fst
      RootSelectionResultAlignedEquivalent
        (rootSelectionResultOfVisit (right.fst, combineVisitStatus left.snd right.snd))
        (GraphQL.Execution.singleFieldResult responseName combinedCompleted) := by
  cases leftCompleted <;> cases rightCompleted <;> cases combinedCompleted <;>
    simp [ResponseValueResultAlignedEquivalent,
      RootSelectionResultAlignedEquivalent, rootSelectionResultOfVisit,
      groupedFieldVisitResult, GraphQL.Execution.singleFieldResult,
      mergeResponseFieldResult, mergeResponseFieldIntoObject,
      mergeResponseField, resultValueOrNull, resultStatus,
      combineVisitStatus, visitOk, GraphQL.Execution.Result.combine,
      mergeResponse, ErrorPresenceEquivalent] at hcombine ⊢
  all_goals omega

theorem executeRootSelectionSet_append_one_aligned_of_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (prefixSelectionSet laterSelectionSet : List Selection)
    (responseName : Name)
    (prefixCompleted laterCompleted combinedCompleted : Result ResponseValue)
    (hprefix
      : visitSubfields schema resolvers variableValues depth parentType source
          prefixSelectionSet (.object [])
        = groupedFieldVisitResult responseName
            (GraphQL.Execution.singleFieldResult responseName prefixCompleted))
    (htail
      : visitSubfields schema resolvers variableValues depth parentType source
          laterSelectionSet
          (groupedFieldVisitResult responseName
            (GraphQL.Execution.singleFieldResult responseName prefixCompleted)).fst
        = mergeResponseFieldResult responseName laterCompleted
            (groupedFieldVisitResult responseName
              (GraphQL.Execution.singleFieldResult responseName prefixCompleted)).fst)
    (haligned
      : ResponseValueResultAlignedEquivalent
          (GraphQL.Execution.Result.combine mergeResponse prefixCompleted laterCompleted)
          combinedCompleted)
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues depth parentType
          source (prefixSelectionSet ++ laterSelectionSet))
        (GraphQL.Execution.singleFieldResult responseName combinedCompleted) := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source prefixSelectionSet laterSelectionSet (.object [])]
  rw [hprefix]
  simp [htail]
  exact
    groupedFieldVisitResult_singleFieldResult_combine_aligned responseName
      prefixCompleted laterCompleted combinedCompleted haligned

theorem groupedFieldVisitResult_singleFieldResult_combine_visit_aligned
    (responseName : Name)
    (leftCompleted rightCompleted combinedCompleted : Result ResponseValue)
    (left : ResponseValue × VisitStatus)
    (hleft
      : GroupedFieldVisitAlignedEquivalent responseName left
          (GraphQL.Execution.singleFieldResult responseName leftCompleted))
    (hcombine
      : ResponseValueResultAlignedEquivalent
          (GraphQL.Execution.Result.combine mergeResponse leftCompleted rightCompleted)
          combinedCompleted)
    : GroupedFieldVisitAlignedEquivalent responseName
        (
          (mergeResponseFieldResult responseName rightCompleted left.fst).fst,
          combineVisitStatus left.snd
            (mergeResponseFieldResult responseName rightCompleted left.fst).snd
        )
        (GraphQL.Execution.singleFieldResult responseName combinedCompleted) := by
  rcases left with ⟨leftOutput, leftStatus⟩
  rcases hleft with ⟨hvalue, hstatus⟩
  cases leftCompleted <;> cases rightCompleted <;> cases combinedCompleted <;>
    cases leftStatus with
    | error leftErrors =>
        simp [GraphQL.Execution.singleFieldResult, groupedFieldVisitResult] at hvalue
        subst leftOutput
        simp [GroupedFieldVisitAlignedEquivalent,
          GraphQL.Execution.singleFieldResult, groupedFieldVisitResult,
          VisitStatusAlignedEquivalent, ResponseValueResultAlignedEquivalent,
          GraphQL.Execution.Result.combine, mergeResponseFieldResult,
          combineVisitStatus, resultValueOrNull, resultStatus,
          mergeResponseFieldIntoObject, mergeResponseField, mergeResponse] at hstatus hcombine ⊢
        all_goals try
          exact ErrorPresenceEquivalent.add_left_congr hstatus hcombine
        all_goals try
          exact ErrorPresenceEquivalent.add_left_congr hstatus hcombine.2
        all_goals try cases hstatus
    | ok leftStatusResult =>
        rcases leftStatusResult with ⟨unitValue, leftErrors⟩
        cases unitValue
        simp [GraphQL.Execution.singleFieldResult, groupedFieldVisitResult] at hvalue
        subst leftOutput
        simp [GroupedFieldVisitAlignedEquivalent,
          GraphQL.Execution.singleFieldResult, groupedFieldVisitResult,
          VisitStatusAlignedEquivalent, ResponseValueResultAlignedEquivalent,
          GraphQL.Execution.Result.combine, mergeResponseFieldResult,
          combineVisitStatus, resultValueOrNull, resultStatus,
          mergeResponseFieldIntoObject, mergeResponseField, visitOk] at hstatus hcombine ⊢
        all_goals try
          exact ⟨by simp [hcombine.1],
            ErrorPresenceEquivalent.add_left_congr hstatus hcombine.2⟩
        all_goals try
          exact ⟨by simp [mergeResponse_null_right],
            ErrorPresenceEquivalent.add_left_congr hstatus hcombine⟩
        all_goals try
          exact ErrorPresenceEquivalent.add_left_congr hstatus hcombine
        all_goals try
          exact ErrorPresenceEquivalent.add_left_congr hstatus hcombine.2
        all_goals try cases hstatus

theorem executeRootSelectionSet_append_one_visit_aligned_of_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (prefixSelectionSet laterSelectionSet : List Selection)
    (responseName : Name)
    (prefixCompleted laterCompleted combinedCompleted : Result ResponseValue)
    (hprefix
      : GroupedFieldVisitAlignedEquivalent responseName
          (visitSubfields schema resolvers variableValues depth parentType source
            prefixSelectionSet (.object []))
          (GraphQL.Execution.singleFieldResult responseName prefixCompleted))
    (htail
      : visitSubfields schema resolvers variableValues depth parentType source
          laterSelectionSet
          (visitSubfields schema resolvers variableValues depth parentType source
            prefixSelectionSet (.object [])).fst
        = mergeResponseFieldResult responseName laterCompleted
            (visitSubfields schema resolvers variableValues depth parentType source
              prefixSelectionSet (.object [])).fst)
    (haligned
      : ResponseValueResultAlignedEquivalent
          (GraphQL.Execution.Result.combine mergeResponse prefixCompleted laterCompleted)
          combinedCompleted)
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues depth parentType
          source (prefixSelectionSet ++ laterSelectionSet))
        (GraphQL.Execution.singleFieldResult responseName combinedCompleted) := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source prefixSelectionSet laterSelectionSet (.object [])]
  simp [htail]
  exact
    (groupedFieldVisitResult_singleFieldResult_combine_visit_aligned responseName
      prefixCompleted laterCompleted combinedCompleted
      (visitSubfields schema resolvers variableValues depth parentType source
        prefixSelectionSet (.object []))
      hprefix haligned).to_rootSelectionResult responseName

theorem visitSubfields_append_one_visit_aligned_of_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (prefixSelectionSet laterSelectionSet : List Selection)
    (responseName : Name)
    (prefixCompleted laterCompleted combinedCompleted : Result ResponseValue)
    (hprefix
      : GroupedFieldVisitAlignedEquivalent responseName
          (visitSubfields schema resolvers variableValues depth parentType source
            prefixSelectionSet (.object []))
          (GraphQL.Execution.singleFieldResult responseName prefixCompleted))
    (htail
      : visitSubfields schema resolvers variableValues depth parentType source
          laterSelectionSet
          (visitSubfields schema resolvers variableValues depth parentType source
            prefixSelectionSet (.object [])).fst
        = mergeResponseFieldResult responseName laterCompleted
            (visitSubfields schema resolvers variableValues depth parentType source
              prefixSelectionSet (.object [])).fst)
    (haligned
      : ResponseValueResultAlignedEquivalent
          (GraphQL.Execution.Result.combine mergeResponse prefixCompleted laterCompleted)
          combinedCompleted)
    : GroupedFieldVisitAlignedEquivalent responseName
        (visitSubfields schema resolvers variableValues depth parentType source
          (prefixSelectionSet ++ laterSelectionSet) (.object []))
        (GraphQL.Execution.singleFieldResult responseName combinedCompleted) := by
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source prefixSelectionSet laterSelectionSet (.object [])]
  simp [htail]
  exact
    groupedFieldVisitResult_singleFieldResult_combine_visit_aligned responseName
      prefixCompleted laterCompleted combinedCompleted
      (visitSubfields schema resolvers variableValues depth parentType source
        prefixSelectionSet (.object []))
      hprefix haligned

theorem completeValue_object_append_eq_visitSubfields_append_result
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hincludes : schema.typeIncludesObjectBool parentType runtimeType = true)
    : completeValue schema resolvers variableValues (childDepth + 1)
        (.named parentType) (firstSelectionSet ++ secondSelectionSet)
        (.object runtimeType identity) none
      = let firstResult :=
          visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) firstSelectionSet (.object [])
        let secondResult :=
          visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) secondSelectionSet firstResult.fst
        catchVisitBubbleAsNull secondResult.fst
          (combineVisitStatus firstResult.snd secondResult.snd) := by
  simp [completeValue, hincludes, reuseOrCreateObject?]
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    childDepth runtimeType (.object runtimeType identity) firstSelectionSet
    secondSelectionSet (.object [])]

def VisitSubfieldsErrorNeutral
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (current : ResponseValue)
    : Prop :=
  (visitSubfields schema resolvers variableValues depth parentType source
    selectionSet current).snd
  = visitOk

theorem resultValueOrNull_nonNullCompletion (completed : Result ResponseValue)
    : resultValueOrNull (nonNullCompletion completed) = resultValueOrNull completed := by
  cases completed with
  | error errors =>
      simp [nonNullCompletion, resultValueOrNull]
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value <;> cases errors <;>
        simp [nonNullCompletion, resultValueOrNull]

theorem resultStatus_nonNullCompletion_eq_ok_of_status_eq_ok_of_nonNull
    (completed : Result ResponseValue)
    (hstatus : resultStatus completed = visitOk)
    (hnonNull : resultValueOrNull completed ≠ .null)
    : resultStatus (nonNullCompletion completed) = visitOk := by
  cases completed with
  | error errors =>
      simp [resultStatus, visitOk] at hstatus
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value <;> cases errors <;>
        simp [resultStatus, visitOk, resultValueOrNull, nonNullCompletion]
          at hstatus hnonNull ⊢

theorem resultStatus_completeResolvedValue_nonNull_eq_ok_of_inner_status_eq_ok_of_nonNull
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (inner : TypeRef)
    (selectionSet : List Selection) (resolved : ResolverValue ObjectIdentity)
    (previous? : Option ResponseValue)
    (hstatus
      : resultStatus
          (completeResolvedValue schema resolvers variableValues depth inner
            selectionSet resolved previous?)
        = visitOk)
    (hnonNull
      : resultValueOrNull
          (completeResolvedValue schema resolvers variableValues depth inner
            selectionSet resolved previous?)
        ≠ .null)
    : resultStatus
        (completeResolvedValue schema resolvers variableValues depth
          (.nonNull inner) selectionSet resolved previous?)
      = visitOk := by
  cases hreuse :
      reusablePreviousValue? schema (.nonNull inner) previous? with
  | some previous =>
      simp [completeResolvedValue, hreuse, resultStatus, visitOk]
  | none =>
      simpa [completeResolvedValue, hreuse] using
        resultStatus_nonNullCompletion_eq_ok_of_status_eq_ok_of_nonNull
          (completeResolvedValue schema resolvers variableValues depth inner
            selectionSet resolved previous?)
          hstatus hnonNull

theorem resultValueOrNull_completeResolvedValue_nonNull_ne_null_of_inner_ne_null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (inner : TypeRef) (selectionSet : List Selection)
    (resolved : ResolverValue ObjectIdentity) (previous? : Option ResponseValue)
    (hnonNull
      : resultValueOrNull
          (completeResolvedValue schema resolvers variableValues depth inner
            selectionSet resolved previous?)
        ≠ .null)
    : resultValueOrNull
        (completeResolvedValue schema resolvers variableValues depth
          (.nonNull inner) selectionSet resolved previous?)
      ≠ .null := by
  cases hinner :
      completeResolvedValue schema resolvers variableValues depth inner
        selectionSet resolved previous? with
  | error errors =>
      simp [resultValueOrNull, hinner] at hnonNull
  | ok result =>
      rcases result with ⟨value, errors⟩
      have hvalue : value ≠ .null := by
        intro hnull
        exact hnonNull (by
          simp [resultValueOrNull, hinner, hnull])
      have hwrapped :=
        completeResolvedValue_nonNull_ok_of_inner_ok
          schema resolvers variableValues depth inner selectionSet resolved
          previous? value errors hinner hvalue
      simpa [resultValueOrNull, hwrapped] using hvalue

mutual
  theorem specCompleteValue_eq_of_no_object
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      : ∀ (depth : Nat) (fieldType : TypeRef)
            (fields otherFields : List ExecutableField)
            (resolved : ResolverValue ObjectIdentity),
          fieldType.isCompositeBool schema = false
          -> GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldType fields resolved
              = GraphQL.Execution.completeValue schema resolvers variableValues
                  depth fieldType otherFields resolved
    | 0, fieldType, fields, otherFields, resolved, _hno => by
        simp [GraphQL.Execution.completeValue]
    | depth + 1, .named typeName, fields, otherFields, resolved, hno => by
        cases resolved with
        | null =>
            simp [GraphQL.Execution.completeValue]
        | scalar value =>
            simp [GraphQL.Execution.completeValue]
        | object runtimeType identity =>
            have hincludes :
                schema.typeIncludesObjectBool typeName runtimeType = false := by
              cases hlookup : schema.lookupType typeName with
              | none =>
                  simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes,
                    hlookup]
              | some typeDefinition =>
                  cases typeDefinition <;>
                    simp [TypeRef.isCompositeBool, TypeRef.namedType,
                      Schema.typeIncludesObjectBool,
                      Schema.getPossibleTypes, hlookup] at hno ⊢
            simp [GraphQL.Execution.completeValue, hincludes]
        | list values =>
            simp [GraphQL.Execution.completeValue]
    | depth + 1, .list inner, fields, otherFields, resolved, hno => by
        cases resolved with
        | null =>
            simp [GraphQL.Execution.completeValue]
        | scalar value =>
            simp [GraphQL.Execution.completeValue]
        | object runtimeType identity =>
            simp [GraphQL.Execution.completeValue]
        | list values =>
            have hinner :
                inner.isCompositeBool schema = false := by
              simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hno
            have hlist :=
              specCompleteValueList_eq_of_no_object schema resolvers
                variableValues depth inner fields otherFields values hinner
            simp [GraphQL.Execution.completeValue, hlist]
    | depth + 1, .nonNull inner, fields, otherFields, resolved, hno => by
        have hinner :
            inner.isCompositeBool schema = false := by
          simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hno
        have hvalue :=
          specCompleteValue_eq_of_no_object schema resolvers variableValues
            (depth + 1) inner fields otherFields resolved hinner
        simp [GraphQL.Execution.completeValue, hvalue]
  termination_by depth fieldType _fields _otherFields resolved _hno =>
    (depth, 0, sizeOf fieldType, sizeOf resolved)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem specCompleteValueList_eq_of_no_object
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      : ∀ (depth : Nat) (itemType : TypeRef)
            (fields otherFields : List ExecutableField)
            (values : List (ResolverValue ObjectIdentity)),
          itemType.isCompositeBool schema = false
          -> GraphQL.Execution.completeValueList schema resolvers variableValues
                depth itemType fields values
              = GraphQL.Execution.completeValueList schema resolvers variableValues
                  depth itemType otherFields values
    | depth, itemType, fields, otherFields, [], _hno => by
        simp [GraphQL.Execution.completeValueList]
    | depth, itemType, fields, otherFields, value :: values, hno => by
        have hhead :=
          specCompleteValue_eq_of_no_object schema resolvers variableValues
            depth itemType fields otherFields value hno
        have htail :=
          specCompleteValueList_eq_of_no_object schema resolvers variableValues
            depth itemType fields otherFields values hno
        simp [GraphQL.Execution.completeValueList, hhead, htail]
  termination_by depth itemType _fields _otherFields values _hno =>
    (depth, 1, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega
end

theorem resultValueOrNull_catchVisitBubbleAsNull
    (value : ResponseValue) (status : VisitStatus)
    : resultValueOrNull (catchVisitBubbleAsNull value status)
      = match status with
        | .error _errors => .null
        | .ok _result => value := by
  cases status with
  | error errors =>
      simp [catchVisitBubbleAsNull, resultValueOrNull]
  | ok result =>
      rcases result with ⟨unitValue, errors⟩
      cases unitValue
      simp [catchVisitBubbleAsNull, resultValueOrNull]

theorem completeValue_object_append_result_of_absorbs_errorNeutral
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hincludes : schema.typeIncludesObjectBool parentType runtimeType = true)
    (habsorbs
      : ResponseAbsorbs
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) firstSelectionSet (.object []))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) secondSelectionSet
            (visitSubfields schema resolvers variableValues childDepth runtimeType
              (.object runtimeType identity) firstSelectionSet (.object [])).fst))
    (herrors
      : VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
          runtimeType (.object runtimeType identity) secondSelectionSet
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) firstSelectionSet (.object [])).fst)
    : let first :=
        completeValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) firstSelectionSet (.object runtimeType identity)
          none
      GraphQL.Execution.Result.combine mergeResponse first
        (completeResolvedValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) secondSelectionSet (.object runtimeType identity)
          (some (resultValueOrNull first)))
      = completeValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) (firstSelectionSet ++ secondSelectionSet)
          (.object runtimeType identity) none := by
  rw [completeValue_object_append_eq_visitSubfields_append_result schema
    resolvers variableValues childDepth parentType runtimeType identity
    firstSelectionSet secondSelectionSet hincludes]
  unfold ResponseAbsorbs at habsorbs
  unfold VisitSubfieldsErrorNeutral at herrors
  have hparentComposite :
      (TypeRef.named parentType).isCompositeBool schema = true := by
    cases hlookup : schema.lookupType parentType with
    | none =>
        simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup]
          at hincludes
    | some typeDefinition =>
        cases typeDefinition <;>
          simp [TypeRef.isCompositeBool, TypeRef.namedType,
            Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup]
            at hincludes ⊢
  cases hfirst :
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) firstSelectionSet (.object []) with
  | mk firstOutput firstStatus =>
      cases hsecond :
          visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) secondSelectionSet firstOutput with
      | mk secondOutput secondStatus =>
          simp [hfirst, hsecond] at habsorbs herrors
          cases firstStatus with
          | error firstErrors =>
              simp [completeResolvedValue_previous_null, completeValue, reuseOrCreateObject?, hincludes, hfirst, resultValueOrNull, hsecond, herrors, catchVisitBubbleAsNull, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk, mergeResponse]
          | ok firstStatusResult =>
              rcases firstStatusResult with ⟨unitValue, firstErrors⟩
              cases unitValue
              obtain ⟨firstFields, hfirstFields⟩ :=
                visitSubfields_preserves_object schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  firstSelectionSet []
              rw [hfirst] at hfirstFields
              simp at hfirstFields
              subst firstOutput
              simp [completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateObject?, hincludes, hparentComposite, hfirst, resultValueOrNull, hsecond, herrors, habsorbs, catchVisitBubbleAsNull, combineVisitStatus, GraphQL.Execution.Result.combine, visitOk]

theorem completeValue_object_append_result_aligned_of_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hincludes : schema.typeIncludesObjectBool parentType runtimeType = true)
    (habsorbs
      : ResponseAbsorbs
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) firstSelectionSet (.object []))
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) secondSelectionSet
            (visitSubfields schema resolvers variableValues childDepth runtimeType
              (.object runtimeType identity) firstSelectionSet (.object [])).fst))
    : let first :=
        completeValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) firstSelectionSet (.object runtimeType identity)
          none
      ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse first
          (completeResolvedValue schema resolvers variableValues (childDepth + 1)
            (.named parentType) secondSelectionSet (.object runtimeType identity)
            (some (resultValueOrNull first))))
        (completeValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) (firstSelectionSet ++ secondSelectionSet)
          (.object runtimeType identity) none) := by
  rw [completeValue_object_append_eq_visitSubfields_append_result schema
    resolvers variableValues childDepth parentType runtimeType identity
    firstSelectionSet secondSelectionSet hincludes]
  unfold ResponseAbsorbs at habsorbs
  have hparentComposite :
      (TypeRef.named parentType).isCompositeBool schema = true := by
    cases hlookup : schema.lookupType parentType with
    | none =>
        simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup]
          at hincludes
    | some typeDefinition =>
        cases typeDefinition <;>
          simp [TypeRef.isCompositeBool, TypeRef.namedType,
            Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup]
            at hincludes ⊢
  cases hfirst :
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) firstSelectionSet (.object []) with
  | mk firstOutput firstStatus =>
      cases hsecond :
          visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) secondSelectionSet firstOutput with
      | mk secondOutput secondStatus =>
          simp [hfirst, hsecond] at habsorbs
          cases firstStatus with
          | error firstErrors =>
              have hfirstPositive : 0 < firstErrors :=
                visitSubfields_status_error_positive schema resolvers
                  variableValues childDepth runtimeType
                  (.object runtimeType identity) firstSelectionSet (.object [])
                  firstErrors (by simp [hfirst])
              cases secondStatus with
              | error secondErrors =>
                  simp [completeResolvedValue_previous_null, completeValue,
                    reuseOrCreateObject?, hincludes, hfirst, resultValueOrNull,
                    hsecond, catchVisitBubbleAsNull, combineVisitStatus,
                    GraphQL.Execution.Result.combine, mergeResponse,
                    ResponseValueResultAlignedEquivalent,
                    ErrorPresenceEquivalent]
                  omega
              | ok secondStatusResult =>
                  rcases secondStatusResult with ⟨unitValue, secondErrors⟩
                  cases unitValue
                  simp [completeResolvedValue_previous_null, completeValue,
                    reuseOrCreateObject?, hincludes, hfirst, resultValueOrNull,
                    hsecond, catchVisitBubbleAsNull, combineVisitStatus,
                    GraphQL.Execution.Result.combine, mergeResponse,
                    ResponseValueResultAlignedEquivalent,
                    ErrorPresenceEquivalent]
                  omega
          | ok firstStatusResult =>
              rcases firstStatusResult with ⟨unitValue, firstErrors⟩
              cases unitValue
              obtain ⟨firstFields, hfirstFields⟩ :=
                visitSubfields_preserves_object schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  firstSelectionSet []
              rw [hfirst] at hfirstFields
              simp at hfirstFields
              subst firstOutput
              cases secondStatus with
              | error secondErrors =>
                  simp [completeResolvedValue, reusablePreviousValue?,
                    completeValue, reuseOrCreateObject?, hincludes,
                    hparentComposite, hfirst, resultValueOrNull, hsecond,
                    catchVisitBubbleAsNull, combineVisitStatus,
                    GraphQL.Execution.Result.combine, mergeResponse,
                    ResponseValueResultAlignedEquivalent,
                    ErrorPresenceEquivalent]
              | ok secondStatusResult =>
                  rcases secondStatusResult with ⟨unitValue, secondErrors⟩
                  cases unitValue
                  simp [completeResolvedValue, reusablePreviousValue?,
                    completeValue, reuseOrCreateObject?, hincludes,
                    hparentComposite, hfirst, resultValueOrNull, hsecond,
                    habsorbs, catchVisitBubbleAsNull, combineVisitStatus,
                    GraphQL.Execution.Result.combine,
                    ResponseValueResultAlignedEquivalent,
                    ErrorPresenceEquivalent]

theorem resultStatus_completeValue_object_append_second_of_errorNeutral
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (firstSelectionSet secondSelectionSet : List Selection)
    (hincludes : schema.typeIncludesObjectBool parentType runtimeType = true)
    (herrors
      : VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
          runtimeType (.object runtimeType identity) secondSelectionSet
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) firstSelectionSet (.object [])).fst)
    : let first :=
        completeValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) firstSelectionSet (.object runtimeType identity)
          none
      resultStatus
        (completeResolvedValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) secondSelectionSet (.object runtimeType identity)
          (some (resultValueOrNull first)))
      = visitOk := by
  unfold VisitSubfieldsErrorNeutral at herrors
  have hparentComposite :
      (TypeRef.named parentType).isCompositeBool schema = true := by
    cases hlookup : schema.lookupType parentType with
    | none =>
        simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup]
          at hincludes
    | some typeDefinition =>
        cases typeDefinition <;>
          simp [TypeRef.isCompositeBool, TypeRef.namedType,
            Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup]
            at hincludes ⊢
  cases hfirst :
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) firstSelectionSet (.object []) with
  | mk firstOutput firstStatus =>
      simp [hfirst] at herrors
      cases firstStatus with
      | error firstErrors =>
          simp [completeResolvedValue_previous_null, completeValue, reuseOrCreateObject?, hincludes, hfirst, resultValueOrNull, catchVisitBubbleAsNull, resultStatus, visitOk]
      | ok firstStatusResult =>
          rcases firstStatusResult with ⟨unitValue, firstErrors⟩
          cases unitValue
          obtain ⟨firstFields, hfirstFields⟩ :=
            visitSubfields_preserves_object schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              firstSelectionSet []
          rw [hfirst] at hfirstFields
          simp at hfirstFields
          subst firstOutput
          simp [completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateObject?, hincludes, hparentComposite, hfirst, resultValueOrNull, catchVisitBubbleAsNull, herrors, resultStatus, visitOk]

theorem completeValue_named_group_append_one_result_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet prefixFields
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later])
                  }
                initial := .object []
              })
    : GraphQL.Execution.Result.combine mergeResponse
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          (.named parentType) prefixFields resolved)
        (completeResolvedValue schema resolvers variableValues depth (.named parentType)
          later.selectionSet resolved
          (some
            (resultValueOrNull
              (GraphQL.Execution.completeValue schema resolvers variableValues depth
                (.named parentType) prefixFields resolved))))
      = GraphQL.Execution.completeValue schema resolvers variableValues depth
          (.named parentType) (prefixFields ++ [later]) resolved := by
  have hprefix :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
        none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved :=
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues prefixFields depth parentType resolved hprefixChildren
  have hextended :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) (prefixFields ++ [later]) resolved :=
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues (prefixFields ++ [later]) depth parentType resolved
      hchildren
  have hmergedAppend :
      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) =
        GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
          later.selectionSet := by
    simp [GraphQL.Execution.mergedFieldSelectionSet_append]
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, GraphQL.Execution.Result.combine]
  | succ childDepth =>
      cases resolved with
      | null =>
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse]
      | scalar value =>
            by_cases hcomposite :
                (TypeRef.named parentType).isCompositeBool schema = true
            · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine, hcomposite]
            · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse, hcomposite]
      | list values =>
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · have hslice :
                GraphQL.Execution.Result.combine mergeResponse
                    (completeValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                      (.object runtimeType identity) none)
                  (completeResolvedValue schema resolvers variableValues
                    (childDepth + 1) (.named parentType)
                    later.selectionSet (.object runtimeType identity)
                      (some (resultValueOrNull
                        (completeValue schema resolvers variableValues
                          (childDepth + 1) (.named parentType)
                          (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                          (.object runtimeType identity) none)))) =
                completeValue schema resolvers variableValues (childDepth + 1)
                    (.named parentType)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (prefixFields ++ [later]))
                    (.object runtimeType identity) none := by
              calc
                GraphQL.Execution.Result.combine mergeResponse
                      (completeValue schema resolvers variableValues
                        (childDepth + 1) (.named parentType)
                        (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                        (.object runtimeType identity) none)
                    (completeResolvedValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      later.selectionSet (.object runtimeType identity)
                        (some (resultValueOrNull
                          (completeValue schema resolvers variableValues
                            (childDepth + 1) (.named parentType)
                            (GraphQL.Execution.mergedFieldSelectionSet
                              prefixFields)
                            (.object runtimeType identity) none)))) =
                  completeValue schema resolvers variableValues (childDepth + 1)
                      (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
                        later.selectionSet)
                      (.object runtimeType identity) none := by
                    exact
                      completeValue_object_append_result_of_absorbs_errorNeutral
                        schema resolvers variableValues childDepth parentType
                        runtimeType identity
                        (GraphQL.Execution.mergedFieldSelectionSet
                          prefixFields)
                        later.selectionSet hincludes
                        (hobjects childDepth runtimeType identity
                          (Nat.lt_succ_self childDepth))
                        (herrors childDepth runtimeType identity
                          (Nat.lt_succ_self childDepth))
                _ =
                  completeValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet
                        (prefixFields ++ [later]))
                      (.object runtimeType identity) none := by
                    rw [hmergedAppend]
            rw [← hprefix]
            rw [← hextended]
            exact hslice
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, hnotIncludes, resultValueOrNull, GraphQL.Execution.Result.combine, completeResolvedValue_previous_null]

theorem resultStatus_completeValue_named_group_append_second_eq_ok
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet prefixFields
                  }
                initial := .object []
              })
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object [])))
    : resultStatus
        (completeResolvedValue schema resolvers variableValues depth (.named parentType)
          later.selectionSet resolved
          (some
            (resultValueOrNull
              (GraphQL.Execution.completeValue schema resolvers variableValues depth
                (.named parentType) prefixFields resolved))))
      = visitOk := by
  have hprefix :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
        none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved :=
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues prefixFields depth parentType resolved hprefixChildren
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, resultStatus, visitOk]
  | succ childDepth =>
      cases resolved with
      | null =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
      | scalar value =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk, hcomposite]
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar, resultValueOrNull, resultStatus, visitOk, hcomposite]
      | list values =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · have hrightLocal :=
              resultStatus_completeValue_object_append_second_of_errorNeutral
                schema resolvers variableValues childDepth parentType
                runtimeType identity
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                later.selectionSet hincludes
                (herrors childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth))
            dsimp at hrightLocal
            rw [hprefix] at hrightLocal
            exact hrightLocal
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hnotIncludes, resultValueOrNull, resultStatus, visitOk]

theorem completeValue_named_group_append_one_result_aligned_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet prefixFields
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                  (.object []))))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later])
                  }
                initial := .object []
              })
    : ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse
          (GraphQL.Execution.completeValue schema resolvers variableValues depth
            (.named parentType) prefixFields resolved)
          (completeResolvedValue schema resolvers variableValues depth
            (.named parentType) later.selectionSet resolved
            (some
              (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth (.named parentType) prefixFields resolved)))))
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          (.named parentType) (prefixFields ++ [later]) resolved) := by
  have hprefix :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
        none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved :=
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues prefixFields depth parentType resolved hprefixChildren
  have hextended :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) (prefixFields ++ [later]) resolved :=
    completeValue_group_eq_spec_of_guarded_merged_child_states schema resolvers
      variableValues (prefixFields ++ [later]) depth parentType resolved
      hchildren
  have hmergedAppend :
      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) =
        GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
          later.selectionSet := by
    simp [GraphQL.Execution.mergedFieldSelectionSet_append]
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
          outOfFuel, resultValueOrNull, GraphQL.Execution.Result.combine,
          ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
  | succ childDepth =>
      cases resolved with
      | null =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
            resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse,
            ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | scalar value =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
              resultValueOrNull, GraphQL.Execution.Result.combine, hcomposite,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar,
              resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse,
              hcomposite, ResponseValueResultAlignedEquivalent,
              ErrorPresenceEquivalent]
      | list values =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
            resultValueOrNull, GraphQL.Execution.Result.combine,
            ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · rw [← hprefix]
            rw [← hextended]
            rw [hmergedAppend]
            exact
              completeValue_object_append_result_aligned_of_absorbs schema
                resolvers variableValues childDepth parentType runtimeType
                identity
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                later.selectionSet hincludes
                (hobjects childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth))
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, hnotIncludes, resultValueOrNull,
              GraphQL.Execution.Result.combine, completeResolvedValue_previous_null,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]

theorem completeValue_named_group_append_one_result_aligned_spec_of_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet prefixFields
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                  (.object []))))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later])
                  }
                initial := .object []
              })
    : ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse
          (GraphQL.Execution.completeValue schema resolvers variableValues depth
            (.named parentType) prefixFields resolved)
          (completeResolvedValue schema resolvers variableValues depth
            (.named parentType) later.selectionSet resolved
            (some
              (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth (.named parentType) prefixFields resolved)))))
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          (.named parentType) (prefixFields ++ [later]) resolved) := by
  have hprefix :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
        none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved :=
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues prefixFields depth parentType resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        exact hprefixChildren childDepth runtimeType identity hlt hcontains
          (by simpa using hincludes))
  have hextended :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) (prefixFields ++ [later]) resolved :=
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues (prefixFields ++ [later]) depth parentType resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        exact hchildren childDepth runtimeType identity hlt hcontains
          (by simpa using hincludes))
  have hmergedAppend :
      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) =
        GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
          later.selectionSet := by
    simp [GraphQL.Execution.mergedFieldSelectionSet_append]
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
          outOfFuel, resultValueOrNull, GraphQL.Execution.Result.combine,
          ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
  | succ childDepth =>
      cases resolved with
      | null =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
            resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse,
            ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | scalar value =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
              resultValueOrNull, GraphQL.Execution.Result.combine, hcomposite,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar,
              resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse,
              hcomposite, ResponseValueResultAlignedEquivalent,
              ErrorPresenceEquivalent]
      | list values =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
            resultValueOrNull, GraphQL.Execution.Result.combine,
            ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · rw [← hprefix]
            rw [← hextended]
            rw [hmergedAppend]
            exact
              completeValue_object_append_result_aligned_of_absorbs schema
                resolvers variableValues childDepth parentType runtimeType
                identity
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                later.selectionSet hincludes
                (hobjects childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth) ValueContainsObject.here)
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
              hnotIncludes, resultValueOrNull, GraphQL.Execution.Result.combine,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]

theorem completeValue_named_group_append_one_result_aligned_spec_of_contained_aligned
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool parentType runtimeType = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)))
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                  (.object []))))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool parentType runtimeType = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later])))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))))
    : ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse
          (GraphQL.Execution.completeValue schema resolvers variableValues depth
            (.named parentType) prefixFields resolved)
          (completeResolvedValue schema resolvers variableValues depth
            (.named parentType) later.selectionSet resolved
            (some
              (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth (.named parentType) prefixFields resolved)))))
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          (.named parentType) (prefixFields ++ [later]) resolved) := by
  let ungroupedPrefix :=
    completeValue schema resolvers variableValues depth (.named parentType)
      (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved none
  let specPrefix :=
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      (.named parentType) prefixFields resolved
  let ungroupedExtended :=
    completeValue schema resolvers variableValues depth (.named parentType)
      (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
      resolved none
  let specExtended :=
    GraphQL.Execution.completeValue schema resolvers variableValues depth
      (.named parentType) (prefixFields ++ [later]) resolved
  have hprefix :
      ResponseValueResultAlignedEquivalent ungroupedPrefix specPrefix := by
    dsimp [ungroupedPrefix, specPrefix]
    exact
      completeValue_group_aligned_of_contained_child_states schema resolvers
        variableValues prefixFields (.named parentType) depth resolved
        (by
          intro childDepth runtimeType identity hlt hcontains hincludes
          exact hprefixChildren childDepth runtimeType identity hlt hcontains
            (by simpa [TypeRef.namedType] using hincludes))
  have hextended :
      ResponseValueResultAlignedEquivalent ungroupedExtended specExtended := by
    dsimp [ungroupedExtended, specExtended]
    exact
      completeValue_group_aligned_of_contained_child_states schema resolvers
        variableValues (prefixFields ++ [later]) (.named parentType) depth
        resolved
        (by
          intro childDepth runtimeType identity hlt hcontains hincludes
          exact hchildren childDepth runtimeType identity hlt hcontains
            (by simpa [TypeRef.namedType] using hincludes))
  have hmergedAppend :
      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) =
        GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
          later.selectionSet := by
    simp [GraphQL.Execution.mergedFieldSelectionSet_append]
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
          outOfFuel, resultValueOrNull, GraphQL.Execution.Result.combine,
          ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
  | succ childDepth =>
      cases resolved with
      | null =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
            resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse,
            ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | scalar value =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
              resultValueOrNull, GraphQL.Execution.Result.combine, hcomposite,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar,
              resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse,
              hcomposite, ResponseValueResultAlignedEquivalent,
              ErrorPresenceEquivalent]
      | list values =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
            resultValueOrNull, GraphQL.Execution.Result.combine,
            ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · have hvalue :
                resultValueOrNull ungroupedPrefix = resultValueOrNull specPrefix :=
              ResponseValueResultAlignedEquivalent.resultValueOrNull_eq hprefix
            have htail :
                completeResolvedValue schema resolvers variableValues
                    (childDepth + 1) (.named parentType)
                    later.selectionSet (.object runtimeType identity)
                    (some (resultValueOrNull ungroupedPrefix))
                  =
                completeResolvedValue schema resolvers variableValues
                    (childDepth + 1) (.named parentType)
                    later.selectionSet (.object runtimeType identity)
                    (some (resultValueOrNull specPrefix)) := by
              rw [hvalue]
            have happend :
                ResponseValueResultAlignedEquivalent
                  (GraphQL.Execution.Result.combine mergeResponse
                    ungroupedPrefix
                    (completeResolvedValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      later.selectionSet (.object runtimeType identity)
                      (some (resultValueOrNull ungroupedPrefix))))
                  ungroupedExtended := by
              dsimp [ungroupedPrefix, ungroupedExtended]
              rw [hmergedAppend]
              exact
                completeValue_object_append_result_aligned_of_absorbs schema
                  resolvers variableValues childDepth parentType runtimeType
                  identity
                  (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                  later.selectionSet hincludes
                  (hobjects childDepth runtimeType identity
                    (Nat.lt_succ_self childDepth) ValueContainsObject.here)
            have htailAligned :
                ResponseValueResultAlignedEquivalent
                  (completeResolvedValue schema resolvers variableValues
                    (childDepth + 1) (.named parentType)
                    later.selectionSet (.object runtimeType identity)
                    (some (resultValueOrNull ungroupedPrefix)))
                  (completeResolvedValue schema resolvers variableValues
                    (childDepth + 1) (.named parentType)
                    later.selectionSet (.object runtimeType identity)
                    (some (resultValueOrNull specPrefix))) :=
              ResponseValueResultAlignedEquivalent.of_eq htail
            have hcombined :
                ResponseValueResultAlignedEquivalent
                  (GraphQL.Execution.Result.combine mergeResponse
                    ungroupedPrefix
                    (completeResolvedValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      later.selectionSet (.object runtimeType identity)
                      (some (resultValueOrNull ungroupedPrefix))))
                  (GraphQL.Execution.Result.combine mergeResponse
                    specPrefix
                    (completeResolvedValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      later.selectionSet (.object runtimeType identity)
                      (some (resultValueOrNull specPrefix)))) :=
              ResponseValueResultAlignedEquivalent.combine_mergeResponse
                hprefix htailAligned
            have hresult :
                ResponseValueResultAlignedEquivalent
                  (GraphQL.Execution.Result.combine mergeResponse
                    specPrefix
                    (completeResolvedValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      later.selectionSet (.object runtimeType identity)
                      (some (resultValueOrNull specPrefix))))
                  specExtended :=
              ResponseValueResultAlignedEquivalent.trans
                (ResponseValueResultAlignedEquivalent.symm hcombined)
                (ResponseValueResultAlignedEquivalent.trans happend hextended)
            simpa [specPrefix, specExtended] using hresult
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null,
              hnotIncludes, resultValueOrNull, GraphQL.Execution.Result.combine,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]

theorem completeValue_named_group_append_one_result_eq_spec_of_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet prefixFields
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later])
                  }
                initial := .object []
              })
    : GraphQL.Execution.Result.combine mergeResponse
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          (.named parentType) prefixFields resolved)
        (completeResolvedValue schema resolvers variableValues depth (.named parentType)
          later.selectionSet resolved
          (some
            (resultValueOrNull
              (GraphQL.Execution.completeValue schema resolvers variableValues depth
                (.named parentType) prefixFields resolved))))
      = GraphQL.Execution.completeValue schema resolvers variableValues depth
          (.named parentType) (prefixFields ++ [later]) resolved := by
  have hprefix :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
        none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved :=
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues prefixFields depth parentType resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        exact hprefixChildren childDepth runtimeType identity hlt hcontains
          (by simpa using hincludes))
  have hextended :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]))
        resolved none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) (prefixFields ++ [later]) resolved :=
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues (prefixFields ++ [later]) depth parentType resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        exact hchildren childDepth runtimeType identity hlt hcontains
          (by simpa using hincludes))
  have hmergedAppend :
      GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later]) =
        GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
          later.selectionSet := by
    simp [GraphQL.Execution.mergedFieldSelectionSet_append]
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, GraphQL.Execution.Result.combine]
  | succ childDepth =>
      cases resolved with
      | null =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse]
      | scalar value =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine, hcomposite]
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse, hcomposite]
      | list values =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · have hslice :
                GraphQL.Execution.Result.combine mergeResponse
                    (completeValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                      (.object runtimeType identity) none)
                  (completeResolvedValue schema resolvers variableValues
                    (childDepth + 1) (.named parentType)
                    later.selectionSet (.object runtimeType identity)
                      (some (resultValueOrNull
                        (completeValue schema resolvers variableValues
                          (childDepth + 1) (.named parentType)
                          (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                          (.object runtimeType identity) none)))) =
                completeValue schema resolvers variableValues (childDepth + 1)
                    (.named parentType)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (prefixFields ++ [later]))
                    (.object runtimeType identity) none := by
              calc
                GraphQL.Execution.Result.combine mergeResponse
                      (completeValue schema resolvers variableValues
                        (childDepth + 1) (.named parentType)
                        (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                        (.object runtimeType identity) none)
                    (completeResolvedValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      later.selectionSet (.object runtimeType identity)
                        (some (resultValueOrNull
                          (completeValue schema resolvers variableValues
                            (childDepth + 1) (.named parentType)
                            (GraphQL.Execution.mergedFieldSelectionSet
                              prefixFields)
                            (.object runtimeType identity) none)))) =
                  completeValue schema resolvers variableValues (childDepth + 1)
                      (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields ++
                        later.selectionSet)
                      (.object runtimeType identity) none := by
                    exact
                      completeValue_object_append_result_of_absorbs_errorNeutral
                        schema resolvers variableValues childDepth parentType
                        runtimeType identity
                        (GraphQL.Execution.mergedFieldSelectionSet
                          prefixFields)
                        later.selectionSet hincludes
                        (hobjects childDepth runtimeType identity
                          (Nat.lt_succ_self childDepth)
                          ValueContainsObject.here)
                        (herrors childDepth runtimeType identity
                          (Nat.lt_succ_self childDepth)
                          ValueContainsObject.here)
                _ =
                  completeValue schema resolvers variableValues
                      (childDepth + 1) (.named parentType)
                      (GraphQL.Execution.mergedFieldSelectionSet
                        (prefixFields ++ [later]))
                      (.object runtimeType identity) none := by
                    rw [hmergedAppend]
            rw [← hprefix]
            rw [← hextended]
            exact hslice
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hnotIncludes, resultValueOrNull, GraphQL.Execution.Result.combine]

theorem resultStatus_completeValue_named_group_append_second_eq_ok_of_contained
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet prefixFields
                  }
                initial := .object []
              })
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object [])))
    : resultStatus
        (completeResolvedValue schema resolvers variableValues depth (.named parentType)
          later.selectionSet resolved
          (some
            (resultValueOrNull
              (GraphQL.Execution.completeValue schema resolvers variableValues depth
                (.named parentType) prefixFields resolved))))
      = visitOk := by
  have hprefix :
      completeValue schema resolvers variableValues depth (.named parentType)
        (GraphQL.Execution.mergedFieldSelectionSet prefixFields) resolved
        none =
      GraphQL.Execution.completeValue schema resolvers variableValues depth
        (.named parentType) prefixFields resolved :=
    completeValue_group_eq_spec_of_contained_child_states schema resolvers
      variableValues prefixFields depth parentType resolved
      (by
        intro childDepth runtimeType identity hlt hcontains hincludes
        exact hprefixChildren childDepth runtimeType identity hlt hcontains
          (by simpa using hincludes))
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, resultStatus, visitOk]
  | succ childDepth =>
      cases resolved with
      | null =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
      | scalar value =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk, hcomposite]
          · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar, resultValueOrNull, resultStatus, visitOk, hcomposite]
      | list values =>
          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
      | object runtimeType identity =>
          by_cases hincludes :
              schema.typeIncludesObjectBool parentType runtimeType = true
          · have hrightLocal :=
              resultStatus_completeValue_object_append_second_of_errorNeutral
                schema resolvers variableValues childDepth parentType
                runtimeType identity
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                later.selectionSet hincludes
                (herrors childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth) ValueContainsObject.here)
            dsimp at hrightLocal
            rw [hprefix] at hrightLocal
            exact hrightLocal
          · have hnotIncludes :
                schema.typeIncludesObjectBool parentType runtimeType = false := by
              cases h : schema.typeIncludesObjectBool parentType runtimeType <;>
                simp [h] at hincludes ⊢
            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hnotIncludes, resultValueOrNull, resultStatus, visitOk]

theorem completeValueList_cons_previous
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (selectionSet : List Selection)
    (value : ResolverValue ObjectIdentity)
    (rest : List (ResolverValue ObjectIdentity))
    (previous : ResponseValue) (previousRest : List ResponseValue)
    : completeValueList schema resolvers variableValues depth itemType
        selectionSet (value :: rest) (previous :: previousRest)
      = Result.combine List.cons
          (match (some previous : Option ResponseValue) with
            | some .null => .ok (.null, 0)
            | _ =>
                completeValue schema resolvers variableValues depth itemType
                  selectionSet value (some previous))
          (completeValueList schema resolvers variableValues depth itemType
            selectionSet rest previousRest) := by
  rw [GraphQL.Algorithms.ExecutionUngrouped.Eager.completeValueList.eq_def]
  rfl

theorem completeValueList_head_eq_completeResolvedValue_of_composite
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (selectionSet : List Selection)
    (value : ResolverValue ObjectIdentity) (previous : ResponseValue)
    (hitemComposite : itemType.isCompositeBool schema = true)
    : (match (some previous : Option ResponseValue) with
        | some .null => .ok (.null, 0)
        | _ =>
            completeValue schema resolvers variableValues depth itemType
              selectionSet value (some previous))
      = completeResolvedValue schema resolvers variableValues depth itemType
          selectionSet value (some previous) := by
  induction itemType generalizing previous with
  | named typeName =>
      cases previous <;>
        unfold completeResolvedValue <;>
        simp [reusablePreviousValue?, hitemComposite]
  | list inner ih =>
      cases previous <;>
        unfold completeResolvedValue <;>
        simp [reusablePreviousValue?, hitemComposite]
  | nonNull inner ih =>
      have hinnerComposite : inner.isCompositeBool schema = true := by
        simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hitemComposite
      cases previous with
      | null =>
          unfold completeResolvedValue
          simp [reusablePreviousValue?]
      | scalar previousValue =>
          cases depth with
          | zero =>
              have hinner :=
                ih (ResponseValue.scalar previousValue) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, outOfFuel,
                nonNullCompletion, ← hinner]
          | succ childDepth =>
              have hinner :=
                ih (ResponseValue.scalar previousValue) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, nonNullCompletion, ← hinner]
      | object fields =>
          cases depth with
          | zero =>
              have hinner := ih (ResponseValue.object fields) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, outOfFuel,
                nonNullCompletion, ← hinner]
          | succ childDepth =>
              have hinner := ih (ResponseValue.object fields) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, nonNullCompletion, ← hinner]
      | list values =>
          cases depth with
          | zero =>
              have hinner := ih (ResponseValue.list values) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, outOfFuel,
                nonNullCompletion, ← hinner]
          | succ childDepth =>
              have hinner := ih (ResponseValue.list values) hinnerComposite
              simp [completeResolvedValue, reusablePreviousValue?,
                hitemComposite, completeValue, nonNullCompletion, ← hinner]

theorem resultStatus_completeValueList_append_second_eq_ok_of_each
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    (hitemComposite : itemType.isCompositeBool schema = true)
    (hstatus
      : ∀ value : ResolverValue ObjectIdentity,
          resultStatus
            (completeResolvedValue schema resolvers variableValues depth itemType
              later.selectionSet value
              (some
                (resultValueOrNull
                  (GraphQL.Execution.completeValue schema resolvers variableValues
                    depth itemType prefixFields value))))
          = visitOk)
    : ∀ values : List (ResolverValue ObjectIdentity),
        match GraphQL.Execution.completeValueList schema resolvers variableValues
                depth itemType prefixFields values with
        | .error _errors => True
        | .ok (previousValues, _errors) =>
            resultStatus
              (completeValueList schema resolvers variableValues depth itemType
                later.selectionSet values previousValues)
            = visitOk := by
  intro values
  induction values with
  | nil =>
      simp [GraphQL.Execution.completeValueList, completeValueList,
        resultStatus, visitOk]
  | cons value rest ih =>
      cases hhead :
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
      | ok headResult =>
          rcases headResult with ⟨headValue, headErrors⟩
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              have hheadStatus :
                  resultStatus
                    (completeResolvedValue schema resolvers variableValues depth
                      itemType later.selectionSet value (some headValue)) =
                  visitOk := by
                simpa [hhead, resultValueOrNull] using hstatus value
              have htailStatus : resultStatus
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) =
                  visitOk := by
                simpa [htail] using ih
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          simp [hrightTail, resultStatus, visitOk] at htailStatus
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              have hrightHeadList :
                                  (match (some headValue : Option ResponseValue) with
                                  | some .null =>
                                      Except.ok (ResponseValue.null, 0)
                                  | _ =>
                                      completeValue schema resolvers
                                        variableValues depth itemType
                                        later.selectionSet value
                                        (some headValue)) =
                                    .ok (rightHeadValue, 0) := by
                                rw [
                                  completeValueList_head_eq_completeResolvedValue_of_composite
                                    schema resolvers variableValues depth
                                    itemType later.selectionSet value
                                    headValue hitemComposite]
                                exact hrightHead
                              have hstatusList :
                                  resultStatus
                                    (Result.combine List.cons
                                      (match
                                        (some headValue : Option ResponseValue)
                                      with
                                      | some .null =>
                                          Except.ok (ResponseValue.null, 0)
                                      | _ =>
                                          completeValue schema resolvers
                                            variableValues depth itemType
                                            later.selectionSet value
                                            (some headValue))
                                      (Except.ok (rightTailValues, 0))) =
                                    visitOk := by
                                rw [hrightHeadList]
                                simp [Result.combine,
                                  GraphQL.Execution.Result.combine,
                                  resultStatus, visitOk]
                              rw [GraphQL.Execution.completeValueList, hhead,
                                htail]
                              simp [GraphQL.Execution.Result.combine]
                              rw [completeValueList_cons_previous, hrightTail]
                              exact hstatusList
                          | succ rightTailErrors =>
                              simp [hrightTail, resultStatus, visitOk] at htailStatus
                  | succ rightHeadErrors =>
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus

theorem resultStatus_completeValueList_append_second_eq_ok_of_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    : ∀ values : List (ResolverValue ObjectIdentity),
        itemType.isCompositeBool schema = true
        -> (∀ value,
              value ∈ values
              -> resultStatus
                    (completeResolvedValue schema resolvers variableValues depth
                      itemType later.selectionSet value
                      (some
                        (resultValueOrNull
                          (GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType prefixFields value))))
                  = visitOk)
        -> match GraphQL.Execution.completeValueList schema resolvers variableValues
                  depth itemType prefixFields values with
            | .error _errors => True
            | .ok (previousValues, _errors) =>
                resultStatus
                  (completeValueList schema resolvers variableValues depth itemType
                    later.selectionSet values previousValues)
                = visitOk
  | [], _hitemComposite, _hstatus => by
      simp [GraphQL.Execution.completeValueList, completeValueList,
        resultStatus, visitOk]
  | value :: rest, hitemComposite, hstatus => by
      cases hhead :
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
      | ok headResult =>
          rcases headResult with ⟨headValue, headErrors⟩
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              simp [GraphQL.Execution.completeValueList, hhead, htail,
                GraphQL.Execution.Result.combine]
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              have hheadStatus :
                  resultStatus
                    (completeResolvedValue schema resolvers variableValues depth
                      itemType later.selectionSet value (some headValue)) =
                  visitOk := by
                simpa [hhead, resultValueOrNull] using
                  hstatus value (by simp)
              have htailStatus : resultStatus
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) =
                  visitOk := by
                have htailStatusRaw :=
                  resultStatus_completeValueList_append_second_eq_ok_of_mem
                    schema resolvers variableValues depth itemType prefixFields
                    later rest hitemComposite
                    (by
                      intro restValue hmem
                      exact hstatus restValue (by simp [hmem]))
                simpa [htail] using htailStatusRaw
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          simp [hrightTail, resultStatus, visitOk] at htailStatus
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              have hrightHeadList :
                                  (match (some headValue : Option ResponseValue) with
                                  | some .null =>
                                      Except.ok (ResponseValue.null, 0)
                                  | _ =>
                                      completeValue schema resolvers
                                        variableValues depth itemType
                                        later.selectionSet value
                                        (some headValue)) =
                                    .ok (rightHeadValue, 0) := by
                                rw [
                                  completeValueList_head_eq_completeResolvedValue_of_composite
                                    schema resolvers variableValues depth
                                    itemType later.selectionSet value
                                    headValue hitemComposite]
                                exact hrightHead
                              have hstatusList :
                                  resultStatus
                                    (Result.combine List.cons
                                      (match
                                        (some headValue : Option ResponseValue)
                                      with
                                      | some .null =>
                                          Except.ok (ResponseValue.null, 0)
                                      | _ =>
                                          completeValue schema resolvers
                                            variableValues depth itemType
                                            later.selectionSet value
                                            (some headValue))
                                      (Except.ok (rightTailValues, 0))) =
                                    visitOk := by
                                rw [hrightHeadList]
                                simp [Result.combine,
                                  GraphQL.Execution.Result.combine,
                                  resultStatus, visitOk]
                              rw [GraphQL.Execution.completeValueList, hhead,
                                htail]
                              simp [GraphQL.Execution.Result.combine]
                              rw [completeValueList_cons_previous, hrightTail]
                              exact hstatusList
                          | succ rightTailErrors =>
                              simp [hrightTail, resultStatus, visitOk] at htailStatus
                  | succ rightHeadErrors =>
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus

theorem completeValueList_append_result_aligned_of_each
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    (hitemComposite : itemType.isCompositeBool schema = true)
    (happend
      : ∀ value : ResolverValue ObjectIdentity,
          ResponseValueResultAlignedEquivalent
            (GraphQL.Execution.Result.combine mergeResponse
              (GraphQL.Execution.completeValue schema resolvers variableValues
                depth itemType prefixFields value)
              (completeResolvedValue schema resolvers variableValues depth itemType
                later.selectionSet value
                (some
                  (resultValueOrNull
                    (GraphQL.Execution.completeValue schema resolvers variableValues
                      depth itemType prefixFields value)))))
            (GraphQL.Execution.completeValue schema resolvers variableValues
              depth itemType (prefixFields ++ [later]) value))
    : ∀ values : List (ResolverValue ObjectIdentity),
        ListResponseResultAlignedEquivalent
          (GraphQL.Execution.Result.combine mergeResponseLists
            (GraphQL.Execution.completeValueList schema resolvers variableValues
              depth itemType prefixFields values)
            (match GraphQL.Execution.completeValueList schema resolvers variableValues
                    depth itemType prefixFields values with
              | .error _errors => .ok ([], 0)
              | .ok (previousValues, _errors) =>
                  completeValueList schema resolvers variableValues depth itemType
                    later.selectionSet values previousValues))
          (GraphQL.Execution.completeValueList schema resolvers variableValues
            depth itemType (prefixFields ++ [later]) values)
  | [] => by
      simp [GraphQL.Execution.completeValueList, completeValueList,
        GraphQL.Execution.Result.combine, mergeResponseLists,
        ListResponseResultAlignedEquivalent, ErrorPresenceEquivalent]
  | value :: rest => by
      have hheadAppend := happend value
      have htailAppend :=
        completeValueList_append_result_aligned_of_each schema resolvers
          variableValues depth itemType prefixFields later hitemComposite
          happend rest
      cases hhead :
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value with
      | error headErrors =>
          have hheadPos :=
            specCompleteValue_error_positive schema resolvers variableValues
              depth itemType prefixFields value headErrors hhead
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              cases happHead :
                  GraphQL.Execution.completeValue schema resolvers
                    variableValues depth itemType (prefixFields ++ [later])
                    value with
              | error appHeadErrors =>
                  have happHeadPos :=
                    specCompleteValue_error_positive schema resolvers
                      variableValues depth itemType (prefixFields ++ [later])
                      value appHeadErrors happHead
                  cases happTail :
                      GraphQL.Execution.completeValueList schema resolvers
                        variableValues depth itemType
                        (prefixFields ++ [later]) rest <;>
                    simp [GraphQL.Execution.completeValueList, hhead, htail,
                      happHead, happTail, GraphQL.Execution.Result.combine,
                      ListResponseResultAlignedEquivalent,
                      ErrorPresenceEquivalent] <;> omega
              | ok appHeadResult =>
                  cases hright :
                      completeResolvedValue schema resolvers variableValues
                        depth itemType later.selectionSet value
                        (some .null) <;>
                    simp [hhead, hright, happHead, resultValueOrNull,
                      GraphQL.Execution.Result.combine,
                      ResponseValueResultAlignedEquivalent] at hheadAppend
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              cases happHead :
                  GraphQL.Execution.completeValue schema resolvers
                    variableValues depth itemType (prefixFields ++ [later])
                    value with
              | error appHeadErrors =>
                  have happHeadPos :=
                    specCompleteValue_error_positive schema resolvers
                      variableValues depth itemType (prefixFields ++ [later])
                      value appHeadErrors happHead
                  cases happTail :
                      GraphQL.Execution.completeValueList schema resolvers
                        variableValues depth itemType
                        (prefixFields ++ [later]) rest <;>
                    simp [GraphQL.Execution.completeValueList, hhead, htail,
                      happHead, happTail, GraphQL.Execution.Result.combine,
                      ListResponseResultAlignedEquivalent,
                      ErrorPresenceEquivalent] <;> omega
              | ok appHeadResult =>
                  cases hright :
                      completeResolvedValue schema resolvers variableValues
                        depth itemType later.selectionSet value
                        (some .null) <;>
                    simp [hhead, hright, happHead, resultValueOrNull,
                      GraphQL.Execution.Result.combine,
                      ResponseValueResultAlignedEquivalent] at hheadAppend
      | ok headResult =>
          rcases headResult with ⟨headValue, headErrors⟩
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              have htailPos :=
                specCompleteValueList_error_positive schema resolvers
                  variableValues depth itemType prefixFields rest tailErrors
                  htail
              cases happTail :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth itemType (prefixFields ++ [later])
                    rest with
              | error appTailErrors =>
                  have happTailPos :=
                    specCompleteValueList_error_positive schema resolvers
                      variableValues depth itemType (prefixFields ++ [later])
                      rest appTailErrors happTail
                  cases happHead :
                      GraphQL.Execution.completeValue schema resolvers
                        variableValues depth itemType
                        (prefixFields ++ [later]) value <;>
                    simp [GraphQL.Execution.completeValueList, hhead, htail,
                      happHead, happTail, GraphQL.Execution.Result.combine,
                      ListResponseResultAlignedEquivalent,
                      ErrorPresenceEquivalent] <;> omega
              | ok appTailResult =>
                  simp [htail, happTail, GraphQL.Execution.Result.combine,
                    ListResponseResultAlignedEquivalent] at htailAppend
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              have hrightHead :
                  (match (some headValue : Option ResponseValue) with
                  | some .null => .ok (.null, 0)
                  | _ =>
                      completeValue schema resolvers variableValues depth
                        itemType later.selectionSet value (some headValue)) =
                    completeResolvedValue schema resolvers variableValues depth
                      itemType later.selectionSet value (some headValue) := by
                exact
                  completeValueList_head_eq_completeResolvedValue_of_composite
                    schema resolvers variableValues depth itemType
                    later.selectionSet value headValue hitemComposite
              rw [GraphQL.Execution.completeValueList, hhead, htail]
              simp [GraphQL.Execution.Result.combine]
              rw [completeValueList_cons_previous]
              simpa [GraphQL.Execution.completeValueList, ← hrightHead,
                hhead, htail, resultValueOrNull,
                GraphQL.Execution.Result.combine,
                Result.combine] using
                ListResponseResultAlignedEquivalent.zip_cons hheadAppend
                  htailAppend

theorem completeValueList_append_result_aligned_of_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    : ∀ values : List (ResolverValue ObjectIdentity),
        itemType.isCompositeBool schema = true
        -> (∀ value,
              value ∈ values
              -> ResponseValueResultAlignedEquivalent
                  (GraphQL.Execution.Result.combine mergeResponse
                    (GraphQL.Execution.completeValue schema resolvers variableValues
                      depth itemType prefixFields value)
                    (completeResolvedValue schema resolvers variableValues depth
                      itemType later.selectionSet value
                      (some
                        (resultValueOrNull
                          (GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType prefixFields value)))))
                  (GraphQL.Execution.completeValue schema resolvers variableValues
                    depth itemType (prefixFields ++ [later]) value))
        -> ListResponseResultAlignedEquivalent
            (GraphQL.Execution.Result.combine mergeResponseLists
              (GraphQL.Execution.completeValueList schema resolvers variableValues
                depth itemType prefixFields values)
              (match GraphQL.Execution.completeValueList schema resolvers variableValues
                      depth itemType prefixFields values with
                | .error _errors => .ok ([], 0)
                | .ok (previousValues, _errors) =>
                    completeValueList schema resolvers variableValues depth itemType
                      later.selectionSet values previousValues))
            (GraphQL.Execution.completeValueList schema resolvers variableValues
              depth itemType (prefixFields ++ [later]) values)
  | [], _hitemComposite, _happend => by
      simp [GraphQL.Execution.completeValueList, completeValueList,
        GraphQL.Execution.Result.combine, mergeResponseLists,
        ListResponseResultAlignedEquivalent, ErrorPresenceEquivalent]
  | value :: rest, hitemComposite, happend => by
      have hheadAppend := happend value (by simp)
      have htailAppend :=
        completeValueList_append_result_aligned_of_mem schema resolvers
          variableValues depth itemType prefixFields later rest hitemComposite
          (by
            intro restValue hmem
            exact happend restValue (by simp [hmem]))
      cases hhead :
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value with
      | error headErrors =>
          have hheadPos :=
            specCompleteValue_error_positive schema resolvers variableValues
              depth itemType prefixFields value headErrors hhead
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              cases happHead :
                  GraphQL.Execution.completeValue schema resolvers
                    variableValues depth itemType (prefixFields ++ [later])
                    value with
              | error appHeadErrors =>
                  have happHeadPos :=
                    specCompleteValue_error_positive schema resolvers
                      variableValues depth itemType (prefixFields ++ [later])
                      value appHeadErrors happHead
                  cases happTail :
                      GraphQL.Execution.completeValueList schema resolvers
                        variableValues depth itemType
                        (prefixFields ++ [later]) rest <;>
                    simp [GraphQL.Execution.completeValueList, hhead, htail,
                      happHead, happTail, GraphQL.Execution.Result.combine,
                      ListResponseResultAlignedEquivalent,
                      ErrorPresenceEquivalent] <;> omega
              | ok appHeadResult =>
                  cases hright :
                      completeResolvedValue schema resolvers variableValues
                        depth itemType later.selectionSet value
                        (some .null) <;>
                    simp [hhead, hright, happHead, resultValueOrNull,
                      GraphQL.Execution.Result.combine,
                      ResponseValueResultAlignedEquivalent] at hheadAppend
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              cases happHead :
                  GraphQL.Execution.completeValue schema resolvers
                    variableValues depth itemType (prefixFields ++ [later])
                    value with
              | error appHeadErrors =>
                  have happHeadPos :=
                    specCompleteValue_error_positive schema resolvers
                      variableValues depth itemType (prefixFields ++ [later])
                      value appHeadErrors happHead
                  cases happTail :
                      GraphQL.Execution.completeValueList schema resolvers
                        variableValues depth itemType
                        (prefixFields ++ [later]) rest <;>
                    simp [GraphQL.Execution.completeValueList, hhead, htail,
                      happHead, happTail, GraphQL.Execution.Result.combine,
                      ListResponseResultAlignedEquivalent,
                      ErrorPresenceEquivalent] <;> omega
              | ok appHeadResult =>
                  cases hright :
                      completeResolvedValue schema resolvers variableValues
                        depth itemType later.selectionSet value
                        (some .null) <;>
                    simp [hhead, hright, happHead, resultValueOrNull,
                      GraphQL.Execution.Result.combine,
                      ResponseValueResultAlignedEquivalent] at hheadAppend
      | ok headResult =>
          rcases headResult with ⟨headValue, headErrors⟩
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              have htailPos :=
                specCompleteValueList_error_positive schema resolvers
                  variableValues depth itemType prefixFields rest tailErrors
                  htail
              cases happTail :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth itemType (prefixFields ++ [later])
                    rest with
              | error appTailErrors =>
                  have happTailPos :=
                    specCompleteValueList_error_positive schema resolvers
                      variableValues depth itemType (prefixFields ++ [later])
                      rest appTailErrors happTail
                  cases happHead :
                      GraphQL.Execution.completeValue schema resolvers
                        variableValues depth itemType
                        (prefixFields ++ [later]) value <;>
                    simp [GraphQL.Execution.completeValueList, hhead, htail,
                      happHead, happTail, GraphQL.Execution.Result.combine,
                      ListResponseResultAlignedEquivalent,
                      ErrorPresenceEquivalent] <;> omega
              | ok appTailResult =>
                  simp [htail, happTail, GraphQL.Execution.Result.combine,
                    ListResponseResultAlignedEquivalent] at htailAppend
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              have hrightHead :
                  (match (some headValue : Option ResponseValue) with
                  | some .null => .ok (.null, 0)
                  | _ =>
                      completeValue schema resolvers variableValues depth
                        itemType later.selectionSet value (some headValue)) =
                    completeResolvedValue schema resolvers variableValues depth
                      itemType later.selectionSet value (some headValue) := by
                exact
                  completeValueList_head_eq_completeResolvedValue_of_composite
                    schema resolvers variableValues depth itemType
                    later.selectionSet value headValue hitemComposite
              rw [GraphQL.Execution.completeValueList, hhead, htail]
              simp [GraphQL.Execution.Result.combine]
              rw [completeValueList_cons_previous]
              simpa [GraphQL.Execution.completeValueList, ← hrightHead,
                hhead, htail, resultValueOrNull,
                GraphQL.Execution.Result.combine,
                Result.combine] using
                ListResponseResultAlignedEquivalent.zip_cons hheadAppend
                  htailAppend

theorem completeValueList_append_result_eq_spec_of_each
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    (hitemComposite : itemType.isCompositeBool schema = true)
    (happend
      : ∀ value : ResolverValue ObjectIdentity,
          GraphQL.Execution.Result.combine mergeResponse
            (GraphQL.Execution.completeValue schema resolvers variableValues
              depth itemType prefixFields value)
            (completeResolvedValue schema resolvers variableValues depth itemType
              later.selectionSet value
              (some
                (resultValueOrNull
                  (GraphQL.Execution.completeValue schema resolvers variableValues
                    depth itemType prefixFields value))))
          = GraphQL.Execution.completeValue schema resolvers variableValues
              depth itemType (prefixFields ++ [later]) value)
    (hstatus
      : ∀ value : ResolverValue ObjectIdentity,
          resultStatus
            (completeResolvedValue schema resolvers variableValues depth itemType
              later.selectionSet value
              (some
                (resultValueOrNull
                  (GraphQL.Execution.completeValue schema resolvers variableValues
                    depth itemType prefixFields value))))
          = visitOk)
    : ∀ values : List (ResolverValue ObjectIdentity),
        GraphQL.Execution.Result.combine mergeResponseLists
          (GraphQL.Execution.completeValueList schema resolvers variableValues
            depth itemType prefixFields values)
          (match GraphQL.Execution.completeValueList schema resolvers variableValues
                  depth itemType prefixFields values with
            | .error _errors => .ok ([], 0)
            | .ok (previousValues, _errors) =>
                completeValueList schema resolvers variableValues depth itemType
                  later.selectionSet values previousValues)
        = GraphQL.Execution.completeValueList schema resolvers variableValues
            depth itemType (prefixFields ++ [later]) values := by
  intro values
  induction values with
  | nil =>
      simp [GraphQL.Execution.completeValueList, completeValueList,
        GraphQL.Execution.Result.combine, mergeResponseLists]
  | cons value rest ih =>
      have hheadAppend := happend value
      have hheadStatus :
          resultStatus
            (completeResolvedValue schema resolvers variableValues depth itemType
              later.selectionSet value
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth itemType prefixFields value)))) =
          visitOk :=
        hstatus value
      have hrestStatus :=
        resultStatus_completeValueList_append_second_eq_ok_of_each schema
          resolvers variableValues depth itemType prefixFields later
          hitemComposite hstatus rest
      cases hhead :
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some .null) with
              | error rightHeadErrors =>
                  simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                    visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .error headErrors := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      have htailAppend' :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) rest =
                          .error tailErrors := by
                        simpa [htail, GraphQL.Execution.Result.combine] using
                          ih.symm
                      simp [GraphQL.Execution.completeValueList, hhead, htail,
                        hheadAppend', htailAppend', Result.combine,
                        GraphQL.Execution.Result.combine]
                  | succ rightHeadErrors =>
                      simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                        visitOk] at hheadStatus
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some .null) with
              | error rightHeadErrors =>
                  simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                    visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .error headErrors := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      have htailAppend' :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) rest =
                          GraphQL.Execution.Result.combine mergeResponseLists
                            (.ok (tailValues, tailErrors))
                            (completeValueList schema resolvers variableValues
                              depth itemType later.selectionSet rest tailValues) := by
                        simpa [htail] using ih.symm
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          have htailStatus' :
                              resultStatus
                                (completeValueList schema resolvers
                                  variableValues depth itemType
                                  later.selectionSet rest tailValues) =
                              visitOk := by
                            simpa [htail] using hrestStatus
                          simp [hrightTail, resultStatus, visitOk] at htailStatus'
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              simp [GraphQL.Execution.completeValueList, hhead,
                                htail, hheadAppend', htailAppend',
                                hrightTail, Result.combine,
                                GraphQL.Execution.Result.combine]
                          | succ rightTailErrors =>
                              have htailStatus' :
                                  resultStatus
                                    (completeValueList schema resolvers
                                      variableValues depth itemType
                                      later.selectionSet rest tailValues) =
                                  visitOk := by
                                simpa [htail] using hrestStatus
                              simp [hrightTail, resultStatus, visitOk] at htailStatus'
                  | succ rightHeadErrors =>
                      simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                        visitOk] at hheadStatus
      | ok headResult =>
          rcases headResult with ⟨headValue, headErrors⟩
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              have htailAppend' :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth itemType
                    (prefixFields ++ [later]) rest =
                  .error tailErrors := by
                simpa [htail, GraphQL.Execution.Result.combine] using ih.symm
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  have hheadStatus' :
                      resultStatus
                        (completeResolvedValue schema resolvers variableValues depth
                          itemType later.selectionSet value (some headValue)) =
                      visitOk := by
                    simpa [hhead, resultValueOrNull] using hheadStatus
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus'
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .ok (mergeResponse headValue rightHeadValue,
                            headErrors) := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      simp [GraphQL.Execution.completeValueList, hhead, htail,
                        hheadAppend', htailAppend', Result.combine,
                        GraphQL.Execution.Result.combine]
                  | succ rightHeadErrors =>
                      have hheadStatus' :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues depth
                              itemType later.selectionSet value (some headValue)) =
                          visitOk := by
                        simpa [hhead, resultValueOrNull] using hheadStatus
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus'
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              have htailStatus' :
                  resultStatus
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) =
                  visitOk := by
                simpa [htail] using hrestStatus
              have htailAppend' :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth itemType
                    (prefixFields ++ [later]) rest =
                  GraphQL.Execution.Result.combine mergeResponseLists
                    (.ok (tailValues, tailErrors))
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) := by
                simpa [htail] using ih.symm
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  have hheadStatus' :
                      resultStatus
                        (completeResolvedValue schema resolvers variableValues depth
                          itemType later.selectionSet value (some headValue)) =
                      visitOk := by
                    simpa [hhead, resultValueOrNull] using hheadStatus
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus'
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .ok (mergeResponse headValue rightHeadValue,
                            headErrors) := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          simp [hrightTail, resultStatus, visitOk] at htailStatus'
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              have hrightHeadList :
                                  (match (some headValue : Option ResponseValue) with
                                  | some .null =>
                                      Except.ok (ResponseValue.null, 0)
                                  | _ =>
                                      completeValue schema resolvers
                                        variableValues depth itemType
                                        later.selectionSet value
                                        (some headValue)) =
                                    Except.ok (rightHeadValue, 0) := by
                                rw [
                                  completeValueList_head_eq_completeResolvedValue_of_composite
                                    schema resolvers variableValues depth
                                    itemType later.selectionSet value
                                    headValue hitemComposite]
                                exact hrightHead
                              have hcombinedList :
                                  GraphQL.Execution.Result.combine
                                      mergeResponseLists
                                      (Except.ok
                                        (headValue :: tailValues,
                                          headErrors + tailErrors))
                                      (Result.combine List.cons
                                        (match
                                          (some headValue : Option ResponseValue)
                                        with
                                        | some .null =>
                                            Except.ok (ResponseValue.null, 0)
                                        | _ =>
                                            completeValue schema resolvers
                                              variableValues depth itemType
                                              later.selectionSet value
                                              (some headValue))
                                        (Except.ok (rightTailValues, 0))) =
                                    Except.ok
                                      (mergeResponse headValue rightHeadValue ::
                                        mergeResponseLists tailValues
                                          rightTailValues,
                                        headErrors + tailErrors) := by
                                rw [hrightHeadList]
                                simp [Result.combine,
                                  GraphQL.Execution.Result.combine,
                                  mergeResponseLists]
                              rw [GraphQL.Execution.completeValueList, hhead,
                                htail]
                              simp [GraphQL.Execution.Result.combine]
                              rw [completeValueList_cons_previous, hrightTail]
                              rw [GraphQL.Execution.completeValueList,
                                hheadAppend', htailAppend', hrightTail]
                              simpa [GraphQL.Execution.Result.combine,
                                Result.combine] using hcombinedList
                          | succ rightTailErrors =>
                              simp [hrightTail, resultStatus, visitOk] at htailStatus'
                  | succ rightHeadErrors =>
                      have hheadStatus' :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues depth
                              itemType later.selectionSet value (some headValue)) =
                          visitOk := by
                        simpa [hhead, resultValueOrNull] using hheadStatus
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus'

theorem completeValueList_append_result_eq_spec_of_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (itemType : TypeRef) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    : ∀ values : List (ResolverValue ObjectIdentity),
        itemType.isCompositeBool schema = true
        -> (∀ value,
              value ∈ values
              -> GraphQL.Execution.Result.combine mergeResponse
                    (GraphQL.Execution.completeValue schema resolvers variableValues
                      depth itemType prefixFields value)
                    (completeResolvedValue schema resolvers variableValues depth
                      itemType later.selectionSet value
                      (some
                        (resultValueOrNull
                          (GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType prefixFields value))))
                  = GraphQL.Execution.completeValue schema resolvers variableValues
                      depth itemType (prefixFields ++ [later]) value)
        -> (∀ value,
              value ∈ values
              -> resultStatus
                    (completeResolvedValue schema resolvers variableValues depth
                      itemType later.selectionSet value
                      (some
                        (resultValueOrNull
                          (GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType prefixFields value))))
                  = visitOk)
        -> GraphQL.Execution.Result.combine mergeResponseLists
              (GraphQL.Execution.completeValueList schema resolvers variableValues
                depth itemType prefixFields values)
              (match GraphQL.Execution.completeValueList schema resolvers variableValues
                      depth itemType prefixFields values with
                | .error _errors => .ok ([], 0)
                | .ok (previousValues, _errors) =>
                    completeValueList schema resolvers variableValues depth itemType
                      later.selectionSet values previousValues)
            = GraphQL.Execution.completeValueList schema resolvers variableValues
                depth itemType (prefixFields ++ [later]) values
  | [], _hitemComposite, _happend, _hstatus => by
      simp [GraphQL.Execution.completeValueList, completeValueList,
        GraphQL.Execution.Result.combine, mergeResponseLists]
  | value :: rest, hitemComposite, happend, hstatus => by
      have hheadAppend := happend value (by simp)
      have hheadStatus :
          resultStatus
            (completeResolvedValue schema resolvers variableValues depth itemType
              later.selectionSet value
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth itemType prefixFields value)))) =
          visitOk :=
        hstatus value (by simp)
      have htailAppendAll :=
        completeValueList_append_result_eq_spec_of_mem schema resolvers
          variableValues depth itemType prefixFields later rest
          hitemComposite
          (by
            intro restValue hmem
            exact happend restValue (by simp [hmem]))
          (by
            intro restValue hmem
            exact hstatus restValue (by simp [hmem]))
      have hrestStatus :=
        resultStatus_completeValueList_append_second_eq_ok_of_mem schema
          resolvers variableValues depth itemType prefixFields later rest
          hitemComposite
          (by
            intro restValue hmem
            exact hstatus restValue (by simp [hmem]))
      cases hhead :
          GraphQL.Execution.completeValue schema resolvers variableValues
            depth itemType prefixFields value with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some .null) with
              | error rightHeadErrors =>
                  simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                    visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .error headErrors := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      have htailAppend' :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) rest =
                          .error tailErrors := by
                        simpa [htail, GraphQL.Execution.Result.combine] using
                          htailAppendAll.symm
                      simp [GraphQL.Execution.completeValueList, hhead, htail,
                        hheadAppend', htailAppend', Result.combine,
                        GraphQL.Execution.Result.combine]
                  | succ rightHeadErrors =>
                      simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                        visitOk] at hheadStatus
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some .null) with
              | error rightHeadErrors =>
                  simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                    visitOk] at hheadStatus
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .error headErrors := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      have htailAppend' :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) rest =
                          GraphQL.Execution.Result.combine mergeResponseLists
                            (.ok (tailValues, tailErrors))
                            (completeValueList schema resolvers variableValues
                              depth itemType later.selectionSet rest tailValues) := by
                        simpa [htail] using htailAppendAll.symm
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          have htailStatus' :
                              resultStatus
                                (completeValueList schema resolvers
                                  variableValues depth itemType
                                  later.selectionSet rest tailValues) =
                              visitOk := by
                            simpa [htail] using hrestStatus
                          simp [hrightTail, resultStatus, visitOk] at htailStatus'
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              simp [GraphQL.Execution.completeValueList, hhead,
                                htail, hheadAppend', htailAppend',
                                hrightTail, Result.combine,
                                GraphQL.Execution.Result.combine]
                          | succ rightTailErrors =>
                              have htailStatus' :
                                  resultStatus
                                    (completeValueList schema resolvers
                                      variableValues depth itemType
                                      later.selectionSet rest tailValues) =
                                  visitOk := by
                                simpa [htail] using hrestStatus
                              simp [hrightTail, resultStatus, visitOk] at htailStatus'
                  | succ rightHeadErrors =>
                      simp [hhead, hrightHead, resultValueOrNull, resultStatus,
                        visitOk] at hheadStatus
      | ok headResult =>
          rcases headResult with ⟨headValue, headErrors⟩
          cases htail :
              GraphQL.Execution.completeValueList schema resolvers
                variableValues depth itemType prefixFields rest with
          | error tailErrors =>
              have htailAppend' :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth itemType
                    (prefixFields ++ [later]) rest =
                  .error tailErrors := by
                simpa [htail, GraphQL.Execution.Result.combine] using
                  htailAppendAll.symm
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  have hheadStatus' :
                      resultStatus
                        (completeResolvedValue schema resolvers variableValues depth
                          itemType later.selectionSet value (some headValue)) =
                      visitOk := by
                    simpa [hhead, resultValueOrNull] using hheadStatus
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus'
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .ok (mergeResponse headValue rightHeadValue,
                            headErrors) := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      simp [GraphQL.Execution.completeValueList, hhead, htail,
                        hheadAppend', htailAppend', Result.combine,
                        GraphQL.Execution.Result.combine]
                  | succ rightHeadErrors =>
                      have hheadStatus' :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues depth
                              itemType later.selectionSet value (some headValue)) =
                          visitOk := by
                        simpa [hhead, resultValueOrNull] using hheadStatus
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus'
          | ok tailResult =>
              rcases tailResult with ⟨tailValues, tailErrors⟩
              have htailStatus' :
                  resultStatus
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) =
                  visitOk := by
                simpa [htail] using hrestStatus
              have htailAppend' :
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues depth itemType
                    (prefixFields ++ [later]) rest =
                  GraphQL.Execution.Result.combine mergeResponseLists
                    (.ok (tailValues, tailErrors))
                    (completeValueList schema resolvers variableValues depth
                      itemType later.selectionSet rest tailValues) := by
                simpa [htail] using htailAppendAll.symm
              cases hrightHead :
                  completeResolvedValue schema resolvers variableValues depth itemType
                    later.selectionSet value (some headValue) with
              | error rightHeadErrors =>
                  have hheadStatus' :
                      resultStatus
                        (completeResolvedValue schema resolvers variableValues depth
                          itemType later.selectionSet value (some headValue)) =
                      visitOk := by
                    simpa [hhead, resultValueOrNull] using hheadStatus
                  simp [hrightHead, resultStatus, visitOk] at hheadStatus'
              | ok rightHeadResult =>
                  rcases rightHeadResult with ⟨rightHeadValue, rightHeadErrors⟩
                  cases rightHeadErrors with
                  | zero =>
                      have hheadAppend' :
                          GraphQL.Execution.completeValue schema resolvers
                            variableValues depth itemType
                            (prefixFields ++ [later]) value =
                          .ok (mergeResponse headValue rightHeadValue,
                            headErrors) := by
                        simpa [hhead, hrightHead, resultValueOrNull,
                          GraphQL.Execution.Result.combine] using hheadAppend.symm
                      cases hrightTail :
                          completeValueList schema resolvers variableValues
                            depth itemType later.selectionSet rest tailValues with
                      | error rightTailErrors =>
                          simp [hrightTail, resultStatus, visitOk] at htailStatus'
                      | ok rightTailResult =>
                          rcases rightTailResult with
                            ⟨rightTailValues, rightTailErrors⟩
                          cases rightTailErrors with
                          | zero =>
                              have hrightHeadList :
                                  (match (some headValue : Option ResponseValue) with
                                  | some .null =>
                                      Except.ok (ResponseValue.null, 0)
                                  | _ =>
                                      completeValue schema resolvers
                                        variableValues depth itemType
                                        later.selectionSet value
                                        (some headValue)) =
                                    Except.ok (rightHeadValue, 0) := by
                                rw [
                                  completeValueList_head_eq_completeResolvedValue_of_composite
                                    schema resolvers variableValues depth
                                    itemType later.selectionSet value
                                    headValue hitemComposite]
                                exact hrightHead
                              have hcombinedList :
                                  GraphQL.Execution.Result.combine
                                      mergeResponseLists
                                      (Except.ok
                                        (headValue :: tailValues,
                                          headErrors + tailErrors))
                                      (Result.combine List.cons
                                        (match
                                          (some headValue : Option ResponseValue)
                                        with
                                        | some .null =>
                                            Except.ok (ResponseValue.null, 0)
                                        | _ =>
                                            completeValue schema resolvers
                                              variableValues depth itemType
                                              later.selectionSet value
                                              (some headValue))
                                        (Except.ok (rightTailValues, 0))) =
                                    Except.ok
                                      (mergeResponse headValue rightHeadValue ::
                                        mergeResponseLists tailValues
                                          rightTailValues,
                                        headErrors + tailErrors) := by
                                rw [hrightHeadList]
                                simp [Result.combine,
                                  GraphQL.Execution.Result.combine,
                                  mergeResponseLists]
                              rw [GraphQL.Execution.completeValueList, hhead,
                                htail]
                              simp [GraphQL.Execution.Result.combine]
                              rw [completeValueList_cons_previous, hrightTail]
                              rw [GraphQL.Execution.completeValueList,
                                hheadAppend', htailAppend', hrightTail]
                              simpa [GraphQL.Execution.Result.combine,
                                Result.combine] using hcombinedList
                          | succ rightTailErrors =>
                              simp [hrightTail, resultStatus, visitOk] at htailStatus'
                  | succ rightHeadErrors =>
                      have hheadStatus' :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues depth
                              itemType later.selectionSet value (some headValue)) =
                          visitOk := by
                        simpa [hhead, resultValueOrNull] using hheadStatus
                      simp [hrightHead, resultStatus, visitOk] at hheadStatus'

end Eager
end ExecutionUngrouped
end Algorithms

end GraphQL
