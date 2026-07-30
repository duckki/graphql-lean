import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldExecution

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped
namespace Eager

open GraphQL.Execution

def VisitSubfieldsAbsorbsFrom
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    (base : ResponseValue)
    : List Selection -> ResponseValue -> Prop
  | [], current => ResponseAbsorbs base current
  | selection :: rest, current =>
      let next :=
        visitSelection schema resolvers variableValues depth parentType source
          selection current
      ResponseAbsorbs base next.fst
      ∧ VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
          parentType source base rest next.fst

def VisitSubfieldsLocalAbsorbsFrom
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    : List Selection -> ResponseValue -> Prop
  | [], current => ResponseMergeReady current
  | selection :: rest, current =>
      let next :=
        visitSelection schema resolvers variableValues depth parentType source
          selection current
      ResponseMergeReady current
      ∧ ResponseMergeReady next.fst
      ∧ ResponseAbsorbs current next.fst
      ∧ VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues depth
          parentType source rest next.fst

theorem visitSubfields_absorbs_from_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    (base : ResponseValue)
    : ∀ (selectionSet : List Selection) (current : ResponseValue),
        VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
          parentType source base selectionSet current
        -> ResponseAbsorbs base
            (visitSubfields schema resolvers variableValues depth parentType
              source selectionSet current).fst
  | [], current, hsteps => by
      simpa [visitSubfields, VisitSubfieldsAbsorbsFrom] using hsteps
  | selection :: rest, current, hsteps => by
      simp [VisitSubfieldsAbsorbsFrom] at hsteps
      rcases hsteps with ⟨_hnext, hrest⟩
      simp [visitSubfields]
      exact visitSubfields_absorbs_from_steps schema resolvers variableValues
        depth parentType source base rest
        (visitSelection schema resolvers variableValues depth parentType source
          selection current).fst
        hrest

theorem visitSubfields_absorbs_from_local_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    (base : ResponseValue)
    : ∀ (selectionSet : List Selection) (current : ResponseValue),
        ResponseMergeReady base
        -> ResponseAbsorbs base current
        -> VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues depth
            parentType source selectionSet current
        -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
            parentType source base selectionSet current
  | [], current, _hbaseReady, hbaseCurrent, _hlocal => by
      simpa [VisitSubfieldsAbsorbsFrom] using hbaseCurrent
  | selection :: rest, current, hbaseReady, hbaseCurrent, hlocal => by
      simp [VisitSubfieldsLocalAbsorbsFrom] at hlocal
      rcases hlocal with
        ⟨hcurrentReady, hnextReady, hcurrentNext, hrestLocal⟩
      let next :=
        visitSelection schema resolvers variableValues depth parentType source
          selection current
      have hbaseNext : ResponseAbsorbs base next.fst :=
        ResponseAbsorbs_trans_of_ready base current next.fst hbaseReady
          hcurrentReady hnextReady hbaseCurrent hcurrentNext
      simp [VisitSubfieldsAbsorbsFrom, next, hbaseNext]
      exact visitSubfields_absorbs_from_local_steps schema resolvers
        variableValues depth parentType source base rest next.fst
        hbaseReady hbaseNext hrestLocal

theorem duplicateFieldSubselections_absorb_of_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (first later : ExecutableField)
    (hsteps
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])).fst
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])).fst)
    : ∀ childDepth runtimeType identity,
        childDepth < depth
        -> ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth runtimeType
              (.object runtimeType identity) first.selectionSet (.object [])).fst
            (visitSubfields schema resolvers variableValues childDepth runtimeType
              (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])).fst).fst := by
  intro childDepth runtimeType identity hlt
  exact
    visitSubfields_absorbs_from_steps schema resolvers variableValues
      childDepth runtimeType (.object runtimeType identity)
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) first.selectionSet (.object [])).fst
      later.selectionSet
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity) first.selectionSet (.object [])).fst
      (hsteps childDepth runtimeType identity hlt)

theorem VisitSubfieldsAbsorbsFrom_single_field_allowed_succ
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × ResponseValue))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : ResponseMergeReady (.object fields)
      -> (∀ existing,
            (responseName, existing) ∈ fields
            -> ResponseAbsorbs existing
                (mergeResponse existing
                  (resultValueOrNull
                    (executeField schema resolvers variableValues depth source
                      (responseObjectField? responseName (.object fields))
                      (executableField parentType responseName fieldName arguments
                        selectionSet)))))
      -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues (depth + 1)
          parentType source (.object fields)
          [.field responseName fieldName arguments directives selectionSet]
          (.object fields) := by
  intro hfieldsReady hcollisionAbsorbs
  have hstep :
      ResponseAbsorbs (.object fields)
        (visitSelection schema resolvers variableValues (depth + 1)
          parentType source
          (.field responseName fieldName arguments directives selectionSet)
          (.object fields)).fst :=
    visitSelection_field_allowed_succ_absorbs schema resolvers variableValues
      depth parentType source responseName fieldName arguments directives
      selectionSet fields hallowed hfieldsReady hcollisionAbsorbs
  simp [VisitSubfieldsAbsorbsFrom, hstep]

theorem VisitSubfieldsAbsorbsFrom_single_field_allowed_succ_of_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × ResponseValue))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh : responseName ∉ fields.map Prod.fst)
    : ResponseMergeReady (.object fields)
      -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues (depth + 1)
          parentType source (.object fields)
          [.field responseName fieldName arguments directives selectionSet]
          (.object fields) := by
  intro hfieldsReady
  have hstep :
      ResponseAbsorbs (.object fields)
        (visitSelection schema resolvers variableValues (depth + 1)
          parentType source
          (.field responseName fieldName arguments directives selectionSet)
          (.object fields)).fst :=
    visitSelection_field_allowed_succ_absorbs_of_fresh schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet fields hallowed hfresh hfieldsReady
  simp [VisitSubfieldsAbsorbsFrom, hstep]

theorem VisitSubfieldsAbsorbsFrom_nil_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    (output : ResponseValue)
    : ResponseMergeReady output
      -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
          parentType source output [] output := by
  intro hready
  simpa [VisitSubfieldsAbsorbsFrom] using
    ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_field_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : ResponseMergeReady output
      -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
          parentType source output
          [.field responseName fieldName arguments directives selectionSet]
          output := by
  intro hready
  simp [VisitSubfieldsAbsorbsFrom,
    visitSelection_field_directives_blocked schema resolvers variableValues
      depth parentType source responseName fieldName arguments directives
      selectionSet output hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_field_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : ResponseMergeReady output
      -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues 0
          parentType source output
          [.field responseName fieldName arguments directives selectionSet]
          output := by
  intro hready
  have hstep :=
    visitSelection_field_depth_zero_absorbs_of_ready schema resolvers
      variableValues parentType source responseName fieldName arguments
      directives selectionSet output hallowed hready
  simp [VisitSubfieldsAbsorbsFrom, hstep]

theorem VisitSubfieldsAbsorbsFrom_single_inline_none_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : ResponseMergeReady output
      -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
          parentType source output
          [.inlineFragment none directives selectionSet]
          output := by
  intro hready
  simp [VisitSubfieldsAbsorbsFrom,
    visitSelection_inline_none_directives_blocked schema resolvers
      variableValues depth parentType source directives selectionSet output
      hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_inline_some_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : ResponseValue)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : ResponseMergeReady output
      -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
          parentType source output
          [.inlineFragment (some typeCondition) directives selectionSet]
          output := by
  intro hready
  simp [VisitSubfieldsAbsorbsFrom,
    visitSelection_inline_some_directives_blocked schema resolvers
      variableValues depth parentType source typeCondition directives
      selectionSet output hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_inline_some_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : ResponseValue)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply : doesFragmentTypeApplyBool schema parentType source typeCondition = false)
    : ResponseMergeReady output
      -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
          parentType source output
          [.inlineFragment (some typeCondition) directives selectionSet]
          output := by
  intro hready
  simp [VisitSubfieldsAbsorbsFrom,
    visitSelection_inline_some_type_not_apply schema resolvers variableValues
      depth parentType source typeCondition directives selectionSet output
      hallowed hnotApply]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem VisitSubfieldsAbsorbsFrom_single_inline_none_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source output selectionSet output
      -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
          parentType source output
          [.inlineFragment none directives selectionSet] output := by
  intro hchild
  have habsorbs :=
    visitSubfields_absorbs_from_steps schema resolvers variableValues depth
      parentType source output selectionSet output hchild
  simp [VisitSubfieldsAbsorbsFrom, visitSelection, hallowed]
  exact habsorbs

theorem VisitSubfieldsAbsorbsFrom_single_inline_some_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : ResponseValue)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly : doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    : VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
        parentType source output selectionSet output
      -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues depth
          parentType source output
          [.inlineFragment (some typeCondition) directives selectionSet]
          output := by
  intro hchild
  have habsorbs :=
    visitSubfields_absorbs_from_steps schema resolvers variableValues depth
      parentType source output selectionSet output hchild
  simp [VisitSubfieldsAbsorbsFrom, visitSelection, hallowed, happly]
  exact habsorbs

theorem visitSelection_preserves_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ (selection : Selection) (fields : List (Name × ResponseValue)),
        ∃ outputFields,
          (visitSelection schema resolvers variableValues depth parentType source
            selection (.object fields)).fst
          = .object outputFields :=
  visitSelection_preserves_object_core schema resolvers variableValues depth
    parentType source

theorem visitSubfields_preserves_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ (selectionSet : List Selection) (fields : List (Name × ResponseValue)),
        ∃ outputFields,
          (visitSubfields schema resolvers variableValues depth parentType source
            selectionSet (.object fields)).fst
          = .object outputFields :=
  visitSubfields_preserves_object_core schema resolvers variableValues depth
    parentType source

theorem visitSubfieldsResult_empty_eq_executeRootSelectionSet_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : ExecutionWindow.visitSubfieldsResult schema resolvers variableValues depth
        parentType source selectionSet (.object [])
      = match executeRootSelectionSet schema resolvers variableValues depth
                parentType source selectionSet with
        | .error errors => .error errors
        | .ok (fields, errors) => .ok (.object fields, errors) := by
  unfold ExecutionWindow.visitSubfieldsResult executeRootSelectionSet
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source selectionSet []
  cases hvisit :
      visitSubfields schema resolvers variableValues depth parentType source
        selectionSet (.object []) with
  | mk output status =>
      have houtput : output = .object fields := by
        simpa [hvisit] using hfields
      subst output
      cases status with
      | error errors =>
          rfl
      | ok statusResult =>
          rcases statusResult with ⟨_unit, errors⟩
          rfl

mutual
  theorem visitSelection_pairKeysNodup
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selection : Selection) (fields : List (Name × ResponseValue)),
          PairKeysNodup fields
          -> PairKeysNodup
              (match (visitSelection schema resolvers variableValues depth parentType
                        source selection (.object fields)).fst with
                | .object outputFields => outputFields
                | _ => fields) := by
      intro selection fields hnodup
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          by_cases hallowed :
              selectionDirectivesAllowBool variableValues directives
          · cases depth with
            | zero =>
                cases hprevious :
                    responseObjectField? responseName (.object fields) with
                | none =>
                    simpa [visitSelection, hallowed, hprevious,
                      mergeResponseFieldResult, mergeResponseFieldIntoObject,
                      resultValueOrNull, outOfFuel] using
                      mergeResponseField_pairKeysNodup responseName .null
                        fields hnodup
                | some previous =>
                    simpa [visitSelection, hallowed, hprevious,
                      mergeResponseFieldResult, mergeResponseFieldIntoObject,
                      resultValueOrNull] using
                      mergeResponseField_pairKeysNodup responseName previous
                        fields hnodup
            | succ depth' =>
                simpa [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject] using
                  mergeResponseField_pairKeysNodup responseName
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        source
                        (responseObjectField? responseName (.object fields))
                        (executableField parentType responseName fieldName
                          arguments selectionSet)))
                    fields hnodup
          · have hblocked :
                selectionDirectivesAllowBool variableValues directives = false :=
              by
                cases h :
                    selectionDirectivesAllowBool variableValues directives with
                | false => rfl
                | true => exact False.elim (hallowed h)
            unfold visitSelection
            simpa [hblocked] using hnodup
      | inlineFragment typeCondition directives selectionSet =>
          by_cases hallowed :
              selectionDirectivesAllowBool variableValues directives
          · cases typeCondition with
            | none =>
                simpa [visitSelection, hallowed] using
                  visitSubfields_pairKeysNodup schema resolvers variableValues
                    depth parentType source selectionSet fields hnodup
            | some typeCondition =>
                by_cases happly :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition
                · simpa [visitSelection, hallowed, happly] using
                    visitSubfields_pairKeysNodup schema resolvers variableValues
                      depth parentType source selectionSet fields hnodup
                · simpa [visitSelection, hallowed, happly] using hnodup
          · have hblocked :
                selectionDirectivesAllowBool variableValues directives = false :=
              by
                cases h :
                    selectionDirectivesAllowBool variableValues directives with
                | false => rfl
                | true => exact False.elim (hallowed h)
            cases typeCondition <;>
              simpa [visitSelection, hblocked] using hnodup

  theorem visitSubfields_pairKeysNodup
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selectionSet : List Selection) (fields : List (Name × ResponseValue)),
          PairKeysNodup fields
          -> PairKeysNodup
              (match (visitSubfields schema resolvers variableValues depth parentType
                        source selectionSet (.object fields)).fst with
                | .object outputFields => outputFields
                | _ => fields) := by
      intro selectionSet fields hnodup
      cases selectionSet with
      | nil =>
          simpa [visitSubfields] using hnodup
      | cons selection rest =>
          rcases
            visitSelection_preserves_object schema resolvers variableValues
              depth parentType source selection fields
          with ⟨headFields, hhead⟩
          have hheadNodup : PairKeysNodup headFields := by
            simpa [hhead] using
              visitSelection_pairKeysNodup schema resolvers variableValues
                depth parentType source selection fields hnodup
          have htail :=
            visitSubfields_pairKeysNodup schema resolvers variableValues
              depth parentType source rest headFields hheadNodup
          rcases
            visitSubfields_preserves_object schema resolvers variableValues
              depth parentType source rest headFields
          with ⟨tailFields, htailObject⟩
          simp [visitSubfields]
          rw [hhead]
          rw [htailObject]
          simpa [htailObject] using htail
end

theorem resultValueOrNull_nonNullCompletion_ready (completed : Result ResponseValue)
    : ResponseMergeReady (resultValueOrNull completed)
      -> ResponseMergeReady (resultValueOrNull (nonNullCompletion completed)) := by
  intro hready
  cases completed with
  | error errors =>
      simp [resultValueOrNull, nonNullCompletion]
      exact ResponseMergeReady.null
  | ok result =>
      rcases result with ⟨response, errors⟩
      cases response <;>
        simp [resultValueOrNull, nonNullCompletion] at hready ⊢
      · exact ResponseMergeReady.null
      · exact hready
      · exact hready
      · exact hready

theorem resultValueOrNull_catchVisitBubbleAsNull_ready
    (value : ResponseValue) (status : VisitStatus)
    : ResponseMergeReady value
      -> ResponseMergeReady
          (resultValueOrNull (catchVisitBubbleAsNull value status)) := by
  intro hvalue
  cases status with
  | error errors =>
      simp [catchVisitBubbleAsNull, resultValueOrNull]
      exact ResponseMergeReady.null
  | ok result =>
      rcases result with ⟨u, errors⟩
      simp [catchVisitBubbleAsNull, resultValueOrNull]
      exact hvalue

theorem resultValueOrNull_catchBubbleAsNull_ready
    {α : Type} (wrap : α -> ResponseValue) (completed : Result α)
    : (∀ value errors, completed = .ok (value, errors) -> ResponseMergeReady (wrap value))
      -> ResponseMergeReady (resultValueOrNull (catchBubbleAsNull wrap completed)) := by
  intro hok
  cases completed with
  | error errors =>
      simp [catchBubbleAsNull, resultValueOrNull]
      exact ResponseMergeReady.null
  | ok result =>
      rcases result with ⟨value, errors⟩
      simp [catchBubbleAsNull, resultValueOrNull]
      exact hok value errors rfl

theorem resultValueOrNull_outOfFuel_ready
    : ResponseMergeReady (resultValueOrNull (outOfFuel : Result ResponseValue)) := by
  simp [outOfFuel, resultValueOrNull]
  exact ResponseMergeReady.null

theorem resultValueOrNull_handleFieldError_ready (fieldType : TypeRef)
    : ResponseMergeReady (resultValueOrNull (handleFieldError fieldType)) := by
  cases fieldType <;>
    simp [handleFieldError, resultValueOrNull] <;>
    exact ResponseMergeReady.null

mutual
  theorem visitSelection_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selection : Selection) (fields : List (Name × ResponseValue)),
          ResponseMergeReady (.object fields)
          -> ResponseMergeReady
              (visitSelection schema resolvers variableValues depth parentType
                source selection (.object fields)).fst := by
    intro selection fields hfieldsReady
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases depth with
          | zero =>
              cases hprevious :
                  responseObjectField? responseName (.object fields) with
              | none =>
                  have hmergedReady :
                      ResponseMergeReady
                        (.object (mergeResponseField responseName .null fields)) :=
                    mergeResponseField_object_ready_of_ready responseName .null
                      fields hfieldsReady ResponseMergeReady.null
                  simpa [visitSelection, hallowed, hprevious,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    resultValueOrNull, outOfFuel] using hmergedReady
              | some previous =>
                  have hpreviousMem :
                      (responseName, previous) ∈ fields := by
                    exact lookupResponseField?_some_mem responseName previous
                      fields (by simpa [responseObjectField?] using hprevious)
                  have hpreviousReady :
                      ResponseMergeReady previous :=
                    ResponseMergeReady_object_field fields responseName
                      previous hfieldsReady hpreviousMem
                  have hmergedReady :
                      ResponseMergeReady
                        (.object (mergeResponseField responseName previous fields)) :=
                    mergeResponseField_object_ready_of_ready responseName previous
                      fields hfieldsReady hpreviousReady
                  simpa [visitSelection, hallowed, hprevious,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    resultValueOrNull] using hmergedReady
          | succ depth' =>
              have hpreviousReady :
                  ∀ previous,
                    responseObjectField? responseName (.object fields) =
                      some previous ->
                    ResponseMergeReady previous := by
                intro previous hlookup
                exact responseObjectField?_some_ready responseName previous
                  fields hfieldsReady hlookup
              have hfieldReady :
                  ResponseMergeReady
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        source (responseObjectField? responseName (.object fields))
                        (executableField parentType responseName fieldName
                          arguments selectionSet))) :=
                executeField_response_ready_of_previous schema resolvers
                  variableValues depth' source
                  (responseObjectField? responseName (.object fields))
                  (executableField parentType responseName fieldName arguments
                    selectionSet)
                  hpreviousReady
              exact
                visitSelection_field_allowed_succ_ready schema resolvers
                  variableValues depth' parentType source responseName fieldName
                  arguments directives selectionSet fields hallowed
                  hfieldsReady hfieldReady
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives with
            | false => rfl
            | true => exact False.elim (hallowed h)
          rw [visitSelection_field_directives_blocked schema resolvers
            variableValues depth parentType source responseName fieldName
            arguments directives selectionSet (.object fields) hblocked]
          exact hfieldsReady
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases typeCondition with
          | none =>
              simpa [visitSelection, hallowed] using
                visitSubfields_response_ready schema resolvers variableValues
                  depth parentType source selectionSet fields hfieldsReady
          | some typeCondition =>
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · simpa [visitSelection, hallowed, happly] using
                  visitSubfields_response_ready schema resolvers variableValues
                    depth parentType source selectionSet fields hfieldsReady
              · simpa [visitSelection, hallowed, happly] using hfieldsReady
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives with
            | false => rfl
            | true => exact False.elim (hallowed h)
          cases typeCondition <;>
            simpa [visitSelection, hblocked] using hfieldsReady
  termination_by selection fields _hfieldsReady =>
    (depth, 0, sizeOf selection, 0)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem visitSubfields_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selectionSet : List Selection) (fields : List (Name × ResponseValue)),
          ResponseMergeReady (.object fields)
          -> ResponseMergeReady
              (visitSubfields schema resolvers variableValues depth parentType
                source selectionSet (.object fields)).fst := by
    intro selectionSet fields hfieldsReady
    cases selectionSet with
    | nil =>
        simpa [visitSubfields] using hfieldsReady
    | cons selection rest =>
        obtain ⟨headFields, hhead⟩ :=
          visitSelection_preserves_object schema resolvers variableValues depth
            parentType source selection fields
        have hheadReady : ResponseMergeReady (.object headFields) := by
          simpa [hhead] using
            visitSelection_response_ready schema resolvers variableValues depth
              parentType source selection fields hfieldsReady
        have htailReady :=
          visitSubfields_response_ready schema resolvers variableValues depth
            parentType source rest headFields hheadReady
        simp [visitSubfields]
        rw [hhead]
        simpa using htailReady
  termination_by selectionSet fields _hfieldsReady =>
    (depth, 0, sizeOf selectionSet, 0)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem completeValue_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      : ∀ (depth : Nat) (fieldType : TypeRef) (selectionSet : List Selection)
            (value : ResolverValue ObjectIdentity) (previous? : Option ResponseValue),
          (∀ previous, previous? = some previous -> ResponseMergeReady previous)
          -> ResponseMergeReady
              (resultValueOrNull
                (completeValue schema resolvers variableValues depth fieldType
                  selectionSet value previous?)) := by
    intro depth fieldType selectionSet value previous? hprevious
    cases previous? with
    | none =>
        cases depth with
        | zero =>
            simpa [completeValue] using
              resultValueOrNull_outOfFuel_ready
        | succ depth' =>
            cases fieldType with
            | nonNull inner =>
                simpa [completeValue] using
                  resultValueOrNull_nonNullCompletion_ready
                    (completeValue schema resolvers variableValues (depth' + 1)
                      inner selectionSet value none)
                    (completeValue_response_ready schema resolvers variableValues
                      (depth' + 1) inner selectionSet value none
                      (by intro previous h; cases h))
            | named typeName =>
                cases value with
                | null =>
                    simp [completeValue, resultValueOrNull]
                    exact ResponseMergeReady.null
                | scalar scalarValue =>
                    by_cases hcomposite :
                        (TypeRef.named typeName).isCompositeBool schema = true
                    · simp [completeValue, resultValueOrNull, hcomposite]
                      exact ResponseMergeReady.null
                    · simp [completeValue, resultValueOrNull, hcomposite]
                      exact ResponseMergeReady.scalar scalarValue
                | object runtimeType identity =>
                    by_cases hinclude :
                        schema.typeIncludesObjectBool typeName runtimeType
                    · have hvisitedReady :
                          ResponseMergeReady
                            (visitSubfields schema resolvers variableValues
                              depth' runtimeType (.object runtimeType identity)
                              selectionSet (.object [])).fst :=
                        visitSubfields_response_ready schema resolvers
                          variableValues depth' runtimeType
                          (.object runtimeType identity) selectionSet []
                          ResponseMergeReady_empty_object
                      simpa [completeValue, hinclude, reuseOrCreateObject?] using
                        resultValueOrNull_catchVisitBubbleAsNull_ready
                          (visitSubfields schema resolvers variableValues
                            depth' runtimeType (.object runtimeType identity)
                            selectionSet (.object [])).fst
                          (visitSubfields schema resolvers variableValues
                            depth' runtimeType (.object runtimeType identity)
                            selectionSet (.object [])).snd
                          hvisitedReady
                    · simp [completeValue, hinclude, resultValueOrNull]
                      exact ResponseMergeReady.null
                | list values =>
                    simp [completeValue, resultValueOrNull]
                    exact ResponseMergeReady.null
            | list inner =>
                cases value with
                | list values =>
                    cases values with
                    | nil =>
                        simpa [completeValue, resultValueOrNull,
                          reuseOrCreateList?, completeValueList,
                          catchBubbleAsNull] using
                          ResponseMergeReady_empty_list
                    | cons value rest =>
                        have hcompleted :
                            (∀ completedValues errors,
                              completeValueList schema resolvers variableValues
                                depth' inner selectionSet (value :: rest) [] =
                                .ok (completedValues, errors) ->
                                ResponseMergeReady
                                  (ResponseValue.list completedValues)) := by
                          intro completedValues errors hok
                          exact ResponseMergeReady.list completedValues
                            (completeValueList_values_ready schema resolvers
                              variableValues depth' inner selectionSet
                              (value :: rest) []
                              (by intro previous hmem; simp at hmem)
                              completedValues errors hok)
                        simpa [completeValue, reuseOrCreateList?] using
                          resultValueOrNull_catchBubbleAsNull_ready
                            ResponseValue.list
                            (completeValueList schema resolvers variableValues
                              depth' inner selectionSet (value :: rest) [])
                            (by
                              intro completedValues errors hok
                              exact hcompleted completedValues errors hok)
                | null =>
                    simp [completeValue, resultValueOrNull]
                    exact ResponseMergeReady.null
                | scalar scalarValue =>
                    simp [completeValue, resultValueOrNull]
                    exact ResponseMergeReady.null
                | object runtimeType identity =>
                    simp [completeValue, resultValueOrNull]
                    exact ResponseMergeReady.null
    | some previous =>
        have hpreviousReady : ResponseMergeReady previous :=
          hprevious previous rfl
        cases previous with
        | null =>
            cases depth with
            | zero =>
                simpa [completeValue] using
                  resultValueOrNull_outOfFuel_ready
            | succ depth' =>
                simp [completeValue, resultValueOrNull]
                exact ResponseMergeReady.null
        | scalar previousValue =>
            cases depth with
            | zero =>
                simpa [completeValue] using
                  resultValueOrNull_outOfFuel_ready
            | succ depth' =>
                cases fieldType with
                | nonNull inner =>
                    simpa [completeValue, nonNullCompletion] using
                      resultValueOrNull_nonNullCompletion_ready
                        (completeValue schema resolvers variableValues
                          (depth' + 1) inner selectionSet value
                          (some (.scalar previousValue)))
                        (completeValue_response_ready schema resolvers
                          variableValues (depth' + 1) inner selectionSet value
                          (some (.scalar previousValue))
                          (by intro previous h; cases h; exact hpreviousReady))
                | named typeName =>
                    cases value with
                    | null =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                    | scalar scalarValue =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                    | object runtimeType identity =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                    | list values =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                | list inner =>
                    cases value <;>
                      simp [completeValue, resultValueOrNull] <;>
                      exact ResponseMergeReady.null
        | object previousFields =>
            cases depth with
            | zero =>
                simpa [completeValue] using
                  resultValueOrNull_outOfFuel_ready
            | succ depth' =>
                cases fieldType with
                | nonNull inner =>
                    simpa [completeValue] using
                      resultValueOrNull_nonNullCompletion_ready
                        (completeValue schema resolvers variableValues
                          (depth' + 1) inner selectionSet value
                          (some (.object previousFields)))
                        (completeValue_response_ready schema resolvers
                          variableValues (depth' + 1) inner selectionSet value
                          (some (.object previousFields))
                          (by intro previous h; cases h; exact hpreviousReady))
                | named typeName =>
                    cases value with
                    | null =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                    | scalar scalarValue =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                    | object runtimeType identity =>
                        by_cases hinclude :
                            schema.typeIncludesObjectBool typeName runtimeType
                        · have hvisitedReady :
                              ResponseMergeReady
                                (visitSubfields schema resolvers variableValues
                                  depth' runtimeType (.object runtimeType identity)
                                  selectionSet (.object previousFields)).fst :=
                            visitSubfields_response_ready schema resolvers
                              variableValues depth' runtimeType
                              (.object runtimeType identity) selectionSet
                              previousFields hpreviousReady
                          simpa [completeValue, hinclude, reuseOrCreateObject?] using
                            resultValueOrNull_catchVisitBubbleAsNull_ready
                              (visitSubfields schema resolvers variableValues
                                depth' runtimeType (.object runtimeType identity)
                                selectionSet (.object previousFields)).fst
                              (visitSubfields schema resolvers variableValues
                                depth' runtimeType (.object runtimeType identity)
                                selectionSet (.object previousFields)).snd
                              hvisitedReady
                        · simp [completeValue, hinclude, resultValueOrNull]
                          exact ResponseMergeReady.null
                    | list values =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                | list inner =>
                    cases value with
                    | list values =>
                        cases values with
                        | nil =>
                            simp [completeValue, resultValueOrNull,
                              reuseOrCreateList?]
                            exact ResponseMergeReady.null
                        | cons value rest =>
                            simp [completeValue, resultValueOrNull]
                            exact ResponseMergeReady.null
                    | null =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                    | scalar scalarValue =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                    | object runtimeType identity =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
        | list previousValues =>
            cases depth with
            | zero =>
                simpa [completeValue] using
                  resultValueOrNull_outOfFuel_ready
            | succ depth' =>
                cases fieldType with
                | nonNull inner =>
                    simpa [completeValue] using
                      resultValueOrNull_nonNullCompletion_ready
                        (completeValue schema resolvers variableValues
                          (depth' + 1) inner selectionSet value
                          (some (.list previousValues)))
                        (completeValue_response_ready schema resolvers
                          variableValues (depth' + 1) inner selectionSet value
                          (some (.list previousValues))
                          (by intro previous h; cases h; exact hpreviousReady))
                | named typeName =>
                    cases value <;>
                      simp [completeValue, resultValueOrNull,
                        reuseOrCreateObject?] <;>
                      exact ResponseMergeReady.null
                | list inner =>
                    cases value with
                    | list values =>
                        cases values with
                        | nil =>
                            cases previousValues with
                            | nil =>
                                simpa [completeValue, resultValueOrNull,
                                  reuseOrCreateList?, completeValueList,
                                  catchBubbleAsNull] using
                                  ResponseMergeReady_empty_list
                            | cons previous rest =>
                                simp [completeValue, resultValueOrNull,
                                  reuseOrCreateList?, completeValueList]
                                exact ResponseMergeReady.null
                        | cons value rest =>
                            have hpreviousValuesReady :
                                ∀ previous, previous ∈ previousValues ->
                                  ResponseMergeReady previous := by
                              intro previous hmem
                              exact ResponseMergeReady_list_value previousValues
                                previous hpreviousReady hmem
                            have hcompleted :
                                (∀ completedValues errors,
                                  completeValueList schema resolvers
                                    variableValues depth' inner selectionSet
                                    (value :: rest) previousValues =
                                    .ok (completedValues, errors) ->
                                    ResponseMergeReady
                                      (ResponseValue.list completedValues)) := by
                              intro completedValues errors hok
                              exact ResponseMergeReady.list completedValues
                                (completeValueList_values_ready schema
                                  resolvers variableValues depth' inner
                                  selectionSet (value :: rest) previousValues
                                  hpreviousValuesReady completedValues
                                  errors hok)
                            simpa [completeValue, reuseOrCreateList?] using
                              resultValueOrNull_catchBubbleAsNull_ready
                                ResponseValue.list
                                (completeValueList schema resolvers
                                  variableValues depth' inner selectionSet
                                  (value :: rest) previousValues)
                                (by
                                  intro completedValues errors hok
                                  exact hcompleted completedValues errors hok)
                    | null =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                    | scalar scalarValue =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
                    | object runtimeType identity =>
                        simp [completeValue, resultValueOrNull]
                        exact ResponseMergeReady.null
  termination_by depth fieldType _selectionSet value _previous? =>
    (depth, 0, sizeOf fieldType, sizeOf value)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem completeResolvedValue_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (completionDepth : Nat)
      (fieldType : TypeRef) (selectionSet : List Selection)
      (resolved : ResolverValue ObjectIdentity) (previous? : Option ResponseValue)
      : (∀ previous, previous? = some previous -> ResponseMergeReady previous)
        -> ResponseMergeReady
            (resultValueOrNull
              (completeResolvedValue schema resolvers variableValues
                completionDepth fieldType selectionSet resolved previous?)) := by
    intro hprevious
    cases hreuse : reusablePreviousValue? schema fieldType previous? with
    | some previous =>
        have hpreviousReady : ResponseMergeReady previous :=
          hprevious previous
            (reusablePreviousValue?_some_eq schema fieldType previous? previous
              hreuse)
        have hcomplete :
            completeResolvedValue schema resolvers variableValues completionDepth
              fieldType selectionSet resolved previous? = .ok (previous, 0) := by
          unfold completeResolvedValue
          rw [hreuse]
        rw [hcomplete]
        simpa [resultValueOrNull] using hpreviousReady
    | none =>
        cases fieldType with
        | nonNull inner =>
            simpa [completeResolvedValue, hreuse] using
              resultValueOrNull_nonNullCompletion_ready
                (completeResolvedValue schema resolvers variableValues
                  completionDepth inner selectionSet resolved previous?)
                (completeResolvedValue_response_ready schema resolvers
                  variableValues completionDepth inner selectionSet resolved
                  previous? hprevious)
        | list inner =>
            have hcomplete :
                completeResolvedValue schema resolvers variableValues
                  completionDepth (.list inner) selectionSet resolved previous? =
                completeValue schema resolvers variableValues completionDepth
                  (.list inner) selectionSet resolved previous? := by
              unfold completeResolvedValue
              rw [hreuse]
            rw [hcomplete]
            exact
              completeValue_response_ready schema resolvers variableValues
                completionDepth (.list inner) selectionSet resolved previous?
                hprevious
        | named typeName =>
            have hcomplete :
                completeResolvedValue schema resolvers variableValues
                  completionDepth (.named typeName) selectionSet resolved
                  previous? =
                completeValue schema resolvers variableValues completionDepth
                  (.named typeName) selectionSet resolved previous? := by
              unfold completeResolvedValue
              rw [hreuse]
            rw [hcomplete]
            exact
              completeValue_response_ready schema resolvers variableValues
                completionDepth (.named typeName) selectionSet resolved previous?
                hprevious
  termination_by _hprevious =>
    (completionDepth, 1, sizeOf fieldType, sizeOf resolved)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem resultCombine_cons_values_ready
      (head : Result ResponseValue) (tail : Result (List ResponseValue))
      : ResponseMergeReady (resultValueOrNull head)
        -> (∀ tailValues tailErrors,
              tail = .ok (tailValues, tailErrors)
              -> ∀ response, response ∈ tailValues -> ResponseMergeReady response)
        -> ∀ completedValues errors,
            Result.combine List.cons head tail = .ok (completedValues, errors)
            -> ∀ response, response ∈ completedValues -> ResponseMergeReady response := by
    intro hheadReady htailReady completedValues errors hok response hmem
    cases head with
    | error headErrors =>
        cases tail with
        | error tailErrors =>
            simp [GraphQL.Execution.Result.combine] at hok
        | ok tailResult =>
            rcases tailResult with ⟨tailValues, tailErrors⟩
            simp [GraphQL.Execution.Result.combine] at hok
    | ok headResult =>
        rcases headResult with ⟨headValue, headErrors⟩
        cases tail with
        | error tailErrors =>
            simp [GraphQL.Execution.Result.combine] at hok
        | ok tailResult =>
            rcases tailResult with ⟨tailValues, tailErrors⟩
            simp [GraphQL.Execution.Result.combine] at hok
            rcases hok with ⟨hcompletedValues, _herrors⟩
            subst completedValues
            simp at hmem
            rcases hmem with hresponse | htailMem
            · subst response
              simpa [resultValueOrNull] using hheadReady
            · exact htailReady tailValues tailErrors rfl response htailMem

  theorem completeValueList_values_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (itemType : TypeRef) (selectionSet : List Selection)
      : ∀ (values : List (ResolverValue ObjectIdentity))
            (previousValues : List ResponseValue),
          (∀ previous, previous ∈ previousValues -> ResponseMergeReady previous)
          -> ∀ completedValues errors,
              completeValueList schema resolvers variableValues depth itemType
                  selectionSet values previousValues
                = .ok (completedValues, errors)
              -> ∀ response,
                  response ∈ completedValues -> ResponseMergeReady response := by
    intro values previousValues hpreviousValues completedValues errors hok
    cases values with
    | nil =>
        cases previousValues with
        | nil =>
            simp [completeValueList] at hok
            rcases hok with ⟨hcompletedValues, _herrors⟩
            subst completedValues
            intro response hmem
            simp at hmem
        | cons previous rest =>
            simp [completeValueList] at hok
    | cons value restValues =>
        let previous? := previousValues.head?
        let remainingPrevious := previousValues.tail
        let head : Result ResponseValue :=
          match previous? with
          | some .null => .ok (.null, 0)
          | _ =>
              completeValue schema resolvers variableValues depth itemType
                selectionSet value previous?
        let tail : Result (List ResponseValue) :=
          completeValueList schema resolvers variableValues depth itemType
            selectionSet restValues remainingPrevious
        have hprevious? :
            ∀ previous, previous? = some previous ->
              ResponseMergeReady previous := by
          cases previousValues with
          | nil =>
              intro previous hsome
              simp [previous?] at hsome
          | cons previous remainingPrevious =>
              intro previousValue hsome
              have hsome' : previous = previousValue := by
                simpa [previous?] using Option.some.inj hsome
              subst previousValue
              exact hpreviousValues previous (by simp)
        have hremainingPrevious :
            ∀ previous, previous ∈ remainingPrevious ->
              ResponseMergeReady previous := by
          cases previousValues with
          | nil =>
              intro previous hmem
              simp [remainingPrevious] at hmem
          | cons previous remainingPrevious =>
              intro previousValue hmem
              exact hpreviousValues previousValue (by
                right
                exact hmem)
        have hheadReady :
            ResponseMergeReady (resultValueOrNull head) := by
          dsimp [head]
          cases hprev : previous? with
          | none =>
              exact completeValue_response_ready schema resolvers variableValues
                depth itemType selectionSet value none
                (by
                  intro previous hsome
                  exact hprevious? previous (by rw [hprev]; exact hsome))
          | some previous =>
              cases previous with
              | null =>
                  exact ResponseMergeReady.null
              | scalar previousScalar =>
                  exact completeValue_response_ready schema resolvers
                    variableValues depth itemType selectionSet value
                    (some (.scalar previousScalar))
                    (by
                      intro previous hsome
                      exact hprevious? previous (by rw [hprev]; exact hsome))
              | object previousFields =>
                  exact completeValue_response_ready schema resolvers
                    variableValues depth itemType selectionSet value
                    (some (.object previousFields))
                    (by
                      intro previous hsome
                      exact hprevious? previous (by rw [hprev]; exact hsome))
              | list previousValues =>
                  exact completeValue_response_ready schema resolvers
                    variableValues depth itemType selectionSet value
                    (some (.list previousValues))
                    (by
                      intro previous hsome
                      exact hprevious? previous (by rw [hprev]; exact hsome))
        have htailReady :
            ∀ tailValues tailErrors,
              tail = .ok (tailValues, tailErrors) ->
                ∀ response, response ∈ tailValues ->
                  ResponseMergeReady response := by
          exact
            completeValueList_values_ready schema resolvers variableValues
              depth itemType selectionSet restValues remainingPrevious
              hremainingPrevious
        exact
          resultCombine_cons_values_ready head tail hheadReady htailReady
            completedValues errors
            (by
              rw [completeValueList.eq_3] at hok
              change Result.combine List.cons head tail =
                .ok (completedValues, errors) at hok
              exact hok)
  termination_by values previousValues _hpreviousValues completedValues errors _hok =>
    (depth, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem executeField_response_ready_of_previous
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (source : ResolverValue ObjectIdentity) (previous? : Option ResponseValue)
      (field : ExecutableField)
      : (∀ previous, previous? = some previous -> ResponseMergeReady previous)
        -> ResponseMergeReady
            (resultValueOrNull
              (executeField schema resolvers variableValues depth source previous?
                field)) := by
    intro hprevious
    cases previous? with
        | none =>
            cases hlookup : schema.lookupField field.parentType field.fieldName with
            | none =>
                simp [executeField, hlookup, resultValueOrNull]
                exact ResponseMergeReady.null
            | some fieldDefinition =>
                have hreuse :
                    reusablePreviousValue? schema fieldDefinition.outputType
                      none = none :=
                  reusablePreviousValue?_none schema fieldDefinition.outputType
                cases hresolve :
                    resolvers.resolve field.parentType field.fieldName
                      field.arguments source with
                | none =>
                    simpa [executeField, hlookup, hreuse, hresolve] using
                      resultValueOrNull_handleFieldError_ready
                        fieldDefinition.outputType
                | some resolved =>
                    simpa [executeField, hlookup, hreuse, hresolve] using
                      completeValue_response_ready schema resolvers
                        variableValues depth fieldDefinition.outputType
                        field.selectionSet resolved none hprevious
        | some previous =>
            cases previous with
            | null =>
                cases hlookup :
                    schema.lookupField field.parentType field.fieldName with
                | none =>
                    simp [executeField, hlookup, resultValueOrNull]
                    exact ResponseMergeReady.null
                | some fieldDefinition =>
                    simp [executeField, hlookup, reusablePreviousValue?_null,
                      resultValueOrNull]
                    exact ResponseMergeReady.null
            | scalar value =>
                cases hlookup : schema.lookupField field.parentType field.fieldName with
                | none =>
                    simp [executeField, hlookup, resultValueOrNull]
                    exact ResponseMergeReady.null
                | some fieldDefinition =>
                    cases hreuse :
                        reusablePreviousValue? schema fieldDefinition.outputType
                          (some (.scalar value)) with
                    | some previous =>
                        have hpreviousReady : ResponseMergeReady previous := by
                          exact hprevious previous
                            (reusablePreviousValue?_some_eq schema
                              fieldDefinition.outputType (some (.scalar value))
                              previous hreuse)
                        simpa [executeField, hlookup, hreuse, resultValueOrNull] using
                          hpreviousReady
                    | none =>
                        cases hresolve :
                            resolvers.resolve field.parentType field.fieldName
                              field.arguments source with
                        | none =>
                            simpa [executeField, hlookup, hreuse, hresolve] using
                              resultValueOrNull_handleFieldError_ready
                                fieldDefinition.outputType
                        | some resolved =>
                            simpa [executeField, hlookup, hreuse, hresolve] using
                              completeValue_response_ready schema resolvers
                                variableValues depth fieldDefinition.outputType
                                field.selectionSet resolved (some (.scalar value))
                                hprevious
            | object fields =>
                cases hlookup : schema.lookupField field.parentType field.fieldName with
                | none =>
                    simp [executeField, hlookup, resultValueOrNull]
                    exact ResponseMergeReady.null
                | some fieldDefinition =>
                    cases hreuse :
                        reusablePreviousValue? schema fieldDefinition.outputType
                          (some (.object fields)) with
                    | some previous =>
                        have hpreviousReady : ResponseMergeReady previous := by
                          exact hprevious previous
                            (reusablePreviousValue?_some_eq schema
                              fieldDefinition.outputType (some (.object fields))
                              previous hreuse)
                        simpa [executeField, hlookup, hreuse, resultValueOrNull] using
                          hpreviousReady
                    | none =>
                        cases hresolve :
                            resolvers.resolve field.parentType field.fieldName
                              field.arguments source with
                        | none =>
                            simpa [executeField, hlookup, hreuse, hresolve] using
                              resultValueOrNull_handleFieldError_ready
                                fieldDefinition.outputType
                        | some resolved =>
                            simpa [executeField, hlookup, hreuse, hresolve] using
                              completeValue_response_ready schema resolvers
                                variableValues depth fieldDefinition.outputType
                                field.selectionSet resolved (some (.object fields))
                                hprevious
            | list values =>
                cases hlookup : schema.lookupField field.parentType field.fieldName with
                | none =>
                    simp [executeField, hlookup, resultValueOrNull]
                    exact ResponseMergeReady.null
                | some fieldDefinition =>
                    cases hreuse :
                        reusablePreviousValue? schema fieldDefinition.outputType
                          (some (.list values)) with
                    | some previous =>
                        have hpreviousReady : ResponseMergeReady previous := by
                          exact hprevious previous
                            (reusablePreviousValue?_some_eq schema
                              fieldDefinition.outputType (some (.list values))
                              previous hreuse)
                        simpa [executeField, hlookup, hreuse, resultValueOrNull] using
                          hpreviousReady
                    | none =>
                        cases hresolve :
                            resolvers.resolve field.parentType field.fieldName
                              field.arguments source with
                        | none =>
                            simpa [executeField, hlookup, hreuse, hresolve] using
                              resultValueOrNull_handleFieldError_ready
                                fieldDefinition.outputType
                        | some resolved =>
                            simpa [executeField, hlookup, hreuse, hresolve] using
                              completeValue_response_ready schema resolvers
                                variableValues depth fieldDefinition.outputType
                                field.selectionSet resolved (some (.list values))
                                hprevious
  termination_by _hprevious =>
    (depth, 1, sizeOf field, 0)
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

theorem executeField_response_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (fields : List (Name × ResponseValue))
    (field : ExecutableField)
    : ResponseMergeReady (.object fields)
      -> ResponseMergeReady
          (resultValueOrNull
            (executeField schema resolvers variableValues depth source
              (some (.object fields)) field)) := by
    intro hfieldsReady
    exact executeField_response_ready_of_previous schema resolvers variableValues
      depth source (some (.object fields)) field
      (by intro previous h; cases h; exact hfieldsReady)

mutual
  theorem visitSelection_local_absorbs_from_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selection : Selection) (fields : List (Name × ResponseValue)),
          ResponseMergeReady (.object fields)
          ->  let next :=
                visitSelection schema resolvers variableValues depth parentType
                  source selection (.object fields)
              ResponseMergeReady (.object fields)
              ∧ ResponseMergeReady next.fst
              ∧ ResponseAbsorbs (.object fields) next.fst := by
    intro selection fields hfieldsReady
    have hnextReady :
        ResponseMergeReady
          (visitSelection schema resolvers variableValues depth parentType
            source selection (.object fields)).fst :=
      visitSelection_response_ready schema resolvers variableValues depth
        parentType source selection fields hfieldsReady
    refine ⟨hfieldsReady, hnextReady, ?_⟩
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases depth with
          | zero =>
              exact
                visitSelection_field_depth_zero_absorbs_of_ready schema
                  resolvers variableValues parentType source responseName
                  fieldName arguments directives selectionSet (.object fields)
                  hallowed hfieldsReady
          | succ depth' =>
              have hpreviousReady :
                  ∀ previous,
                    responseObjectField? responseName (.object fields) =
                      some previous ->
                    ResponseMergeReady previous := by
                intro previous hlookup
                exact responseObjectField?_some_ready responseName previous
                  fields hfieldsReady hlookup
              have hfieldReady :
                  ResponseMergeReady
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        source
                        (responseObjectField? responseName (.object fields))
                        (executableField parentType responseName fieldName
                          arguments selectionSet))) :=
                executeField_response_ready_of_previous schema resolvers
                  variableValues depth' source
                  (responseObjectField? responseName (.object fields))
                  (executableField parentType responseName fieldName arguments
                    selectionSet)
                  hpreviousReady
              exact
                visitSelection_field_allowed_succ_absorbs schema resolvers
                  variableValues depth' parentType source responseName fieldName
                  arguments directives selectionSet fields hallowed
                  hfieldsReady
                  (by
                    intro existing hmem
                    exact
                      ResponseAbsorbs_merge_of_ready existing
                        (resultValueOrNull
                          (executeField schema resolvers variableValues depth'
                            source
                            (responseObjectField? responseName (.object fields))
                            (executableField parentType responseName fieldName
                              arguments selectionSet)))
                        (ResponseMergeReady_object_field fields responseName
                          existing hfieldsReady hmem)
                        hfieldReady)
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives with
            | false => rfl
            | true => exact False.elim (hallowed h)
          rw [visitSelection_field_directives_blocked schema resolvers
            variableValues depth parentType source responseName fieldName
            arguments directives selectionSet (.object fields) hblocked]
          exact ResponseAbsorbs_refl_of_ready (.object fields) hfieldsReady
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases typeCondition with
          | none =>
              have hlocal :=
                visitSubfields_local_absorbs_from_ready schema resolvers
                  variableValues depth parentType source selectionSet fields
                  hfieldsReady
              have hsteps :=
                visitSubfields_absorbs_from_local_steps schema resolvers
                  variableValues depth parentType source (.object fields)
                  selectionSet (.object fields) hfieldsReady
                  (ResponseAbsorbs_refl_of_ready (.object fields) hfieldsReady)
                  hlocal
              have habsorbs :=
                visitSubfields_absorbs_from_steps schema resolvers
                  variableValues depth parentType source (.object fields)
                  selectionSet (.object fields) hsteps
              simpa [visitSelection, hallowed] using habsorbs
          | some typeCondition =>
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · have hlocal :=
                  visitSubfields_local_absorbs_from_ready schema resolvers
                    variableValues depth parentType source selectionSet fields
                    hfieldsReady
                have hsteps :=
                  visitSubfields_absorbs_from_local_steps schema resolvers
                    variableValues depth parentType source (.object fields)
                    selectionSet (.object fields) hfieldsReady
                    (ResponseAbsorbs_refl_of_ready (.object fields)
                      hfieldsReady)
                    hlocal
                have habsorbs :=
                  visitSubfields_absorbs_from_steps schema resolvers
                    variableValues depth parentType source (.object fields)
                    selectionSet (.object fields) hsteps
                simpa [visitSelection, hallowed, happly] using habsorbs
              · simpa [visitSelection, hallowed, happly] using
                  ResponseAbsorbs_refl_of_ready (.object fields)
                    hfieldsReady
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives with
            | false => rfl
            | true => exact False.elim (hallowed h)
          cases typeCondition <;>
            simpa [visitSelection, hblocked] using
              ResponseAbsorbs_refl_of_ready (.object fields) hfieldsReady

  theorem visitSubfields_local_absorbs_from_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selectionSet : List Selection) (fields : List (Name × ResponseValue)),
          ResponseMergeReady (.object fields)
          -> VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues depth
              parentType source selectionSet (.object fields) := by
    intro selectionSet fields hfieldsReady
    cases selectionSet with
    | nil =>
        simpa [VisitSubfieldsLocalAbsorbsFrom] using hfieldsReady
    | cons selection rest =>
        rcases
          visitSelection_local_absorbs_from_ready schema resolvers
            variableValues depth parentType source selection fields hfieldsReady
        with ⟨hcurrentReady, hnextReady, habsorbs⟩
        obtain ⟨headFields, hhead⟩ :=
          visitSelection_preserves_object schema resolvers variableValues depth
            parentType source selection fields
        have hheadReady : ResponseMergeReady (.object headFields) := by
          simpa [hhead] using hnextReady
        have hrest :=
          visitSubfields_local_absorbs_from_ready schema resolvers
            variableValues depth parentType source rest headFields hheadReady
        simp [VisitSubfieldsLocalAbsorbsFrom]
        rw [hhead]
        exact ⟨hcurrentReady, by simpa [hhead] using hnextReady,
          by simpa [hhead] using habsorbs, hrest⟩
end

theorem VisitSubfieldsAbsorbsFrom_single_field_allowed_succ_of_visit_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (firstSelectionSet : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh
      : ∀ fields,
          (visitSubfields schema resolvers variableValues (depth + 1)
              parentType source firstSelectionSet (.object [])).fst
            = .object fields
          -> responseName ∉ fields.map Prod.fst)
    : VisitSubfieldsAbsorbsFrom schema resolvers variableValues (depth + 1)
        parentType source
        (visitSubfields schema resolvers variableValues (depth + 1)
          parentType source firstSelectionSet (.object [])).fst
        [.field responseName fieldName arguments directives selectionSet]
        (visitSubfields schema resolvers variableValues (depth + 1)
          parentType source firstSelectionSet (.object [])).fst := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (depth + 1) parentType source firstSelectionSet []
  rw [hfields]
  apply VisitSubfieldsAbsorbsFrom_single_field_allowed_succ_of_fresh
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet fields hallowed
    (hfresh fields hfields)
  simpa [hfields] using
    visitSubfields_response_ready schema resolvers variableValues (depth + 1)
      parentType source firstSelectionSet [] ResponseMergeReady_empty_object

end Eager
end ExecutionUngrouped

end Algorithms
end GraphQL
