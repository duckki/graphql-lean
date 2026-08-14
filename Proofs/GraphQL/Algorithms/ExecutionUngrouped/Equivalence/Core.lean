import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Eager
import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.Shared.Execution
import Proofs.GraphQL.Theories.NormalForm.Shared.FieldMerge
import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeTypes
import Proofs.GraphQL.SchemaWellFormedness.PossibleTypes
import Proofs.GraphQL.Validation.FieldMerge
import Proofs.GraphQL.Validation.SelectionValidity

/-!
Proof-facing scaffolding for relating direct ungrouped execution to the grouped
spec execution in `GraphQL.Execution`.

The final equivalence theorem is intended for valid operations over stable resolver
behavior: validation rules rule out invalid alias collisions, and explicit global
invariants supply the assumption that repeated field visits for the same response key
resolve the same source data. The algorithm itself remains operationally direct and may
call resolvers more often than the grouped spec; equivalence is about the public response
envelope, including response data and the counted execution errors.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution
structure ExecutionWindow (ObjectIdentity : Type) where
  schema : Schema
  resolvers : Resolvers ObjectIdentity
  variableValues : VariableValues
  depth : Nat
  parentType : Name
  source : ResolverValue ObjectIdentity
  selectionSet : List Selection

namespace ExecutionWindow

abbrev visitSubfieldsResult
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (initial : ResponseValue)
    : Result ResponseValue :=
  let visited :=
    visitSubfields schema resolvers variableValues depth parentType source
      selectionSet initial
  match visited.snd with
  | .error errors => .error errors
  | .ok (_unit, errors) => .ok (visited.fst, errors)

@[simp]
theorem visitSubfieldsResult_nil
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (initial : ResponseValue)
    : visitSubfieldsResult schema resolvers variableValues depth parentType source
        [] initial
      = .ok (initial, 0) := by
  simp [visitSubfieldsResult, visitSubfields, visitOk]

def ungroupedResult (window : ExecutionWindow ObjectIdentity)
    : Result (List (Name × ResponseValue)) :=
  executeRootSelectionSet window.schema window.resolvers window.variableValues
    window.depth window.parentType window.source window.selectionSet

def specResult (window : ExecutionWindow ObjectIdentity)
    : Result (List (Name × ResponseValue)) :=
  GraphQL.Execution.executeRootSelectionSet window.schema window.resolvers
    window.variableValues window.depth window.parentType window.source
    window.selectionSet

def ungroupedResponseFields (window : ExecutionWindow ObjectIdentity)
    : List (Name × ResponseValue) :=
  GraphQL.Execution.Result.getD [] window.ungroupedResult

def specResponseFields (window : ExecutionWindow ObjectIdentity)
    : List (Name × ResponseValue) :=
  GraphQL.Execution.Result.getD [] window.specResult

def ungroupedResponse (window : ExecutionWindow ObjectIdentity) : ResponseValue :=
  .object window.ungroupedResponseFields

def specResponse (window : ExecutionWindow ObjectIdentity) : ResponseValue :=
  .object window.specResponseFields

end ExecutionWindow

structure ExecutionEquivalenceState (ObjectIdentity : Type) where
  window : ExecutionWindow ObjectIdentity
  initial : ResponseValue

namespace ExecutionEquivalenceState

def ungroupedProjectionResult (state : ExecutionEquivalenceState ObjectIdentity)
    : Result ResponseValue :=
  ExecutionWindow.visitSubfieldsResult state.window.schema state.window.resolvers
    state.window.variableValues state.window.depth state.window.parentType
    state.window.source state.window.selectionSet state.initial

def specProjectionResult (state : ExecutionEquivalenceState ObjectIdentity)
    : Result ResponseValue :=
  match GraphQL.Execution.executeCollectedFields state.window.schema
          state.window.resolvers state.window.variableValues state.window.depth
          state.window.source
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType state.window.source
            state.window.selectionSet) with
  | .error errors => .error errors
  | .ok (fields, errors) =>
      .ok (mergeResponse state.initial (.object fields), errors)

def ungroupedProjection (state : ExecutionEquivalenceState ObjectIdentity)
    : ResponseValue :=
  GraphQL.Execution.Result.getD default state.ungroupedProjectionResult

def specProjection (state : ExecutionEquivalenceState ObjectIdentity) : ResponseValue :=
  GraphQL.Execution.Result.getD default state.specProjectionResult

end ExecutionEquivalenceState

def ResponseValueEquivalent (left right : ResponseValue) : Prop :=
  left = right

def ResponseResultEquivalent {α : Type} (left right : Result α) : Prop :=
  left = right

def resultErrorCount {α : Type} : Result α -> Nat
  | .error errors => errors
  | .ok (_value, errors) => errors

theorem resultErrorCount_combine
    {α β γ : Type} (combine : α -> β -> γ)
    (left : Result α) (right : Result β)
    : resultErrorCount (GraphQL.Execution.Result.combine combine left right)
      = resultErrorCount left + resultErrorCount right := by
  cases left <;> cases right <;> simp [resultErrorCount,
    GraphQL.Execution.Result.combine]

def ErrorPresenceEquivalent (ungrouped spec : Nat) : Prop :=
  (spec = 0 -> ungrouped = 0) ∧ (0 < spec -> 0 < ungrouped)

theorem ErrorPresenceEquivalent.refl (errors : Nat)
    : ErrorPresenceEquivalent errors errors :=
  ⟨fun hzero => hzero, fun hpositive => hpositive⟩

theorem ErrorPresenceEquivalent.of_pos
    {ungrouped spec : Nat} (hUngrouped : 0 < ungrouped)
    (hSpec : 0 < spec)
    : ErrorPresenceEquivalent ungrouped spec := by
  constructor
  · intro hzero
    omega
  · intro _hpositive
    exact hUngrouped

theorem ErrorPresenceEquivalent.trans {left middle right : Nat}
    : ErrorPresenceEquivalent left middle
      -> ErrorPresenceEquivalent middle right
      -> ErrorPresenceEquivalent left right := by
  intro hleft hmiddle
  exact ⟨
    fun hrightZero => hleft.1 (hmiddle.1 hrightZero),
    fun hrightPositive => hleft.2 (hmiddle.2 hrightPositive)
  ⟩

theorem ErrorPresenceEquivalent.symm {left right : Nat}
    : ErrorPresenceEquivalent left right -> ErrorPresenceEquivalent right left := by
  intro h
  constructor
  · intro hleftZero
    by_cases hrightZero : right = 0
    · exact hrightZero
    · have hrightPositive : 0 < right := Nat.pos_of_ne_zero hrightZero
      have hleftPositive : 0 < left := h.2 hrightPositive
      omega
  · intro hleftPositive
    by_cases hrightZero : right = 0
    · have hleftZero : left = 0 := h.1 hrightZero
      omega
    · exact Nat.pos_of_ne_zero hrightZero

theorem ErrorPresenceEquivalent.add
    {ungroupedLeft specLeft ungroupedRight specRight : Nat}
    (hleft : ErrorPresenceEquivalent ungroupedLeft specLeft)
    (hright : ErrorPresenceEquivalent ungroupedRight specRight)
    : ErrorPresenceEquivalent
        (ungroupedLeft + ungroupedRight) (specLeft + specRight) := by
  constructor
  · intro hzero
    have hspecLeft : specLeft = 0 := by omega
    have hspecRight : specRight = 0 := by omega
    have hungroupedLeft : ungroupedLeft = 0 := hleft.1 hspecLeft
    have hungroupedRight : ungroupedRight = 0 := hright.1 hspecRight
    omega
  · intro hpositive
    by_cases hspecLeft : specLeft = 0
    · have hspecRightPositive : 0 < specRight := by omega
      have hungroupedRightPositive : 0 < ungroupedRight :=
        hright.2 hspecRightPositive
      omega
    · have hspecLeftPositive : 0 < specLeft := Nat.pos_of_ne_zero hspecLeft
      have hungroupedLeftPositive : 0 < ungroupedLeft :=
        hleft.2 hspecLeftPositive
      omega

theorem ErrorPresenceEquivalent.drop_right_of_left_pos
    {left right spec : Nat} (hleft : 0 < left)
    (hcombined : ErrorPresenceEquivalent (left + right) spec)
    : ErrorPresenceEquivalent left spec := by
  constructor
  · intro hspecZero
    have hsumZero := hcombined.1 hspecZero
    omega
  · intro _hspecPositive
    exact hleft

theorem ErrorPresenceEquivalent.add_spec_right_of_ungrouped_pos
    {ungrouped specLeft specRight : Nat} (hUngrouped : 0 < ungrouped)
    (hleft : ErrorPresenceEquivalent ungrouped specLeft)
    : ErrorPresenceEquivalent ungrouped (specLeft + specRight) := by
  constructor
  · intro hzero
    have hspecLeftZero : specLeft = 0 := by omega
    have hungroupedZero := hleft.1 hspecLeftZero
    omega
  · intro _hpositive
    exact hUngrouped

theorem ErrorPresenceEquivalent.add_reassociate
    {headLeft headRight tailLeft tailRight headSpec tailSpec : Nat}
    (hhead : ErrorPresenceEquivalent (headLeft + headRight) headSpec)
    (htail : ErrorPresenceEquivalent (tailLeft + tailRight) tailSpec)
    : ErrorPresenceEquivalent
        (headLeft + tailLeft + (headRight + tailRight))
        (headSpec + tailSpec) := by
  have hcombined := ErrorPresenceEquivalent.add hhead htail
  constructor
  · intro hzero
    have hleftZero := hcombined.1 hzero
    omega
  · intro hpositive
    have hleftPositive := hcombined.2 hpositive
    omega

def ResultDataAndErrorPresenceEquivalent {α : Type} [Inhabited α]
    (ungrouped spec : Result α)
    : Prop :=
  GraphQL.Execution.Result.getD default ungrouped
    = GraphQL.Execution.Result.getD default spec
  ∧ (resultErrorCount spec = 0 -> resultErrorCount ungrouped = 0)
  ∧ (0 < resultErrorCount spec -> 0 < resultErrorCount ungrouped)

theorem ResultDataAndErrorPresenceEquivalent.of_eq
    {α : Type} [Inhabited α] {ungrouped spec : Result α}
    (h : ungrouped = spec)
    : ResultDataAndErrorPresenceEquivalent ungrouped spec := by
  subst ungrouped
  exact ⟨rfl, fun hzero => hzero, fun hpositive => hpositive⟩

theorem ResultDataAndErrorPresenceEquivalent.trans
    {α : Type} [Inhabited α] {left middle right : Result α}
    : ResultDataAndErrorPresenceEquivalent left middle
      -> ResultDataAndErrorPresenceEquivalent middle right
      -> ResultDataAndErrorPresenceEquivalent left right := by
  intro hleft hmiddle
  rcases hleft with ⟨hleftData, hleftZero, hleftPositive⟩
  rcases hmiddle with ⟨hmiddleData, hmiddleZero, hmiddlePositive⟩
  exact ⟨
    hleftData.trans hmiddleData,
    fun hrightZero => hleftZero (hmiddleZero hrightZero),
    fun hrightPositive => hleftPositive (hmiddlePositive hrightPositive)
  ⟩

theorem ResultDataAndErrorPresenceEquivalent.errorPresence
    {α : Type} [Inhabited α] {ungrouped spec : Result α}
    : ResultDataAndErrorPresenceEquivalent ungrouped spec
      -> ErrorPresenceEquivalent (resultErrorCount ungrouped)
          (resultErrorCount spec) := by
  intro h
  exact ⟨h.2.1, h.2.2⟩

def ResponseValueResultAlignedEquivalent (ungrouped spec : Result ResponseValue) : Prop :=
  match ungrouped, spec with
  | .error ungroupedErrors, .error specErrors =>
      ErrorPresenceEquivalent ungroupedErrors specErrors
  | .ok (ungroupedValue, ungroupedErrors), .ok (specValue, specErrors) =>
      ungroupedValue = specValue ∧ ErrorPresenceEquivalent ungroupedErrors specErrors
  | _, _ => False

theorem ResponseValueResultAlignedEquivalent.of_eq
    {ungrouped spec : Result ResponseValue} (h : ungrouped = spec)
    : ResponseValueResultAlignedEquivalent ungrouped spec := by
  subst ungrouped
  cases spec with
  | error errors =>
      exact ErrorPresenceEquivalent.refl errors
  | ok result =>
      rcases result with ⟨value, errors⟩
      exact ⟨rfl, ErrorPresenceEquivalent.refl errors⟩

theorem ResponseValueResultAlignedEquivalent.trans
    {left middle right : Result ResponseValue}
    : ResponseValueResultAlignedEquivalent left middle
      -> ResponseValueResultAlignedEquivalent middle right
      -> ResponseValueResultAlignedEquivalent left right := by
  intro hleft hmiddle
  cases left <;> cases middle <;> cases right <;>
    simp [ResponseValueResultAlignedEquivalent] at hleft hmiddle ⊢
  · exact ErrorPresenceEquivalent.trans hleft hmiddle
  · rcases hleft with ⟨hleftValue, hleftErrors⟩
    rcases hmiddle with ⟨hmiddleValue, hmiddleErrors⟩
    exact ⟨
      hleftValue.trans hmiddleValue,
      ErrorPresenceEquivalent.trans hleftErrors hmiddleErrors
    ⟩

theorem ResponseValueResultAlignedEquivalent.symm {left right : Result ResponseValue}
    : ResponseValueResultAlignedEquivalent left right
      -> ResponseValueResultAlignedEquivalent right left := by
  intro h
  cases left <;> cases right <;>
    simp [ResponseValueResultAlignedEquivalent] at h ⊢
  · exact ErrorPresenceEquivalent.symm h
  · rcases h with ⟨hvalue, herrors⟩
    exact ⟨hvalue.symm, ErrorPresenceEquivalent.symm herrors⟩

theorem ResponseValueResultAlignedEquivalent.resultValueOrNull_eq
    {left right : Result ResponseValue}
    : ResponseValueResultAlignedEquivalent left right
      -> resultValueOrNull left = resultValueOrNull right := by
  intro h
  cases left <;> cases right <;>
    simp [ResponseValueResultAlignedEquivalent, resultValueOrNull] at h ⊢
  rcases h with ⟨hvalue, _herrors⟩
  exact hvalue

theorem ResponseValueResultAlignedEquivalent.nonNullCompletion_aligned
    {ungrouped spec : Result ResponseValue}
    (h : ResponseValueResultAlignedEquivalent ungrouped spec)
    : ResponseValueResultAlignedEquivalent
        (nonNullCompletion ungrouped) (nonNullCompletion spec) := by
  cases ungrouped <;> cases spec <;>
    simp [ResponseValueResultAlignedEquivalent, nonNullCompletion,
      ErrorPresenceEquivalent] at h ⊢
  · exact h
  · rcases h with ⟨hvalue, herrors⟩
    rename_i ungroupedResult specResult
    rcases ungroupedResult with ⟨value, ungroupedErrors⟩
    rcases specResult with ⟨specValue, specErrors⟩
    simp at hvalue herrors
    subst specValue
    cases value <;> cases ungroupedErrors <;> cases specErrors <;>
      simp at herrors ⊢
    all_goals omega

theorem ResponseValueResultAlignedEquivalent.nonNull_merge_inner
    {left right wrappedRight : Result ResponseValue}
    (hleftErrorPositive : ∀ errors, left = .error errors -> 0 < errors)
    (hrightErrorPositive : ∀ errors, right = .error errors -> 0 < errors)
    (hwrappedNull : resultValueOrNull left = .null -> wrappedRight = .ok (.null, 0))
    (hwrappedNonNull
      : resultValueOrNull left ≠ .null
        -> wrappedRight = GraphQL.Execution.nonNullCompletion right)
    : ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse
          (GraphQL.Execution.nonNullCompletion left) wrappedRight)
        (GraphQL.Execution.nonNullCompletion
          (GraphQL.Execution.Result.combine mergeResponse left right)) := by
  cases left with
  | error leftErrors =>
      have hleftPositive : 0 < leftErrors :=
        hleftErrorPositive leftErrors rfl
      have hwrapped : wrappedRight = .ok (.null, 0) :=
        hwrappedNull rfl
      subst wrappedRight
      cases right with
      | error rightErrors =>
          simp [GraphQL.Execution.Result.combine, nonNullCompletion,
            ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          exact ⟨fun hleftZero _hrightZero => hleftZero,
            fun _hpositive => hleftPositive⟩
      | ok rightResult =>
          rcases rightResult with ⟨rightValue, rightErrors⟩
          simp [GraphQL.Execution.Result.combine, nonNullCompletion,
            ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          omega
  | ok leftResult =>
      rcases leftResult with ⟨leftValue, leftErrors⟩
      cases leftValue with
      | null =>
          have hwrapped : wrappedRight = .ok (.null, 0) :=
            hwrappedNull rfl
          subst wrappedRight
          cases leftErrors with
          | zero =>
              cases right with
              | error rightErrors =>
                  have hrightPositive : 0 < rightErrors :=
                    hrightErrorPositive rightErrors rfl
                  simp [GraphQL.Execution.Result.combine, nonNullCompletion,
                    ResponseValueResultAlignedEquivalent,
                    ErrorPresenceEquivalent]
                  omega
              | ok rightResult =>
                  rcases rightResult with ⟨rightValue, rightErrors⟩
                  cases rightValue <;> cases rightErrors <;>
                    simp [GraphQL.Execution.Result.combine,
                      nonNullCompletion,
                      ResponseValueResultAlignedEquivalent,
                      ErrorPresenceEquivalent, mergeResponse]
          | succ leftErrors =>
              cases right with
              | error rightErrors =>
                  simp [GraphQL.Execution.Result.combine, nonNullCompletion,
                    ResponseValueResultAlignedEquivalent,
                    ErrorPresenceEquivalent]
              | ok rightResult =>
                  rcases rightResult with ⟨rightValue, rightErrors⟩
                  cases rightValue <;> cases rightErrors <;>
                    simp [GraphQL.Execution.Result.combine,
                      nonNullCompletion,
                      ResponseValueResultAlignedEquivalent,
                      ErrorPresenceEquivalent, mergeResponse] <;>
                    try omega
      | scalar leftScalar =>
          have hwrapped : wrappedRight = nonNullCompletion right :=
            hwrappedNonNull (by simp [resultValueOrNull])
          subst wrappedRight
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine, nonNullCompletion,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | ok rightResult =>
              rcases rightResult with ⟨rightValue, rightErrors⟩
              cases rightValue <;> cases rightErrors <;> cases leftErrors <;>
                simp [GraphQL.Execution.Result.combine, nonNullCompletion,
                  ResponseValueResultAlignedEquivalent,
                  ErrorPresenceEquivalent, mergeResponse] <;>
                try omega
      | object leftFields =>
          have hwrapped : wrappedRight = nonNullCompletion right :=
            hwrappedNonNull (by simp [resultValueOrNull])
          subst wrappedRight
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine, nonNullCompletion,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | ok rightResult =>
              rcases rightResult with ⟨rightValue, rightErrors⟩
              cases rightValue <;> cases rightErrors <;> cases leftErrors <;>
                simp [GraphQL.Execution.Result.combine, nonNullCompletion,
                  ResponseValueResultAlignedEquivalent,
                  ErrorPresenceEquivalent, mergeResponse] <;>
                try omega
      | list leftValues =>
          have hwrapped : wrappedRight = nonNullCompletion right :=
            hwrappedNonNull (by simp [resultValueOrNull])
          subst wrappedRight
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine, nonNullCompletion,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | ok rightResult =>
              rcases rightResult with ⟨rightValue, rightErrors⟩
              cases rightValue <;> cases rightErrors <;> cases leftErrors <;>
                simp [GraphQL.Execution.Result.combine, nonNullCompletion,
                  ResponseValueResultAlignedEquivalent,
                  ErrorPresenceEquivalent, mergeResponse] <;>
                try omega

theorem ResponseValueResultAlignedEquivalent.combine_mergeResponse
    {ungroupedLeft specLeft ungroupedRight specRight : Result ResponseValue}
    (hleft : ResponseValueResultAlignedEquivalent ungroupedLeft specLeft)
    (hright : ResponseValueResultAlignedEquivalent ungroupedRight specRight)
    : ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse ungroupedLeft ungroupedRight)
        (GraphQL.Execution.Result.combine mergeResponse specLeft specRight) := by
  cases ungroupedLeft <;> cases specLeft <;>
    cases ungroupedRight <;> cases specRight <;>
    simp [ResponseValueResultAlignedEquivalent,
      GraphQL.Execution.Result.combine] at hleft hright ⊢
  · exact ErrorPresenceEquivalent.add hleft hright
  · exact ErrorPresenceEquivalent.add hleft hright.2
  · exact ErrorPresenceEquivalent.add hleft.2 hright
  · rcases hleft with ⟨hleftValue, hleftErrors⟩
    rcases hright with ⟨hrightValue, hrightErrors⟩
    rw [hleftValue, hrightValue]
    exact ⟨rfl, ErrorPresenceEquivalent.add hleftErrors hrightErrors⟩

def ListResponseResultAlignedEquivalent (ungrouped spec : Result (List ResponseValue))
    : Prop :=
  match ungrouped, spec with
  | .error ungroupedErrors, .error specErrors =>
      ErrorPresenceEquivalent ungroupedErrors specErrors
  | .ok (ungroupedValues, ungroupedErrors), .ok (specValues, specErrors) =>
      ungroupedValues = specValues ∧ ErrorPresenceEquivalent ungroupedErrors specErrors
  | _, _ => False

theorem ListResponseResultAlignedEquivalent.of_eq
    {ungrouped spec : Result (List ResponseValue)} (h : ungrouped = spec)
    : ListResponseResultAlignedEquivalent ungrouped spec := by
  subst ungrouped
  cases spec with
  | error errors =>
      exact ErrorPresenceEquivalent.refl errors
  | ok result =>
      rcases result with ⟨values, errors⟩
      exact ⟨rfl, ErrorPresenceEquivalent.refl errors⟩

theorem ListResponseResultAlignedEquivalent.combine_cons
    {ungroupedHead specHead : Result ResponseValue}
    {ungroupedTail specTail : Result (List ResponseValue)}
    (hhead : ResponseValueResultAlignedEquivalent ungroupedHead specHead)
    (htail : ListResponseResultAlignedEquivalent ungroupedTail specTail)
    : ListResponseResultAlignedEquivalent
        (GraphQL.Execution.Result.combine List.cons ungroupedHead ungroupedTail)
        (GraphQL.Execution.Result.combine List.cons specHead specTail) := by
  cases ungroupedHead <;> cases specHead <;>
    cases ungroupedTail <;> cases specTail <;>
    simp [ResponseValueResultAlignedEquivalent,
      ListResponseResultAlignedEquivalent,
      GraphQL.Execution.Result.combine] at hhead htail ⊢
  · exact ErrorPresenceEquivalent.add hhead htail
  · exact ErrorPresenceEquivalent.add hhead htail.2
  · exact ErrorPresenceEquivalent.add hhead.2 htail
  · rcases hhead with ⟨hheadValue, hheadErrors⟩
    rcases htail with ⟨htailValue, htailErrors⟩
    rw [hheadValue, htailValue]
    exact ⟨⟨rfl, rfl⟩, ErrorPresenceEquivalent.add hheadErrors htailErrors⟩

theorem ListResponseResultAlignedEquivalent.catchBubbleAsNull
    {ungrouped spec : Result (List ResponseValue)}
    (h : ListResponseResultAlignedEquivalent ungrouped spec)
    : ResponseValueResultAlignedEquivalent
        (catchBubbleAsNull ResponseValue.list ungrouped)
        (catchBubbleAsNull ResponseValue.list spec) := by
  cases ungrouped <;> cases spec <;>
    simp [ListResponseResultAlignedEquivalent,
      ResponseValueResultAlignedEquivalent,
      GraphQL.Execution.catchBubbleAsNull] at h ⊢
  · exact h
  · exact h

theorem ListResponseResultAlignedEquivalent.catchBubbleAsNull_mergeResponse
    {base right spec : Result (List ResponseValue)}
    (hrightBaseError : ∀ errors, base = .error errors -> right = .ok ([], 0))
    (h
      : ListResponseResultAlignedEquivalent
          (GraphQL.Execution.Result.combine mergeResponseLists base right)
          spec)
    : ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse
          (GraphQL.Execution.catchBubbleAsNull ResponseValue.list base)
          (match base with
            | .error _errors => .ok (.null, 0)
            | .ok _result =>
                GraphQL.Execution.catchBubbleAsNull ResponseValue.list right))
        (GraphQL.Execution.catchBubbleAsNull ResponseValue.list spec) := by
  cases base with
  | error baseErrors =>
      have hright : right = .ok ([], 0) :=
        hrightBaseError baseErrors rfl
      subst right
      cases spec <;>
        simp [ListResponseResultAlignedEquivalent,
          ResponseValueResultAlignedEquivalent,
          GraphQL.Execution.Result.combine,
          GraphQL.Execution.catchBubbleAsNull, mergeResponse,
          ErrorPresenceEquivalent] at h ⊢
      exact h
  | ok baseResult =>
      cases right <;> cases spec <;>
      simp [ListResponseResultAlignedEquivalent,
        ResponseValueResultAlignedEquivalent,
        GraphQL.Execution.Result.combine,
        GraphQL.Execution.catchBubbleAsNull, mergeResponse,
        ErrorPresenceEquivalent] at h ⊢
      all_goals
        first
        | exact h
        | exact h.2
        | (
            rcases h with ⟨hvalues, herrors⟩
            exact ⟨by simp [hvalues], herrors⟩)

theorem ListResponseResultAlignedEquivalent.zip_cons
    {headPrefix headRight headSpec : Result ResponseValue}
    {tailPrefix tailRight tailSpec : Result (List ResponseValue)}
    (hhead
      : ResponseValueResultAlignedEquivalent
          (GraphQL.Execution.Result.combine mergeResponse headPrefix headRight)
          headSpec)
    (htail
      : ListResponseResultAlignedEquivalent
          (GraphQL.Execution.Result.combine mergeResponseLists tailPrefix tailRight)
          tailSpec)
    : ListResponseResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponseLists
          (GraphQL.Execution.Result.combine List.cons headPrefix tailPrefix)
          (GraphQL.Execution.Result.combine List.cons headRight tailRight))
        (GraphQL.Execution.Result.combine List.cons headSpec tailSpec) := by
  cases headPrefix <;> cases headRight <;> cases headSpec <;>
    cases tailPrefix <;> cases tailRight <;> cases tailSpec <;>
    simp [ResponseValueResultAlignedEquivalent,
      ListResponseResultAlignedEquivalent,
      GraphQL.Execution.Result.combine, mergeResponseLists] at hhead htail ⊢
  all_goals
    try exact ErrorPresenceEquivalent.add_reassociate hhead htail
    try exact ErrorPresenceEquivalent.add_reassociate hhead htail.2
    try exact ErrorPresenceEquivalent.add_reassociate hhead.2 htail
    try
      rcases hhead with ⟨hheadValue, hheadErrors⟩
      rcases htail with ⟨htailValue, htailErrors⟩
      exact
        ⟨⟨hheadValue, htailValue⟩,
          ErrorPresenceEquivalent.add_reassociate hheadErrors htailErrors⟩

def rootSelectionResultData (result : Result (List (Name × ResponseValue)))
    : ResponseValue :=
  match result with
  | .error _errors => .null
  | .ok (fields, _errors) => .object fields

def responseOfRootSelectionResult (result : Result (List (Name × ResponseValue)))
    : GraphQL.Execution.Response :=
  {
    data := rootSelectionResultData result
    errors := resultErrorCount result
  }

def RootSelectionResultDataAndErrorPresenceEquivalent
    (ungrouped spec : Result (List (Name × ResponseValue)))
    : Prop :=
  rootSelectionResultData ungrouped = rootSelectionResultData spec
  ∧ ErrorPresenceEquivalent (resultErrorCount ungrouped) (resultErrorCount spec)

def RootSelectionResultAlignedEquivalent
    (ungrouped spec : Result (List (Name × ResponseValue)))
    : Prop :=
  match ungrouped, spec with
  | .error ungroupedErrors, .error specErrors =>
      ErrorPresenceEquivalent ungroupedErrors specErrors
  | .ok (ungroupedFields, ungroupedErrors), .ok (specFields, specErrors) =>
      ungroupedFields = specFields ∧ ErrorPresenceEquivalent ungroupedErrors specErrors
  | _, _ => False

theorem ResponseValueResultAlignedEquivalent.singleFieldResult
    {ungrouped spec : Result ResponseValue} (responseName : Name)
    : ResponseValueResultAlignedEquivalent ungrouped spec
      -> RootSelectionResultAlignedEquivalent
          (GraphQL.Execution.singleFieldResult responseName ungrouped)
          (GraphQL.Execution.singleFieldResult responseName spec) := by
  intro h
  cases ungrouped <;> cases spec <;>
    simp [ResponseValueResultAlignedEquivalent,
      RootSelectionResultAlignedEquivalent,
      GraphQL.Execution.singleFieldResult] at h ⊢
  · exact h
  · rcases h with ⟨hvalue, herrors⟩
    exact ⟨by simp [hvalue], herrors⟩

theorem RootSelectionResultDataAndErrorPresenceEquivalent.of_eq
    {ungrouped spec : Result (List (Name × ResponseValue))}
    (h : ungrouped = spec)
    : RootSelectionResultDataAndErrorPresenceEquivalent ungrouped spec := by
  subst ungrouped
  exact ⟨rfl, ErrorPresenceEquivalent.refl _⟩

theorem RootSelectionResultAlignedEquivalent.of_eq
    {ungrouped spec : Result (List (Name × ResponseValue))}
    (h : ungrouped = spec)
    : RootSelectionResultAlignedEquivalent ungrouped spec := by
  subst ungrouped
  cases spec with
  | error errors =>
      exact ErrorPresenceEquivalent.refl errors
  | ok result =>
      rcases result with ⟨fields, errors⟩
      exact ⟨rfl, ErrorPresenceEquivalent.refl errors⟩

theorem RootSelectionResultAlignedEquivalent.to_dataAndErrorPresence
    {ungrouped spec : Result (List (Name × ResponseValue))}
    : RootSelectionResultAlignedEquivalent ungrouped spec
      -> RootSelectionResultDataAndErrorPresenceEquivalent ungrouped spec := by
  intro h
  cases ungrouped <;> cases spec <;>
    simp [RootSelectionResultAlignedEquivalent,
      RootSelectionResultDataAndErrorPresenceEquivalent,
      rootSelectionResultData, resultErrorCount] at h ⊢
  · exact h
  · exact h

theorem RootSelectionResultAlignedEquivalent.trans
    {left middle right : Result (List (Name × ResponseValue))}
    : RootSelectionResultAlignedEquivalent left middle
      -> RootSelectionResultAlignedEquivalent middle right
      -> RootSelectionResultAlignedEquivalent left right := by
  intro hleft hmiddle
  cases left <;> cases middle <;> cases right <;>
    simp [RootSelectionResultAlignedEquivalent] at hleft hmiddle ⊢
  · exact ErrorPresenceEquivalent.trans hleft hmiddle
  · rcases hleft with ⟨hleftFields, hleftErrors⟩
    rcases hmiddle with ⟨hmiddleFields, hmiddleErrors⟩
    exact ⟨
      hleftFields.trans hmiddleFields,
      ErrorPresenceEquivalent.trans hleftErrors hmiddleErrors
    ⟩

theorem RootSelectionResultAlignedEquivalent.combine_append
    {ungroupedLeft specLeft ungroupedRight specRight
      : Result (List (Name × ResponseValue))}
    : RootSelectionResultAlignedEquivalent ungroupedLeft specLeft
      -> RootSelectionResultAlignedEquivalent ungroupedRight specRight
      -> RootSelectionResultAlignedEquivalent
          (GraphQL.Execution.Result.combine List.append ungroupedLeft ungroupedRight)
          (GraphQL.Execution.Result.combine List.append specLeft specRight) := by
  intro hleft hright
  cases ungroupedLeft <;> cases specLeft <;>
    cases ungroupedRight <;> cases specRight <;>
    simp [RootSelectionResultAlignedEquivalent,
      GraphQL.Execution.Result.combine] at hleft hright ⊢
  · exact ErrorPresenceEquivalent.add hleft hright
  · rcases hright with ⟨hrightFields, hrightErrors⟩
    exact ErrorPresenceEquivalent.add hleft hrightErrors
  · rcases hleft with ⟨hleftFields, hleftErrors⟩
    exact ErrorPresenceEquivalent.add hleftErrors hright
  · rcases hleft with ⟨hleftFields, hleftErrors⟩
    rcases hright with ⟨hrightFields, hrightErrors⟩
    exact ⟨by simp [hleftFields, hrightFields],
      ErrorPresenceEquivalent.add hleftErrors hrightErrors⟩

theorem RootSelectionResultDataAndErrorPresenceEquivalent.trans
    {left middle right : Result (List (Name × ResponseValue))}
    : RootSelectionResultDataAndErrorPresenceEquivalent left middle
      -> RootSelectionResultDataAndErrorPresenceEquivalent middle right
      -> RootSelectionResultDataAndErrorPresenceEquivalent left right := by
  intro hleft hmiddle
  exact ⟨hleft.1.trans hmiddle.1, ErrorPresenceEquivalent.trans hleft.2 hmiddle.2⟩

theorem responseDataAndErrorPresenceEquivalent_of_rootSelectionResult
    {ungrouped spec : Result (List (Name × ResponseValue))}
    : RootSelectionResultDataAndErrorPresenceEquivalent ungrouped spec
      -> responseDataAndErrorPresenceEquivalent
          (responseOfRootSelectionResult ungrouped)
          (responseOfRootSelectionResult spec) := by
  intro h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem responseDataAndErrorPresenceEquivalent_of_selectionSetResultToResponse
    {ungrouped spec : Result (List (Name × ResponseValue))}
    : RootSelectionResultAlignedEquivalent ungrouped spec
      -> responseDataAndErrorPresenceEquivalent
          (GraphQL.Execution.selectionSetResultToResponse ungrouped)
          (GraphQL.Execution.selectionSetResultToResponse spec) := by
  intro h
  cases ungrouped <;> cases spec <;>
    simp [RootSelectionResultAlignedEquivalent,
      GraphQL.Execution.selectionSetResultToResponse,
      responseDataAndErrorPresenceEquivalent, ErrorPresenceEquivalent] at h ⊢
  all_goals exact h

theorem responseDataAndErrorPresenceEquivalent_of_eq
    {ungrouped spec : GraphQL.Execution.Response}
    (h : ungrouped = spec)
    : responseDataAndErrorPresenceEquivalent ungrouped spec := by
  subst ungrouped
  exact ⟨rfl, fun hzero => hzero, fun hpositive => hpositive⟩

theorem responseDataAndErrorPresenceEquivalent_trans
    {left middle right : GraphQL.Execution.Response}
    : responseDataAndErrorPresenceEquivalent left middle
      -> responseDataAndErrorPresenceEquivalent middle right
      -> responseDataAndErrorPresenceEquivalent left right := by
  intro hleft hmiddle
  rcases hleft with ⟨hleftData, hleftZero, hleftPositive⟩
  rcases hmiddle with ⟨hmiddleData, hmiddleZero, hmiddlePositive⟩
  exact ⟨
    hleftData.trans hmiddleData,
    fun hrightZero => hleftZero (hmiddleZero hrightZero),
    fun hrightPositive => hleftPositive (hmiddlePositive hrightPositive)
  ⟩

def ResponseAbsorbs (base output : ResponseValue) : Prop :=
  mergeResponse base output = output

def ExecutionWindowEquivalent (window : ExecutionWindow ObjectIdentity) : Prop :=
  ResponseResultEquivalent window.ungroupedResult window.specResult

def ExecutionStateEquivalent (state : ExecutionEquivalenceState ObjectIdentity) : Prop :=
  ResponseResultEquivalent state.ungroupedProjectionResult state.specProjectionResult

def PairKeysNodup {α : Type} (fields : List (Name × α)) : Prop :=
  (fields.map Prod.fst).Nodup

theorem PairKeysNodup.tail {α : Type} {head : Name × α} {rest : List (Name × α)}
    : PairKeysNodup (head :: rest) -> PairKeysNodup rest := by
  intro hnodup
  rcases head with ⟨_, _⟩
  unfold PairKeysNodup at hnodup ⊢
  exact (List.nodup_cons.mp hnodup).2

theorem PairKeysNodup.head_not_mem_tail
    {α : Type} {responseName : Name} {value : α}
    {rest : List (Name × α)}
    : PairKeysNodup ((responseName, value) :: rest)
      -> responseName ∉ rest.map Prod.fst := by
  intro hnodup
  unfold PairKeysNodup at hnodup
  exact (List.nodup_cons.mp hnodup).1

theorem PairKeysNodup.append {α : Type} {left right : List (Name × α)}
    : PairKeysNodup left
      -> PairKeysNodup right
      -> (∀ responseName,
            responseName ∈ left.map Prod.fst -> responseName ∉ right.map Prod.fst)
      -> PairKeysNodup (left ++ right) := by
  intro hleft hright hdisjoint
  unfold PairKeysNodup at hleft hright ⊢
  rw [List.map_append]
  exact List.nodup_append.mpr
    ⟨hleft, hright, by
      intro leftName hleftMem rightName hrightMem heq
      exact hdisjoint leftName hleftMem (by simpa [heq] using hrightMem)⟩

theorem executableGroupNamesDisjoint_singleton_tail_of_pairKeysNodup
    {responseName : Name} {fields : List ExecutableField}
    {rest : List (Name × List ExecutableField)}
    : PairKeysNodup ((responseName, fields) :: rest)
      -> NormalForm.executableGroupNamesDisjoint [(responseName, fields)] rest := by
  intro hnodup candidate hleft hright
  have hcandidate : candidate = responseName := by
    simpa using hleft
  subst candidate
  exact PairKeysNodup.head_not_mem_tail hnodup hright

theorem executableGroupNamesNodup_of_pairKeysNodup
    (groups : List (Name × List ExecutableField))
    : PairKeysNodup groups -> NormalForm.executableGroupNamesNodup groups := by
  induction groups with
  | nil =>
      simp [PairKeysNodup, NormalForm.executableGroupNamesNodup]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      intro hnodup
      have hparts :
          responseName ∉ rest.map Prod.fst ∧ PairKeysNodup rest := by
        unfold PairKeysNodup at hnodup ⊢
        exact List.nodup_cons.mp hnodup
      exact ⟨hparts.1, ih hparts.2⟩

theorem PairKeysNodup_of_executableGroupNamesNodup
    (groups : List (Name × List ExecutableField))
    : NormalForm.executableGroupNamesNodup groups -> PairKeysNodup groups := by
  induction groups with
  | nil =>
      simp [PairKeysNodup]
  | cons group rest ih =>
      cases group with
      | mk responseName fields =>
          intro hnodup
          unfold NormalForm.executableGroupNamesNodup at hnodup
          unfold PairKeysNodup
          exact List.nodup_cons.mpr ⟨hnodup.1, ih hnodup.2⟩

inductive ResponseMergeReady : ResponseValue -> Prop where
  | null : ResponseMergeReady .null
  | scalar (value : String) : ResponseMergeReady (.scalar value)
  | object (fields : List (Name × ResponseValue))
    : PairKeysNodup fields
      -> (∀ responseName response,
            (responseName, response) ∈ fields -> ResponseMergeReady response)
      -> ResponseMergeReady (.object fields)
  | list (values : List ResponseValue)
    : (∀ response, response ∈ values -> ResponseMergeReady response)
      -> ResponseMergeReady (.list values)

def MergeResponseFieldsReadySteps
    : List (Name × ResponseValue) -> List (Name × ResponseValue) -> Prop
  | _existing, [] => True
  | existing, (responseName, incoming)::rest =>
      ResponseMergeReady incoming
      ∧ (∀ existingResponse,
          (responseName, existingResponse) ∈ existing
          -> ResponseMergeReady (mergeResponse existingResponse incoming))
      ∧ MergeResponseFieldsReadySteps
          (mergeResponseField responseName incoming existing) rest

def MergeResponseFieldsAbsorbsFrom (base : List (Name × ResponseValue))
    : List (Name × ResponseValue) -> List (Name × ResponseValue) -> Prop
  | current, [] => ResponseAbsorbs (.object base) (.object current)
  | current, (responseName, incoming)::rest =>
      ResponseAbsorbs (.object base)
        (.object (mergeResponseField responseName incoming current))
      ∧ MergeResponseFieldsAbsorbsFrom base
          (mergeResponseField responseName incoming current) rest

def ExecutableFieldsMergeCompatible (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.responseName = later.responseName
    -> first.parentType = later.parentType
        ∧ first.fieldName = later.fieldName
        ∧ first.arguments = later.arguments

def ExecutableFieldsValidationMergeCompatible (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.responseName = later.responseName
    -> first.parentType = later.parentType
        ∧ first.fieldName = later.fieldName
        ∧ Argument.argumentsEquivalent first.arguments later.arguments

def ExecutableFieldsSameParentValidationMergeCompatible (fields : List ExecutableField)
    : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.responseName = later.responseName
    -> first.parentType = later.parentType
    -> first.fieldName = later.fieldName
        ∧ Argument.argumentsEquivalent first.arguments later.arguments

def ExecutableFieldsFieldValidationMergeCompatible (fields : List ExecutableField)
    : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.responseName = later.responseName
    -> first.fieldName = later.fieldName
        ∧ Argument.argumentsEquivalent first.arguments later.arguments

def ExecutableFieldsArgumentsNodup (fields : List ExecutableField) : Prop :=
  ∀ field, field ∈ fields -> (field.arguments.map Argument.name).Nodup

def ExecutableFieldsSameResponseParent (fields : List ExecutableField) : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.responseName = later.responseName
    -> first.parentType = later.parentType

def ExecutableFieldsParent (parentType : Name) (fields : List ExecutableField) : Prop :=
  ∀ field, field ∈ fields -> field.parentType = parentType

def ScopedFieldsValidationMergeCompatible (fields : List FieldMerge.ScopedField) : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.responseName = later.responseName
    -> first.parentType = later.parentType
    -> first.fieldName = later.fieldName
        ∧ Argument.argumentsEquivalent first.arguments later.arguments

def ScopedFieldsSameResponseParent (fields : List FieldMerge.ScopedField) : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.responseName = later.responseName
    -> first.parentType = later.parentType

def ScopedFieldsFieldValidationMergeCompatible (fields : List FieldMerge.ScopedField)
    : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.responseName = later.responseName
    -> first.fieldName = later.fieldName
        ∧ Argument.argumentsEquivalent first.arguments later.arguments

-- Proof-facing strengthening of GraphQL field merge compatibility for the scoped
-- query fragment currently under consideration: every duplicated response key is
-- the same semantic field with equivalent arguments.
def ScopedFieldsNoAliasCollision (fields : List FieldMerge.ScopedField) : Prop :=
  ScopedFieldsFieldValidationMergeCompatible fields

def OperationNoAliasCollision (schema : Schema) (operation : Operation) : Prop :=
  ScopedFieldsNoAliasCollision
    (FieldMerge.collectFields schema (operation.rootType schema) operation.selectionSet)

def ScopedFieldRuntimeApplies
    (schema : Schema) (runtimeType : Name)
    (field : FieldMerge.ScopedField)
    : Prop :=
  schema.typeIncludesObjectBool field.parentType runtimeType = true

def ScopedParentRuntimeApplies (schema : Schema) (runtimeType parentType : Name) : Prop :=
  schema.typeIncludesObjectBool parentType runtimeType = true

theorem ScopedParentRuntimeApplies.of_rootSourceAppliesBool
    {ObjectIdentity : Type}
    (schema : Schema) (operation : Operation)
    (runtimeType : Name) (identity : ObjectIdentity)
    : rootSourceAppliesBool schema operation (.object runtimeType identity) = true
      -> ScopedParentRuntimeApplies schema runtimeType (operation.rootType schema) := by
  intro hroot
  simpa [ScopedParentRuntimeApplies, rootSourceAppliesBool, runtimeObjectType?]
    using hroot

theorem ScopedParentRuntimeApplies.of_typeIncludesObjectBool
    (schema : Schema) (runtimeType parentType : Name)
    : schema.typeIncludesObjectBool parentType runtimeType = true
      -> ScopedParentRuntimeApplies schema runtimeType parentType := by
  intro hincludes
  exact hincludes

theorem ScopedParentRuntimeApplies.runtimeObjectType
    (schema : Schema) {runtimeType parentType : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> ScopedParentRuntimeApplies schema runtimeType parentType
      -> schema.objectType runtimeType := by
  intro hschema hparentRuntime
  exact SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
    parentType runtimeType (List.contains_iff_mem.mp hparentRuntime)

theorem ScopedParentRuntimeApplies.runtimeSelf
    (schema : Schema) {runtimeType parentType : Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> ScopedParentRuntimeApplies schema runtimeType parentType
      -> schema.typeIncludesObjectBool runtimeType runtimeType = true := by
  intro hschema hparentRuntime
  exact NormalForm.object_typeIncludesObjectBool_self schema
    (ScopedParentRuntimeApplies.runtimeObjectType schema hschema
      hparentRuntime)

theorem ScopedFieldsNoAliasCollision.fieldCompatible
    (fields : List FieldMerge.ScopedField)
    : ScopedFieldsNoAliasCollision fields
      -> ScopedFieldsFieldValidationMergeCompatible fields := by
  intro hnoAlias
  exact hnoAlias

theorem ScopedFieldsNoAliasCollision.prefix_selection
    (schema : Schema) (parentType : Name)
    (selectionSet prefixSelections suffix : List Selection)
    (selection : Selection)
    : ScopedFieldsNoAliasCollision
        (FieldMerge.collectFields schema parentType selectionSet)
      -> selectionSet = prefixSelections ++ selection :: suffix
      -> ScopedFieldsNoAliasCollision
          (FieldMerge.collectFields schema parentType [selection]) := by
  intro hnoAlias hselectionSet
  unfold ScopedFieldsNoAliasCollision
  change ScopedFieldsFieldValidationMergeCompatible
    (FieldMerge.collectFields schema parentType selectionSet) at hnoAlias
  unfold ScopedFieldsFieldValidationMergeCompatible at hnoAlias ⊢
  intro first later hfirst hlater hresponse
  apply hnoAlias first later
  · rw [hselectionSet]
    apply GraphQL.NormalForm.fieldMerge_collectFields_append_right_mem
      schema parentType prefixSelections (selection :: suffix)
    apply GraphQL.NormalForm.fieldMerge_collectFields_append_left_mem
      schema parentType [selection] suffix
    exact hfirst
  · rw [hselectionSet]
    apply GraphQL.NormalForm.fieldMerge_collectFields_append_right_mem
      schema parentType prefixSelections (selection :: suffix)
    apply GraphQL.NormalForm.fieldMerge_collectFields_append_left_mem
      schema parentType [selection] suffix
    exact hlater
  · exact hresponse

theorem OperationNoAliasCollision.prefix_selection
    (schema : Schema) (operation : Operation)
    (prefixSelections suffix : List Selection) (selection : Selection)
    : OperationNoAliasCollision schema operation
      -> operation.selectionSet = prefixSelections ++ selection :: suffix
      -> ScopedFieldsNoAliasCollision
          (FieldMerge.collectFields schema (operation.rootType schema) [selection]) := by
  intro hnoAlias hselectionSet
  exact ScopedFieldsNoAliasCollision.prefix_selection schema (operation.rootType schema)
    operation.selectionSet prefixSelections suffix selection hnoAlias
    hselectionSet

structure ValidOperationPrefixSelectionState
    (schema : Schema) (operation : Operation)
    (prefixSelections : List Selection) (selection : Selection)
    (suffix : List Selection)
    : Prop where
  selectionValid
    : Validation.selectionValid schema operation.variableDefinitions
        (operation.rootType schema) selection
  fieldsInSetCanMerge
    : FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema) [selection]
  noAlias
    : ScopedFieldsNoAliasCollision
        (FieldMerge.collectFields schema (operation.rootType schema) [selection])

theorem ValidOperationPrefixSelectionState.of_valid_noAlias
    (schema : Schema) (operation : Operation)
    (prefixSelections suffix : List Selection) (selection : Selection)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hnoAlias : OperationNoAliasCollision schema operation)
    (hselectionSet : operation.selectionSet = prefixSelections ++ selection :: suffix)
    : ValidOperationPrefixSelectionState schema operation prefixSelections
        selection suffix := by
  exact {
    selectionValid := by
      have hselSet : Validation.selectionSetValid schema operation.variableDefinitions (operation.rootType schema) (prefixSelections ++ selection :: suffix) := by
        rw [← hselectionSet]
        exact Validation.operationDefinitionValid_selectionSetValid hvalid
      have hright : Validation.selectionSetValid schema operation.variableDefinitions (operation.rootType schema) (selection :: suffix) :=
        Validation.selectionSetValid_append_right hselSet
      exact (by
        simp [Validation.selectionSetValid] at hright
        exact hright.1)
    fieldsInSetCanMerge := by
      have hmergeAll : FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema) (prefixSelections ++ selection :: suffix) := by
        rw [← hselectionSet]
        exact Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
      have hright : FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema) (selection :: suffix) :=
        GraphQL.NormalForm.fieldsInSetCanMerge_append_right schema (operation.rootType schema) prefixSelections (selection :: suffix) hmergeAll
      exact GraphQL.NormalForm.fieldsInSetCanMerge_append_left schema (operation.rootType schema) [selection] suffix hright
    noAlias :=
      OperationNoAliasCollision.prefix_selection schema operation
        prefixSelections suffix selection hnoAlias hselectionSet
  }

theorem ValidOperationPrefixSelectionState.field_lookup
    {schema : Schema} {operation : Operation}
    {prefixSelections suffix : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    : ValidOperationPrefixSelectionState schema operation prefixSelections
        (.field responseName fieldName arguments directives selectionSet)
        suffix
      -> ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) fieldName = some fieldDefinition
          ∧ Validation.argumentsValid schema fieldDefinition.arguments
              operation.variableDefinitions arguments
          ∧ Validation.fieldSelectionSetValid schema
              operation.variableDefinitions fieldDefinition selectionSet := by
  intro hstate
  exact Validation.selectionValid_field_lookup hstate.selectionValid

theorem ValidOperationPrefixSelectionState.inline_none_selectionSetValid
    {schema : Schema} {operation : Operation}
    {prefixSelections suffix : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    : ValidOperationPrefixSelectionState schema operation prefixSelections
        (.inlineFragment none directives selectionSet) suffix
      -> Validation.selectionSetValid schema operation.variableDefinitions
          (operation.rootType schema) selectionSet := by
  intro hstate
  exact
    Validation.selectionValid_inlineFragment_none_selectionSetValid
      hstate.selectionValid

theorem ValidOperationPrefixSelectionState.inline_some_selectionSetValid
    {schema : Schema} {operation : Operation}
    {prefixSelections suffix : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    : ValidOperationPrefixSelectionState schema operation prefixSelections
        (.inlineFragment (some typeCondition) directives selectionSet) suffix
      -> Validation.selectionSetValid schema operation.variableDefinitions
          typeCondition selectionSet := by
  intro hstate
  exact
    Validation.selectionValid_inlineFragment_some_selectionSetValid
      hstate.selectionValid

theorem ScopedFieldRuntimeApplies.mergeIdentityCondition
    (schema : Schema) (runtimeType : Name)
    (first later : FieldMerge.ScopedField)
    : ScopedFieldRuntimeApplies schema runtimeType first
      -> ScopedFieldRuntimeApplies schema runtimeType later
      -> first.parentType = later.parentType
          ∨ ¬ schema.objectType first.parentType
          ∨ ¬ schema.objectType later.parentType := by
  intro hfirst hlater
  by_cases hfirstObject : schema.objectType first.parentType
  · by_cases hlaterObject : schema.objectType later.parentType
    · have hfirstRuntime :
          runtimeType = first.parentType :=
        object_typeIncludesObjectBool_eq_self schema hfirstObject
          hfirst
      have hlaterRuntime :
          runtimeType = later.parentType :=
        object_typeIncludesObjectBool_eq_self schema hlaterObject
          hlater
      exact Or.inl (hfirstRuntime.symm.trans hlaterRuntime)
    · exact Or.inr (Or.inr hlaterObject)
  · exact Or.inr (Or.inl hfirstObject)

def ScopedFieldMatchesExecutable
    (scopedField : FieldMerge.ScopedField)
    (executableField : ExecutableField)
    : Prop :=
  scopedField.parentType = executableField.parentType
  ∧ scopedField.responseName = executableField.responseName
  ∧ scopedField.fieldName = executableField.fieldName
  ∧ scopedField.arguments = executableField.arguments
  ∧ scopedField.selectionSet = executableField.selectionSet

def ScopedFieldMatchesExecutableIdentity
    (scopedField : FieldMerge.ScopedField)
    (executableField : ExecutableField)
    : Prop :=
  scopedField.responseName = executableField.responseName
  ∧ scopedField.fieldName = executableField.fieldName
  ∧ scopedField.arguments = executableField.arguments
  ∧ scopedField.selectionSet = executableField.selectionSet

def ExecutableFieldsScopedBy
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : Prop :=
  ∀ field,
    field ∈ fields
    -> ∃ scopedField,
        scopedField ∈ scopedFields ∧ ScopedFieldMatchesExecutable scopedField field

def ExecutableFieldsIdentityScopedBy
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : Prop :=
  ∀ field,
    field ∈ fields
    -> ∃ scopedField,
        scopedField ∈ scopedFields
        ∧ ScopedFieldMatchesExecutableIdentity scopedField field

def ExecutableFieldsRuntimeScopedBy
    (schema : Schema) (runtimeType : Name)
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : Prop :=
  ∀ field,
    field ∈ fields
    -> ∃ scopedField,
        scopedField ∈ scopedFields
        ∧ ScopedFieldMatchesExecutableIdentity scopedField field
        ∧ ScopedFieldRuntimeApplies schema runtimeType scopedField

theorem ScopedFieldMatchesExecutable.identity
    {scopedField : FieldMerge.ScopedField}
    {executableField : ExecutableField}
    : ScopedFieldMatchesExecutable scopedField executableField
      -> ScopedFieldMatchesExecutableIdentity scopedField executableField := by
  intro hmatch
  rcases hmatch with
    ⟨_hparent, hresponseName, hfieldName, harguments, hselectionSet⟩
  exact ⟨hresponseName, hfieldName, harguments, hselectionSet⟩

theorem ExecutableFieldsScopedBy.identity
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : ExecutableFieldsScopedBy scopedFields fields
      -> ExecutableFieldsIdentityScopedBy scopedFields fields := by
  intro hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch⟩
  exact ⟨scopedField, hscopedMem, ScopedFieldMatchesExecutable.identity hmatch⟩

theorem ExecutableFieldsRuntimeScopedBy.identityScopedBy
    (schema : Schema) (runtimeType : Name)
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : ExecutableFieldsRuntimeScopedBy schema runtimeType scopedFields fields
      -> ExecutableFieldsIdentityScopedBy scopedFields fields := by
  intro hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch, _hruntime⟩
  exact ⟨scopedField, hscopedMem, hmatch⟩

theorem ExecutableFieldsRuntimeScopedBy.mono
    (schema : Schema) (runtimeType : Name)
    (scopedFields : List FieldMerge.ScopedField)
    (source target : List ExecutableField)
    : (∀ field, field ∈ target -> field ∈ source)
      -> ExecutableFieldsRuntimeScopedBy schema runtimeType scopedFields source
      -> ExecutableFieldsRuntimeScopedBy schema runtimeType scopedFields target := by
  intro hsubset hscoped field hfield
  exact hscoped field (hsubset field hfield)

def ExecutableFieldsResolveStable
    {ObjectIdentity : Type} (schema : Schema)
    (resolvers : Resolvers ObjectIdentity) (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity) (fields : List ExecutableField)
    : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.responseName = later.responseName
    -> resolveFieldValueByName schema resolvers variableValues first.parentType
          first.fieldName first.arguments source
        = resolveFieldValueByName schema resolvers variableValues later.parentType
            later.fieldName later.arguments source

def ResolversRespectArgumentEquivalence
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    : Prop :=
  ∀ parentType fieldName firstArguments laterArguments,
    Argument.argumentsEquivalent firstArguments laterArguments
    -> resolveFieldValueByName schema resolvers variableValues parentType fieldName
          firstArguments source
        = resolveFieldValueByName schema resolvers variableValues parentType fieldName
            laterArguments source

def ResolversRespectValidArgumentEquivalence
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    : Prop :=
  ∀ parentType fieldName firstArguments laterArguments,
    (firstArguments.map Argument.name).Nodup
    -> (laterArguments.map Argument.name).Nodup
    -> Argument.argumentsEquivalent firstArguments laterArguments
    -> resolveFieldValueByName schema resolvers variableValues parentType fieldName
          firstArguments source
        = resolveFieldValueByName schema resolvers variableValues parentType fieldName
            laterArguments source

def ResolversRespectFieldAndArgumentEquivalence
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    : Prop :=
  ∀ firstParent laterParent fieldName firstArguments laterArguments,
    Argument.argumentsEquivalent firstArguments laterArguments
    -> resolveFieldValueByName schema resolvers variableValues firstParent fieldName
          firstArguments source
        = resolveFieldValueByName schema resolvers variableValues laterParent fieldName
            laterArguments source

def ResolversRespectValidFieldAndArgumentEquivalence
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    : Prop :=
  ∀ firstParent laterParent fieldName firstArguments laterArguments,
    (firstArguments.map Argument.name).Nodup
    -> (laterArguments.map Argument.name).Nodup
    -> Argument.argumentsEquivalent firstArguments laterArguments
    -> resolveFieldValueByName schema resolvers variableValues firstParent fieldName
          firstArguments source
        = resolveFieldValueByName schema resolvers variableValues laterParent fieldName
            laterArguments source

theorem Resolvers.respectValidArgumentEquivalence
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    : ResolversRespectValidArgumentEquivalence schema resolvers variableValues
        source := by
  intro parentType fieldName firstArguments laterArguments hfirstNodup
    hlaterNodup hequivalent
  simp only [resolveFieldValueByName]
  split
  · rfl
  · simp only [resolveFieldValue]
    apply resolvers.resolve_argumentsEquivalent
    exact coerceArgumentValues_equivalent_of_equivalent schema variableValues _
      hfirstNodup hlaterNodup hequivalent

theorem ExecutableFieldsResolveStable.tail
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (fields : List ExecutableField)
    : ExecutableFieldsResolveStable schema resolvers variableValues source
        (field :: fields)
      -> ExecutableFieldsResolveStable schema resolvers variableValues source fields := by
  intro hstable first later hfirst hlater hresponse
  exact hstable first later (by simp [hfirst]) (by simp [hlater]) hresponse

theorem ExecutableFieldsResolveStable.head_eq_later
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity) (field later : ExecutableField)
    (fields : List ExecutableField)
    : ExecutableFieldsResolveStable schema resolvers variableValues source
        (field :: fields)
      -> later ∈ fields
      -> field.responseName = later.responseName
      -> resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source
          = resolveFieldValueByName schema resolvers variableValues later.parentType
              later.fieldName later.arguments source := by
  intro hstable hlater hresponse
  exact hstable field later (by simp) (by simp [hlater]) hresponse

structure ExecutedResponseFieldAt
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (source : ResolverValue ObjectIdentity) (output : ResponseValue)
    (field : ExecutableField) (response : ResponseValue) where
  previous : ResponseValue
  resolved : ResolverValue ObjectIdentity
  previous_eq
    : previous = (responseObjectField? field.responseName output).getD (.object [])
  resolved_eq
    : resolved
      = resolveFieldValueByName schema resolvers variableValues field.parentType
          field.fieldName field.arguments source
  response_eq
    : response
      = completeValue schema resolvers variableValues completionDepth
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          field.selectionSet resolved previous

def executableFieldSelection (field : ExecutableField) : Selection :=
  .field field.responseName field.fieldName field.arguments [] field.selectionSet

def executableFieldSelections (fields : List ExecutableField) : List Selection :=
  fields.map executableFieldSelection

theorem selectionDirectivesAllowBool_empty (variableValues : VariableValues)
    : selectionDirectivesAllowBool variableValues [] = true := by
  rfl

theorem collectSelection_executableFieldSelection
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    : GraphQL.Execution.collectSelection schema variableValues parentType source
        (executableFieldSelection field)
      = [(field.responseName, [{ field with parentType := parentType }])] := by
  simp [executableFieldSelection, GraphQL.Execution.collectSelection,
    selectionDirectivesAllowBool_empty]

theorem collectSelection_executableFieldSelection_of_parent
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    : field.parentType = parentType
      -> GraphQL.Execution.collectSelection schema variableValues parentType source
            (executableFieldSelection field)
          = [(field.responseName, [field])] := by
  intro hparent
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp at hparent ⊢
      subst fieldParent
      simp [collectSelection_executableFieldSelection]

theorem collectFields_executableFieldSelections_same_group
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name)
    : ∀ fields : List ExecutableField,
        (∀ field, field ∈ fields -> field.responseName = responseName)
        -> (∀ field, field ∈ fields -> field.parentType = parentType)
        -> GraphQL.Execution.collectFields schema variableValues parentType source
              (executableFieldSelections fields)
            = match fields with
              | [] => []
              | _field :: _rest => [(responseName, fields)]
  | [], _hresponse, _hparent => by
      simp [executableFieldSelections, GraphQL.Execution.collectFields]
  | field :: rest, hresponse, hparent => by
      have hfieldResponse : field.responseName = responseName :=
        hresponse field (by simp)
      have hfieldParent : field.parentType = parentType :=
        hparent field (by simp)
      have hrestResponse :
          ∀ restField, restField ∈ rest ->
            restField.responseName = responseName := by
        intro restField hmem
        exact hresponse restField (by simp [hmem])
      have hrestParent :
          ∀ restField, restField ∈ rest ->
            restField.parentType = parentType := by
        intro restField hmem
        exact hparent restField (by simp [hmem])
      cases rest with
      | nil =>
          simp [executableFieldSelections, GraphQL.Execution.collectFields,
            collectSelection_executableFieldSelection_of_parent schema
              variableValues parentType source field hfieldParent,
            GraphQL.Execution.mergeExecutableGroups, hfieldResponse]
      | cons next restTail =>
          have hrestCollect :=
            collectFields_executableFieldSelections_same_group schema
              variableValues parentType source responseName (next :: restTail)
              hrestResponse hrestParent
          change
            GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source (executableFieldSelection field))
              (GraphQL.Execution.collectFields schema variableValues parentType
                source (executableFieldSelections (next :: restTail))) =
            [(responseName, field :: next :: restTail)]
          rw [collectSelection_executableFieldSelection_of_parent schema
            variableValues parentType source field hfieldParent, hrestCollect]
          simp [GraphQL.Execution.mergeExecutableGroups,
            GraphQL.Execution.addExecutableGroup, hfieldResponse]

theorem specExecuteRootSelectionSet_executableFieldSelections_same_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate, candidate ∈ field :: fields -> candidate.parentType = parentType)
    : GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (executableFieldSelections (field :: fields))
      = GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          depth source [(responseName, field :: fields)] := by
  simp [GraphQL.Execution.executeRootSelectionSet,
    collectFields_executableFieldSelections_same_group schema variableValues
      parentType source responseName (field :: fields) hresponse hparent]

theorem ResolversRespectFieldAndArgumentEquivalence.to_valid
    {ObjectIdentity : Type} {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues}
    {source : ResolverValue ObjectIdentity}
    : ResolversRespectFieldAndArgumentEquivalence schema resolvers variableValues source
      -> ResolversRespectValidFieldAndArgumentEquivalence schema resolvers variableValues
          source := by
  intro hrespect firstParent laterParent fieldName firstArguments
    laterArguments _hfirstNodup _hlaterNodup hequivalent
  exact hrespect firstParent laterParent fieldName firstArguments
    laterArguments hequivalent

def CollectedGroupsMergeCompatible
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> ExecutableFieldsMergeCompatible fields
        ∧ ExecutableFieldsResolveStable schema resolvers variableValues source fields

def CollectedGroupsSameResponseParent (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups -> ExecutableFieldsSameResponseParent fields

def CollectedGroupsParent
    (parentType : Name)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups -> ExecutableFieldsParent parentType fields

def ExecutableFieldsResponseName (responseName : Name) (fields : List ExecutableField)
    : Prop :=
  ∀ field, field ∈ fields -> field.responseName = responseName

def CollectedGroupsResponseName (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups -> ExecutableFieldsResponseName responseName fields

def CollectedGroupsFieldsNonempty (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields, (responseName, fields) ∈ groups -> fields ≠ []

theorem CollectedGroupsFieldsNonempty_nil : CollectedGroupsFieldsNonempty [] := by
  intro _responseName _fields hmem
  simp at hmem

theorem CollectedGroupsFieldsNonempty_singleton
    (responseName : Name) (fields : List ExecutableField)
    : fields ≠ [] -> CollectedGroupsFieldsNonempty [(responseName, fields)] := by
  intro hfields groupResponseName groupFields hmem
  have hgroup :
      (groupResponseName, groupFields) = (responseName, fields) := by
    simpa using hmem
  cases hgroup
  exact hfields

theorem CollectedGroupsFieldsNonempty_tail
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)}
    : CollectedGroupsFieldsNonempty (group :: groups)
      -> CollectedGroupsFieldsNonempty groups := by
  intro hgroups responseName fields hmem
  exact hgroups responseName fields (by simp [hmem])

theorem CollectedGroupsFieldsNonempty_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : group.snd ≠ []
      -> CollectedGroupsFieldsNonempty groups
      -> CollectedGroupsFieldsNonempty
          (GraphQL.Execution.addExecutableGroup group groups) := by
  rcases group with ⟨groupName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      simpa [GraphQL.Execution.addExecutableGroup] using
        CollectedGroupsFieldsNonempty_singleton groupName groupFields hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · have hcurrentNonempty : currentFields ≠ [] :=
          hgroups currentName currentFields (by simp)
        have happendNonempty : currentFields ++ groupFields ≠ [] := by
          cases currentFields with
          | nil => exact False.elim (hcurrentNonempty rfl)
          | cons _ _ => simp
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hname] at hmem
        rcases hmem with hhead | htail
        · have hfields :
              fields = currentFields ++ groupFields := by
            simpa using hhead.2
          subst fields
          exact happendNonempty
        · exact hgroups responseName fields (by simp [htail])
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hfalse] at hmem
        rcases hmem with hhead | htail
        · have hfields : fields = currentFields := by
            simpa using hhead.2
          subst fields
          exact hgroups currentName currentFields (by simp)
        · exact ih (CollectedGroupsFieldsNonempty_tail hgroups)
            responseName fields htail

theorem CollectedGroupsFieldsNonempty_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    : CollectedGroupsFieldsNonempty left
      -> CollectedGroupsFieldsNonempty right
      -> CollectedGroupsFieldsNonempty
          (GraphQL.Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [GraphQL.Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      exact ih (GraphQL.Execution.addExecutableGroup group left)
        (CollectedGroupsFieldsNonempty_addExecutableGroup group left
          (hright group.fst group.snd (by simp)) hleft)
        (CollectedGroupsFieldsNonempty_tail hright)

theorem ExecutableFieldsParent.sameResponseParent
    (parentType : Name) (fields : List ExecutableField)
    : ExecutableFieldsParent parentType fields
      -> ExecutableFieldsSameResponseParent fields := by
  intro hparent first later hfirst hlater _hresponse
  rw [hparent first hfirst, hparent later hlater]

theorem CollectedGroupsParent.sameResponseParent
    (parentType : Name) (groups : List (Name × List ExecutableField))
    : CollectedGroupsParent parentType groups
      -> CollectedGroupsSameResponseParent groups := by
  intro hparent responseName fields hmem
  exact ExecutableFieldsParent.sameResponseParent parentType fields
    (hparent responseName fields hmem)

theorem ExecutableFieldsResponseName_singleton
    (responseName : Name) (field : ExecutableField)
    : field.responseName = responseName
      -> ExecutableFieldsResponseName responseName [field] := by
  intro hfield candidate hmem
  have hcandidate : candidate = field := by
    simpa using hmem
  subst candidate
  exact hfield

theorem ExecutableFieldsResponseName_append
    (responseName : Name) (left right : List ExecutableField)
    : ExecutableFieldsResponseName responseName left
      -> ExecutableFieldsResponseName responseName right
      -> ExecutableFieldsResponseName responseName (left ++ right) := by
  intro hleft hright field hmem
  rcases List.mem_append.mp hmem with hfield | hfield
  · exact hleft field hfield
  · exact hright field hfield

theorem CollectedGroupsResponseName_nil : CollectedGroupsResponseName [] := by
  intro _responseName _fields hmem
  simp at hmem

theorem CollectedGroupsResponseName_singleton
    (responseName : Name) (fields : List ExecutableField)
    : ExecutableFieldsResponseName responseName fields
      -> CollectedGroupsResponseName [(responseName, fields)] := by
  intro hfields groupResponseName groupFields hmem
  have hpair :
      (groupResponseName, groupFields) = (responseName, fields) := by
    simpa using hmem
  cases hpair
  exact hfields

theorem CollectedGroupsResponseName_tail
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)}
    : CollectedGroupsResponseName (group :: groups)
      -> CollectedGroupsResponseName groups := by
  intro hgroups responseName fields hmem
  exact hgroups responseName fields (by simp [hmem])

theorem CollectedGroupsResponseName_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : ExecutableFieldsResponseName group.fst group.snd
      -> CollectedGroupsResponseName groups
      -> CollectedGroupsResponseName
          (GraphQL.Execution.addExecutableGroup group groups) := by
  rcases group with ⟨groupName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro responseName fields hmem
      simp [GraphQL.Execution.addExecutableGroup] at hmem
      rcases hmem with ⟨hresponseName, hfields⟩
      cases hresponseName
      cases hfields
      exact hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · have hcurrent : currentName = groupName := beq_iff_eq.mp hname
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hname] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨hresponseName, hfields⟩
          cases hresponseName
          cases hfields
          exact ExecutableFieldsResponseName_append currentName currentFields
            groupFields
            (hgroups currentName currentFields (by simp))
            (by simpa [hcurrent] using hgroup)
        · exact hgroups responseName fields (by simp [htail])
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hfalse] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨hresponseName, hfields⟩
          cases hresponseName
          cases hfields
          exact hgroups currentName currentFields (by simp)
        · exact ih (CollectedGroupsResponseName_tail hgroups)
            responseName fields htail

theorem CollectedGroupsResponseName_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    : CollectedGroupsResponseName left
      -> CollectedGroupsResponseName right
      -> CollectedGroupsResponseName
          (GraphQL.Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [GraphQL.Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      simp [GraphQL.Execution.mergeExecutableGroups]
      exact ih (GraphQL.Execution.addExecutableGroup group left)
        (CollectedGroupsResponseName_addExecutableGroup group left
          (hright group.fst group.snd (by simp)) hleft)
        (CollectedGroupsResponseName_tail hright)

theorem ExecutableFieldsParent_singleton (parentType : Name) (field : ExecutableField)
    : field.parentType = parentType -> ExecutableFieldsParent parentType [field] := by
  intro hfield candidate hmem
  have hcandidate : candidate = field := by
    simpa using hmem
  subst candidate
  exact hfield

theorem ExecutableFieldsParent_append
    (parentType : Name) (left right : List ExecutableField)
    : ExecutableFieldsParent parentType left
      -> ExecutableFieldsParent parentType right
      -> ExecutableFieldsParent parentType (left ++ right) := by
  intro hleft hright field hmem
  rcases List.mem_append.mp hmem with hfield | hfield
  · exact hleft field hfield
  · exact hright field hfield

theorem CollectedGroupsParent_nil (parentType : Name)
    : CollectedGroupsParent parentType [] := by
  intro _responseName _fields hmem
  simp at hmem

theorem CollectedGroupsParent_singleton
    (parentType responseName : Name) (fields : List ExecutableField)
    : ExecutableFieldsParent parentType fields
      -> CollectedGroupsParent parentType [(responseName, fields)] := by
  intro hfields groupResponseName groupFields hmem
  have hpair :
      (groupResponseName, groupFields) = (responseName, fields) := by
    simpa using hmem
  cases hpair
  exact hfields

theorem CollectedGroupsParent_tail
    {parentType : Name}
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)}
    : CollectedGroupsParent parentType (group :: groups)
      -> CollectedGroupsParent parentType groups := by
  intro hgroups responseName fields hmem
  exact hgroups responseName fields (by simp [hmem])

theorem CollectedGroupsParent_addExecutableGroup
    (parentType : Name)
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : ExecutableFieldsParent parentType group.snd
      -> CollectedGroupsParent parentType groups
      -> CollectedGroupsParent parentType
          (GraphQL.Execution.addExecutableGroup group groups) := by
  rcases group with ⟨groupName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro responseName fields hmem
      simp [GraphQL.Execution.addExecutableGroup] at hmem
      rcases hmem with ⟨_hresponseName, hfields⟩
      cases hfields
      exact hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hname] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨_hresponseName, hfields⟩
          cases hfields
          exact ExecutableFieldsParent_append parentType currentFields
            groupFields
            (hgroups currentName currentFields (by simp))
            hgroup
        · exact hgroups responseName fields (by simp [htail])
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hfalse] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨_hresponseName, hfields⟩
          cases hfields
          exact hgroups currentName currentFields (by simp)
        · exact ih (CollectedGroupsParent_tail hgroups)
            responseName fields htail

theorem CollectedGroupsParent_mergeExecutableGroups
    (parentType : Name)
    (left right : List (Name × List ExecutableField))
    : CollectedGroupsParent parentType left
      -> CollectedGroupsParent parentType right
      -> CollectedGroupsParent parentType
          (GraphQL.Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [GraphQL.Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [GraphQL.Execution.mergeExecutableGroups]
      exact ih (GraphQL.Execution.addExecutableGroup (responseName, fields) left)
        (CollectedGroupsParent_addExecutableGroup parentType
          (responseName, fields) left (hright responseName fields (by simp))
          hleft)
        (CollectedGroupsParent_tail hright)

mutual
  theorem collectSelection_parent
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selection : Selection)
      : CollectedGroupsParent parentType
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsParent_singleton parentType responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }]
            (ExecutableFieldsParent_singleton parentType
              {
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              } rfl)
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsParent_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact collectFields_parent schema variableValues parentType source
                selectionSet
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsParent_nil]
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact collectFields_parent schema variableValues parentType
                  source selectionSet
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsParent_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsParent_nil]

  theorem collectFields_parent
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selectionSet : List Selection)
      : CollectedGroupsParent parentType
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, CollectedGroupsParent_nil]
    | cons selection rest =>
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsParent_mergeExecutableGroups parentType
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (collectSelection_parent schema variableValues parentType source
            selection)
          (collectFields_parent schema variableValues parentType source rest)
end

mutual
  theorem collectSelection_responseName
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selection : Selection)
      : CollectedGroupsResponseName
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsResponseName_singleton responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }]
            (ExecutableFieldsResponseName_singleton responseName
              {
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              } rfl)
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsResponseName_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact collectFields_responseName schema variableValues parentType
                source selectionSet
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsResponseName_nil]
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact collectFields_responseName schema variableValues
                  parentType source selectionSet
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsResponseName_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsResponseName_nil]

  theorem collectFields_responseName
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selectionSet : List Selection)
      : CollectedGroupsResponseName
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, CollectedGroupsResponseName_nil]
    | cons selection rest =>
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsResponseName_mergeExecutableGroups
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (collectSelection_responseName schema variableValues parentType source
            selection)
          (collectFields_responseName schema variableValues parentType source
            rest)
end

mutual
  theorem collectSelection_fieldsNonempty
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selection : Selection)
      : CollectedGroupsFieldsNonempty
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsFieldsNonempty_singleton responseName
            [{ parentType := parentType
               responseName := responseName
               fieldName := fieldName
               arguments := arguments
               selectionSet := selectionSet }]
            (by simp)
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsFieldsNonempty_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact collectFields_fieldsNonempty schema variableValues
                parentType source selectionSet
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsFieldsNonempty_nil]
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact collectFields_fieldsNonempty schema variableValues
                  parentType source selectionSet
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsFieldsNonempty_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsFieldsNonempty_nil]

  theorem collectFields_fieldsNonempty
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selectionSet : List Selection)
      : CollectedGroupsFieldsNonempty
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields,
          CollectedGroupsFieldsNonempty_nil]
    | cons selection rest =>
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsFieldsNonempty_mergeExecutableGroups
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (collectSelection_fieldsNonempty schema variableValues parentType
            source selection)
          (collectFields_fieldsNonempty schema variableValues parentType source
            rest)
end

theorem collectFields_sameResponseParent
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : CollectedGroupsSameResponseParent
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) :=
  CollectedGroupsParent.sameResponseParent parentType
    (GraphQL.Execution.collectFields schema variableValues parentType source selectionSet)
    (collectFields_parent schema variableValues parentType source selectionSet)

def CollectedGroupsValidationMergeCompatible (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> ExecutableFieldsSameParentValidationMergeCompatible fields

def CollectedGroupsFieldValidationMergeCompatible
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> ExecutableFieldsFieldValidationMergeCompatible fields

end Eager

open GraphQL.Execution
open Eager

def cancelingRootSelectionAppend (left right : Result (List (Name × ResponseValue)))
    : Result (List (Name × ResponseValue)) :=
  match left with
  | .error errors => .error errors
  | .ok _ok => GraphQL.Execution.Result.combine List.append left right

def cancelingVisitResultAppend (left right : ResponseValue × VisitStatus)
    : ResponseValue × VisitStatus :=
  match left.snd with
  | .error errors => (left.fst, .error errors)
  | .ok _ok => (right.fst, combineVisitStatus left.snd right.snd)

@[simp]
theorem cancelingVisitResultAppend_error_left
    (value : ResponseValue) (errors : Nat)
    (right : ResponseValue × VisitStatus)
    : cancelingVisitResultAppend (value, .error errors) right
      = (value, .error errors) := by
  rfl

@[simp]
theorem cancelingVisitResultAppend_visitOk_left
    (value : ResponseValue) (right : ResponseValue × VisitStatus)
    : cancelingVisitResultAppend (value, visitOk) right = right := by
  rcases right with ⟨rightValue, rightStatus⟩
  cases rightStatus <;>
    simp [cancelingVisitResultAppend, combineVisitStatus, visitOk,
      GraphQL.Execution.Result.combine]

theorem Eager.RootSelectionResultAlignedEquivalent.canceling_combine_append
    {ungroupedLeft specLeft ungroupedRight specRight
      : Result (List (Name × ResponseValue))}
    (hleftPositive : ∀ errors, ungroupedLeft = .error errors -> 0 < errors)
    : RootSelectionResultAlignedEquivalent ungroupedLeft specLeft
      -> RootSelectionResultAlignedEquivalent ungroupedRight specRight
      -> RootSelectionResultAlignedEquivalent
          (cancelingRootSelectionAppend ungroupedLeft ungroupedRight)
          (GraphQL.Execution.Result.combine List.append specLeft specRight) := by
  intro hleft hright
  cases ungroupedLeft with
  | error ungroupedErrors =>
      have hungroupedPositive : 0 < ungroupedErrors :=
        hleftPositive ungroupedErrors rfl
      cases specLeft with
      | error specLeftErrors =>
          have hleftErrors :
              ErrorPresenceEquivalent ungroupedErrors specLeftErrors := by
            simpa [RootSelectionResultAlignedEquivalent] using hleft
          cases specRight with
          | error specRightErrors =>
              simpa [RootSelectionResultAlignedEquivalent,
                cancelingRootSelectionAppend,
                GraphQL.Execution.Result.combine] using
                ErrorPresenceEquivalent.add_spec_right_of_ungrouped_pos
                  hungroupedPositive hleftErrors
          | ok specRightResult =>
              rcases specRightResult with ⟨specRightFields, specRightErrors⟩
              simpa [RootSelectionResultAlignedEquivalent,
                cancelingRootSelectionAppend,
                GraphQL.Execution.Result.combine] using
                ErrorPresenceEquivalent.add_spec_right_of_ungrouped_pos
                  hungroupedPositive hleftErrors
      | ok specLeftResult =>
          rcases specLeftResult with ⟨specLeftFields, specLeftErrors⟩
          simp [RootSelectionResultAlignedEquivalent] at hleft
  | ok ungroupedLeftResult =>
      simpa [cancelingRootSelectionAppend] using
        RootSelectionResultAlignedEquivalent.combine_append hleft hright

end ExecutionUngroupedUncached
end Algorithms

end GraphQL
