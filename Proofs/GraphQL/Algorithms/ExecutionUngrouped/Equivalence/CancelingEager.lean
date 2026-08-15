import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Eager
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Core

/-!
Aligned bridge from canceling ungrouped execution to the legacy eager visitor.

The two implementations are identical unless a selection bubbles. At that point
the canceling visitor returns immediately while the eager visitor continues
through the remaining siblings. Consequently successful results agree exactly,
while bubbling results need only agree on positive error presence.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached

open GraphQL.Execution
open Eager

@[simp]
private theorem errorPresenceEquivalent_zero : ErrorPresenceEquivalent 0 0 :=
  ErrorPresenceEquivalent.refl 0

private def StrongResultAligned {α : Type} (canceling eager : Result α) : Prop :=
  match canceling, eager with
  | .error cancelingErrors, .error eagerErrors =>
      0 < cancelingErrors ∧ 0 < eagerErrors
  | .ok (cancelingValue, cancelingErrors), .ok (eagerValue, eagerErrors) =>
      cancelingValue = eagerValue ∧ ErrorPresenceEquivalent cancelingErrors eagerErrors
  | _, _ => False

private theorem StrongResultAligned.of_eq {α : Type}
    {canceling eager : Result α} (h : canceling = eager)
    (hpositive : ∀ errors, eager = .error errors -> 0 < errors)
    : StrongResultAligned canceling eager := by
  subst canceling
  cases eager with
  | error errors =>
      exact ⟨hpositive errors rfl, hpositive errors rfl⟩
  | ok result =>
      rcases result with ⟨value, errors⟩
      exact ⟨rfl, ErrorPresenceEquivalent.refl errors⟩

private theorem StrongResultAligned.errorPresence {α : Type}
    {canceling eager : Result α}
    (h : StrongResultAligned canceling eager)
    : ErrorPresenceEquivalent (resultErrorCount canceling) (resultErrorCount eager) := by
  cases canceling <;> cases eager <;>
    simp [StrongResultAligned, resultErrorCount] at h ⊢
  · exact ⟨fun heagerZero => False.elim (by omega), fun _heagerPositive => h.1⟩
  · exact h.2

private theorem StrongResultAligned.nonNullCompletion
    {canceling eager : Result ResponseValue}
    (h : StrongResultAligned canceling eager)
    : StrongResultAligned (nonNullCompletion canceling) (nonNullCompletion eager) := by
  cases canceling <;> cases eager <;>
    simp [StrongResultAligned, ErrorPresenceEquivalent] at h ⊢
  · exact h
  · rename_i cancelingResult eagerResult
    rcases cancelingResult with ⟨cancelingValue, cancelingErrors⟩
    rcases eagerResult with ⟨eagerValue, eagerErrors⟩
    rcases h with ⟨hvalue, herrors⟩
    simp at hvalue herrors
    subst eagerValue
    cases cancelingValue with
    | null =>
        cases cancelingErrors with
        | zero =>
            cases eagerErrors with
            | zero =>
                exact ⟨Nat.zero_lt_succ 0, Nat.zero_lt_succ 0⟩
            | succ eagerErrors =>
                exact False.elim (Nat.not_lt_zero _
                  (herrors.2 (Nat.zero_lt_succ eagerErrors)))
        | succ cancelingErrors =>
            cases eagerErrors with
            | zero =>
                have hzero := herrors.1 rfl
                simp at hzero
            | succ eagerErrors =>
                exact ⟨Nat.zero_lt_succ _, Nat.zero_lt_succ _⟩
    | scalar value =>
        exact ⟨rfl, herrors⟩
    | object fields =>
        exact ⟨rfl, herrors⟩
    | list values =>
        exact ⟨rfl, herrors⟩

private theorem StrongResultAligned.catchBubbleAsNull {α : Type}
    (wrap : α -> ResponseValue)
    {canceling eager : Result α}
    (h : StrongResultAligned canceling eager)
    : StrongResultAligned
        (catchBubbleAsNull wrap canceling)
        (catchBubbleAsNull wrap eager) := by
  cases canceling <;> cases eager <;>
    simp [StrongResultAligned, ErrorPresenceEquivalent] at h ⊢
  · exact ⟨rfl, ⟨fun heagerZero => False.elim (by omega), fun _heagerPositive => h.1⟩⟩
  · rcases h with ⟨hvalue, herrors⟩
    exact ⟨by simp [hvalue], herrors⟩

private theorem handleFieldError_strongResultAligned (fieldType : TypeRef)
    : StrongResultAligned (handleFieldError fieldType) (handleFieldError fieldType) := by
  cases fieldType <;>
    simp [handleFieldError, StrongResultAligned, ErrorPresenceEquivalent]

private theorem StrongResultAligned.combine {α β γ : Type}
    (f : α -> β -> γ)
    {cancelingLeft eagerLeft : Result α}
    {cancelingRight eagerRight : Result β}
    (hleft : StrongResultAligned cancelingLeft eagerLeft)
    (hright : StrongResultAligned cancelingRight eagerRight)
    : StrongResultAligned
        (GraphQL.Execution.Result.combine f cancelingLeft cancelingRight)
        (GraphQL.Execution.Result.combine f eagerLeft eagerRight) := by
  cases cancelingLeft
  <;> cases eagerLeft
  <;>
    cases cancelingRight
  <;> cases eagerRight
  <;>
      simp only [StrongResultAligned,
        GraphQL.Execution.Result.combine] at hleft hright ⊢
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · rcases hleft with ⟨hleftValue, hleftErrors⟩
    rcases hright with ⟨hrightValue, hrightErrors⟩
    exact ⟨
      by simp [hleftValue, hrightValue],
      ErrorPresenceEquivalent.add hleftErrors hrightErrors
    ⟩

private def visitResult (visited : ResponseValue × Result PUnit) : Result ResponseValue :=
  match visited.snd with
  | .error errors => .error errors
  | .ok (_unit, errors) => .ok (visited.fst, errors)

private def VisitResultAligned (canceling eager : ResponseValue × Result PUnit) : Prop :=
  StrongResultAligned (visitResult canceling) (visitResult eager)

private theorem VisitResultAligned.catchVisitBubbleAsNull
    {canceling eager : ResponseValue × Result PUnit}
    (h : VisitResultAligned canceling eager)
    : StrongResultAligned
        (catchVisitBubbleAsNull canceling.fst canceling.snd)
        (catchVisitBubbleAsNull eager.fst eager.snd) := by
  rcases canceling with ⟨cancelingValue, cancelingStatus⟩
  rcases eager with ⟨eagerValue, eagerStatus⟩
  cases cancelingStatus
  <;> cases eagerStatus
  <;>
      simp [VisitResultAligned, visitResult, StrongResultAligned,
        ErrorPresenceEquivalent] at h ⊢
  · exact ⟨rfl, ⟨fun heagerZero => False.elim (by omega), fun _heagerPositive => h.1⟩⟩
  · rcases h with ⟨hvalue, herrors⟩
    exact ⟨hvalue, herrors⟩

private theorem StrongResultAligned.mergeResponseFieldResult
    (responseName : Name) (output : ResponseValue)
    {canceling eager : Result ResponseValue}
    (h : StrongResultAligned canceling eager)
    : VisitResultAligned
        (mergeResponseFieldResult responseName canceling output)
        (mergeResponseFieldResult responseName eager output) := by
  cases canceling <;> cases eager <;>
    simp [VisitResultAligned, visitResult, StrongResultAligned] at h ⊢
  · exact h
  · rename_i cancelingResult eagerResult
    rcases cancelingResult with ⟨cancelingValue, cancelingErrors⟩
    rcases eagerResult with ⟨eagerValue, eagerErrors⟩
    rcases h with ⟨hvalue, herrors⟩
    simp at hvalue herrors
    subst eagerValue
    refine ⟨?_, herrors⟩
    rfl

private theorem StrongResultAligned.to_responseValueAligned
    {canceling eager : Result ResponseValue}
    (h : StrongResultAligned canceling eager)
    : ResponseValueResultAlignedEquivalent canceling eager := by
  cases canceling <;> cases eager <;>
    simp [StrongResultAligned, ResponseValueResultAlignedEquivalent] at h ⊢
  · exact ⟨fun heagerZero => False.elim (by omega), fun _heagerPositive => h.1⟩
  · exact h

private theorem StrongResultAligned.to_rootAligned
    {canceling eager : Result (List (Name × ResponseValue))}
    (h : StrongResultAligned canceling eager)
    : RootSelectionResultAlignedEquivalent canceling eager := by
  cases canceling <;> cases eager <;>
    simp [StrongResultAligned, RootSelectionResultAlignedEquivalent] at h ⊢
  · exact ⟨fun heagerZero => False.elim (by omega), fun _heagerPositive => h.1⟩
  · exact h

mutual
  private def selectionVisitSize : Selection -> Nat
    | .field _ _ _ _ selectionSet => selectionSetVisitSize selectionSet + 1
    | .inlineFragment _ _ selectionSet =>
        selectionSetVisitSize selectionSet + 1

  private def selectionSetVisitSize : List Selection -> Nat
    | [] => 0
    | selection :: rest =>
        selectionVisitSize selection + selectionSetVisitSize rest + 1
end

mutual
  private theorem visitSelection_canceling_eager_aligned
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (hexecute
        : ∀ completionFuel previous field,
            fuel = completionFuel + 1
            -> StrongResultAligned
                (executeField schema resolvers variableValues completionFuel source
                  previous field)
                (Eager.executeField schema resolvers variableValues completionFuel
                  source previous field))
      : ∀ selection output,
          VisitResultAligned
            (visitSelection schema resolvers variableValues fuel parentType source
              selection output)
            (Eager.visitSelection schema resolvers variableValues fuel parentType
              source selection output) := by
    intro selection output
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        cases hallows : selectionDirectivesAllowBool variableValues directives with
        | false =>
            simp [visitSelection, Eager.visitSelection, hallows,
              VisitResultAligned, visitResult, StrongResultAligned, visitOk]
        | true =>
            cases fuel with
            | zero =>
                cases hprevious : responseObjectField? responseName output with
                | none =>
                    have hresult :
                        StrongResultAligned
                          (outOfFuel : Result ResponseValue)
                          (outOfFuel : Result ResponseValue) := by
                      simp [StrongResultAligned, outOfFuel]
                    simpa [visitSelection, Eager.visitSelection, hallows,
                      hprevious] using
                      StrongResultAligned.mergeResponseFieldResult responseName
                        output hresult
                | some previous =>
                    have hresult :
                        StrongResultAligned
                          (.ok (previous, 0) : Result ResponseValue)
                          (.ok (previous, 0) : Result ResponseValue) := by
                      exact ⟨rfl, ErrorPresenceEquivalent.refl 0⟩
                    simpa [visitSelection, Eager.visitSelection, hallows,
                      hprevious] using
                      StrongResultAligned.mergeResponseFieldResult responseName
                        output hresult
            | succ completionFuel =>
                have hfield :=
                  hexecute completionFuel
                    (responseObjectField? responseName output)
                    (executableField parentType responseName fieldName arguments
                      selectionSet)
                    rfl
                simpa [visitSelection, Eager.visitSelection, hallows] using
                  StrongResultAligned.mergeResponseFieldResult responseName output
                    hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases hallows : selectionDirectivesAllowBool variableValues directives with
        | false =>
            have hneutral :
                VisitResultAligned (output, visitOk) (output, visitOk) := by
              simp [VisitResultAligned, visitResult, StrongResultAligned, visitOk]
            cases typeCondition <;>
              simpa [visitSelection, Eager.visitSelection, hallows] using hneutral
        | true =>
            cases typeCondition with
            | none =>
                simpa [visitSelection, Eager.visitSelection, hallows] using
                  visitSubfields_canceling_eager_aligned schema resolvers
                    variableValues fuel parentType source hexecute selectionSet
                    output
            | some typeCondition =>
                cases happly
                      : doesFragmentTypeApplyBool schema parentType source
                          typeCondition with
                | false =>
                    simp [visitSelection, Eager.visitSelection, hallows, happly,
                      VisitResultAligned, visitResult, StrongResultAligned,
                      visitOk]
                | true =>
                    simpa [visitSelection, Eager.visitSelection, hallows, happly]
                      using
                        visitSubfields_canceling_eager_aligned schema resolvers
                          variableValues fuel parentType source hexecute
                          selectionSet output
  termination_by selection _output => selectionVisitSize selection
  decreasing_by
    all_goals
      simp_all [selectionVisitSize]
      try omega

  private theorem visitSubfields_canceling_eager_aligned
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (hexecute
        : ∀ completionFuel previous field,
            fuel = completionFuel + 1
            -> StrongResultAligned
                (executeField schema resolvers variableValues completionFuel source
                  previous field)
                (Eager.executeField schema resolvers variableValues completionFuel
                  source previous field))
      : ∀ selectionSet output,
          VisitResultAligned
            (visitSubfields schema resolvers variableValues fuel parentType source
              selectionSet output)
            (Eager.visitSubfields schema resolvers variableValues fuel parentType
              source selectionSet output) := by
    intro selectionSet output
    cases selectionSet with
    | nil =>
        simp [visitSubfields, Eager.visitSubfields, VisitResultAligned,
          visitResult, StrongResultAligned, visitOk]
    | cons selection rest =>
        have hhead :=
          visitSelection_canceling_eager_aligned schema resolvers variableValues
            fuel parentType source hexecute selection output
        generalize
          hcancelingHead :
            visitSelection schema resolvers variableValues fuel parentType source
                selection output =
              cancelingHead at hhead ⊢
        generalize
          heagerHead :
            Eager.visitSelection schema resolvers variableValues fuel parentType
                source selection output =
              eagerHead at hhead ⊢
        rcases cancelingHead with ⟨cancelingValue, cancelingStatus⟩
        rcases eagerHead with ⟨eagerValue, eagerStatus⟩
        cases cancelingStatus with
        | error cancelingErrors =>
            cases eagerStatus with
            | ok eagerOk =>
                simp [VisitResultAligned, visitResult, StrongResultAligned] at hhead
            | error eagerErrors =>
                have hcancelingPositive : 0 < cancelingErrors := by
                  simpa [VisitResultAligned, visitResult, StrongResultAligned]
                    using hhead.1
                have heagerPositive : 0 < eagerErrors := by
                  simpa [VisitResultAligned, visitResult, StrongResultAligned]
                    using hhead.2
                generalize
                  htail :
                    Eager.visitSubfields schema resolvers variableValues fuel
                        parentType source rest eagerValue =
                      eagerTail
                rcases eagerTail with ⟨tailValue, tailStatus⟩
                cases tailStatus with
                | error tailErrors =>
                    simp [visitSubfields, Eager.visitSubfields,
                      hcancelingHead, heagerHead, htail, VisitResultAligned,
                      visitResult, StrongResultAligned, combineVisitStatus,
                      GraphQL.Execution.Result.combine]
                    exact ⟨hcancelingPositive, by omega⟩
                | ok tailOk =>
                    rcases tailOk with ⟨unitValue, tailErrors⟩
                    cases unitValue
                    simp [visitSubfields, Eager.visitSubfields,
                      hcancelingHead, heagerHead, htail, VisitResultAligned,
                      visitResult, StrongResultAligned, combineVisitStatus,
                      GraphQL.Execution.Result.combine]
                    exact ⟨hcancelingPositive, by omega⟩
        | ok cancelingOk =>
            rcases cancelingOk with ⟨cancelingUnit, cancelingErrors⟩
            cases cancelingUnit
            cases eagerStatus with
            | error eagerErrors =>
                simp [VisitResultAligned, visitResult, StrongResultAligned] at hhead
            | ok eagerOk =>
                rcases eagerOk with ⟨eagerUnit, eagerErrors⟩
                cases eagerUnit
                have hvalue : cancelingValue = eagerValue := by
                  simpa [VisitResultAligned, visitResult, StrongResultAligned]
                    using hhead.1
                have hheadErrors :
                    ErrorPresenceEquivalent cancelingErrors eagerErrors := by
                  simpa [VisitResultAligned, visitResult, StrongResultAligned]
                    using hhead.2
                subst eagerValue
                have htail :=
                  visitSubfields_canceling_eager_aligned schema resolvers
                    variableValues fuel parentType source hexecute rest
                    cancelingValue
                generalize
                  hcancelingTail :
                    visitSubfields schema resolvers variableValues fuel parentType
                        source rest cancelingValue =
                      cancelingTail at htail ⊢
                generalize
                  heagerTail :
                    Eager.visitSubfields schema resolvers variableValues fuel
                        parentType source rest cancelingValue =
                      eagerTail at htail ⊢
                rcases cancelingTail with ⟨cancelingTailValue, cancelingTailStatus⟩
                rcases eagerTail with ⟨eagerTailValue, eagerTailStatus⟩
                cases cancelingTailStatus with
                | error cancelingTailErrors =>
                    cases eagerTailStatus with
                    | ok eagerTailOk =>
                        simp [VisitResultAligned, visitResult,
                          StrongResultAligned] at htail
                    | error eagerTailErrors =>
                        have hcancelingTailPositive :
                            0 < cancelingTailErrors := by
                          simpa [VisitResultAligned, visitResult,
                            StrongResultAligned] using htail.1
                        have heagerTailPositive : 0 < eagerTailErrors := by
                          simpa [VisitResultAligned, visitResult,
                            StrongResultAligned] using htail.2
                        simp [visitSubfields, Eager.visitSubfields,
                          hcancelingHead, heagerHead, hcancelingTail, heagerTail,
                          VisitResultAligned, visitResult, StrongResultAligned,
                          combineVisitStatus, GraphQL.Execution.Result.combine]
                        exact ⟨by omega, by omega⟩
                | ok cancelingTailOk =>
                    rcases cancelingTailOk with
                      ⟨cancelingTailUnit, cancelingTailErrors⟩
                    cases cancelingTailUnit
                    cases eagerTailStatus with
                    | error eagerTailErrors =>
                        simp [VisitResultAligned, visitResult,
                          StrongResultAligned] at htail
                    | ok eagerTailOk =>
                        rcases eagerTailOk with
                          ⟨eagerTailUnit, eagerTailErrors⟩
                        cases eagerTailUnit
                        have htailValue :
                            cancelingTailValue = eagerTailValue := by
                          simpa [VisitResultAligned, visitResult,
                            StrongResultAligned] using htail.1
                        have htailErrors :
                            ErrorPresenceEquivalent cancelingTailErrors
                              eagerTailErrors := by
                          simpa [VisitResultAligned, visitResult,
                            StrongResultAligned] using htail.2
                        simp [visitSubfields, Eager.visitSubfields,
                          hcancelingHead, heagerHead, hcancelingTail, heagerTail,
                          VisitResultAligned, visitResult, StrongResultAligned,
                          combineVisitStatus, GraphQL.Execution.Result.combine]
                        exact ⟨
                          htailValue,
                          ErrorPresenceEquivalent.add hheadErrors htailErrors
                        ⟩
  termination_by selectionSet _output => selectionSetVisitSize selectionSet
  decreasing_by
    all_goals
      simp_all [selectionSetVisitSize]
      try omega
end

private structure FuelImplementationsAligned
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fuel : Nat)
    : Prop where
  completeValue
    : ∀ fieldType selectionSet value previous,
        StrongResultAligned
          (completeValue schema resolvers variableValues fuel fieldType selectionSet
            value previous)
          (Eager.completeValue schema resolvers variableValues fuel fieldType
            selectionSet value previous)
  completeValueList
    : ∀ itemType selectionSet values previousValues,
        StrongResultAligned
          (completeValueList schema resolvers variableValues fuel itemType selectionSet
            values previousValues)
          (Eager.completeValueList schema resolvers variableValues fuel itemType
            selectionSet values previousValues)
  executeField
    : ∀ source previous field,
        StrongResultAligned
          (executeField schema resolvers variableValues fuel source previous field)
          (Eager.executeField schema resolvers variableValues fuel source previous field)
  visitSubfields
    : ∀ parentType source selectionSet output,
        VisitResultAligned
          (visitSubfields schema resolvers variableValues fuel parentType source
            selectionSet output)
          (Eager.visitSubfields schema resolvers variableValues fuel parentType source
            selectionSet output)

private theorem completeValueList_canceling_eager_aligned
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fuel : Nat)
    (hcomplete
      : ∀ fieldType selectionSet value previous,
          StrongResultAligned
            (completeValue schema resolvers variableValues fuel fieldType selectionSet
              value previous)
            (Eager.completeValue schema resolvers variableValues fuel fieldType
              selectionSet value previous))
    : ∀ itemType selectionSet values previousValues,
        StrongResultAligned
          (completeValueList schema resolvers variableValues fuel itemType
            selectionSet values previousValues)
          (Eager.completeValueList schema resolvers variableValues fuel itemType
            selectionSet values previousValues) := by
  intro itemType selectionSet values
  induction values with
  | nil =>
      intro previousValues
      cases previousValues <;>
        simp [completeValueList, Eager.completeValueList, StrongResultAligned,
          ErrorPresenceEquivalent]
  | cons value values ih =>
      intro previousValues
      have htail := ih previousValues.tail
      cases hprevious : previousValues.head? with
      | none =>
          have hhead :=
            hcomplete itemType selectionSet value previousValues.head?
          simpa [completeValueList, Eager.completeValueList, hprevious] using
            StrongResultAligned.combine List.cons hhead htail
      | some previous =>
          cases previous with
          | null =>
              have hhead :
                  StrongResultAligned
                    (.ok (.null, 0) : Result ResponseValue)
                    (.ok (.null, 0) : Result ResponseValue) := by
                exact ⟨rfl, ErrorPresenceEquivalent.refl 0⟩
              simpa [completeValueList, Eager.completeValueList, hprevious] using
                StrongResultAligned.combine List.cons hhead htail
          | scalar scalar =>
              have hhead :=
                hcomplete itemType selectionSet value previousValues.head?
              simpa [completeValueList, Eager.completeValueList, hprevious] using
                StrongResultAligned.combine List.cons hhead htail
          | object fields =>
              have hhead :=
                hcomplete itemType selectionSet value previousValues.head?
              simpa [completeValueList, Eager.completeValueList, hprevious] using
                StrongResultAligned.combine List.cons hhead htail
          | list items =>
              have hhead :=
                hcomplete itemType selectionSet value previousValues.head?
              simpa [completeValueList, Eager.completeValueList, hprevious] using
                StrongResultAligned.combine List.cons hhead htail

private theorem fuelImplementations_canceling_eager_aligned
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    : ∀ fuel, FuelImplementationsAligned schema resolvers variableValues fuel := by
  intro fuel
  induction fuel with
  | zero =>
      have hcomplete :
          ∀ fieldType selectionSet value previous,
            StrongResultAligned
              (completeValue schema resolvers variableValues 0 fieldType selectionSet
                value previous)
              (Eager.completeValue schema resolvers variableValues 0 fieldType
                selectionSet value previous) := by
        intro fieldType selectionSet value previous
        simp [completeValue, Eager.completeValue, outOfFuel,
          StrongResultAligned]
      have hlist :=
        completeValueList_canceling_eager_aligned schema resolvers variableValues 0
          hcomplete
      have hfield :
          ∀ source previous field,
            StrongResultAligned
              (executeField schema resolvers variableValues 0 source previous field)
              (Eager.executeField schema resolvers variableValues 0 source previous
                field) := by
        intro source previous field
        unfold executeField Eager.executeField
        split <;> rename_i hlookup
        · rw [hlookup]
          simp [StrongResultAligned]
        · rw [hlookup]
          simp only
          split <;> rename_i hreuse
          · rw [hreuse]
            simp only
            simp [StrongResultAligned, ErrorPresenceEquivalent]
          · rw [hreuse]
            simp only
            split <;> rename_i hresolve
            · rw [hresolve]
              simp only
              exact handleFieldError_strongResultAligned _
            · rw [hresolve]
              simp only
              exact hcomplete _ field.selectionSet _ previous
      refine {
        completeValue := hcomplete
        completeValueList := hlist
        executeField := hfield
        visitSubfields := ?_
      }
      intro parentType source selectionSet output
      apply
        visitSubfields_canceling_eager_aligned schema resolvers variableValues 0
          parentType source
      intro completionFuel previous field himpossible
      omega
  | succ fuel ih =>
      have hcomplete :
          ∀ fieldType selectionSet value previous,
            StrongResultAligned
              (completeValue schema resolvers variableValues (fuel + 1) fieldType
                selectionSet value previous)
              (Eager.completeValue schema resolvers variableValues (fuel + 1)
                fieldType selectionSet value previous) := by
        intro fieldType
        induction fieldType with
        | named typeName =>
            intro selectionSet value previous
            cases value with
            | null =>
                cases previous with
                | none =>
                    simp [completeValue, Eager.completeValue, StrongResultAligned,
                      ErrorPresenceEquivalent]
                | some previous =>
                    cases previous <;>
                      simp [completeValue, Eager.completeValue, StrongResultAligned,
                        ErrorPresenceEquivalent]
            | scalar scalar =>
                cases previous with
                | none =>
                    by_cases hcomposite :
                        (TypeRef.named typeName).isCompositeBool schema = true
                    <;>
                      simp [completeValue, Eager.completeValue, hcomposite,
                        StrongResultAligned, ErrorPresenceEquivalent]
                | some previous =>
                    cases previous <;>
                      simp [completeValue, Eager.completeValue, StrongResultAligned,
                        ErrorPresenceEquivalent]
            | object runtimeType ref =>
                cases previous with
                | none =>
                    by_cases hincludes :
                        schema.typeIncludesObjectBool typeName runtimeType = true
                    · have hvisit :=
                        ih.visitSubfields runtimeType (.object runtimeType ref)
                          selectionSet (.object [])
                      simpa [completeValue, Eager.completeValue, hincludes,
                        reuseOrCreateObject?] using
                          hvisit.catchVisitBubbleAsNull
                    · simp [completeValue, Eager.completeValue, hincludes,
                        StrongResultAligned]
                | some previous =>
                    cases previous with
                    | null =>
                        simp [completeValue, Eager.completeValue,
                          StrongResultAligned, ErrorPresenceEquivalent]
                    | scalar scalar =>
                        simp [completeValue, Eager.completeValue,
                          StrongResultAligned]
                    | object fields =>
                        by_cases hincludes :
                            schema.typeIncludesObjectBool typeName runtimeType = true
                        · have hvisit :=
                            ih.visitSubfields runtimeType (.object runtimeType ref)
                              selectionSet (.object fields)
                          simpa [completeValue, Eager.completeValue, hincludes,
                            reuseOrCreateObject?] using
                              hvisit.catchVisitBubbleAsNull
                        · simp [completeValue, Eager.completeValue, hincludes,
                            StrongResultAligned]
                    | list items =>
                        simp [completeValue, Eager.completeValue,
                          reuseOrCreateObject?, StrongResultAligned]
            | list values =>
                cases previous with
                | none =>
                    simp [completeValue, Eager.completeValue, StrongResultAligned]
                | some previous =>
                    cases previous <;>
                      simp [completeValue, Eager.completeValue, StrongResultAligned,
                        ErrorPresenceEquivalent]
        | list inner innerIh =>
            intro selectionSet value previous
            cases value with
            | null =>
                cases previous with
                | none =>
                    simp [completeValue, Eager.completeValue, StrongResultAligned,
                      ErrorPresenceEquivalent]
                | some previous =>
                    cases previous <;>
                      simp [completeValue, Eager.completeValue, StrongResultAligned,
                        ErrorPresenceEquivalent]
            | scalar scalar =>
                cases previous with
                | none =>
                    simp [completeValue, Eager.completeValue, StrongResultAligned]
                | some previous =>
                    cases previous <;>
                      simp [completeValue, Eager.completeValue, StrongResultAligned,
                        ErrorPresenceEquivalent]
            | object runtimeType ref =>
                cases previous with
                | none =>
                    simp [completeValue, Eager.completeValue, StrongResultAligned]
                | some previous =>
                    cases previous <;>
                      simp [completeValue, Eager.completeValue, StrongResultAligned,
                        ErrorPresenceEquivalent]
            | list values =>
                cases previous with
                | none =>
                    have hitems :=
                      ih.completeValueList inner selectionSet values []
                    simpa [completeValue, Eager.completeValue, reuseOrCreateList?]
                      using
                        StrongResultAligned.catchBubbleAsNull ResponseValue.list
                          hitems
                | some previous =>
                    cases previous with
                    | null =>
                        simp [completeValue, Eager.completeValue,
                          StrongResultAligned, ErrorPresenceEquivalent]
                    | scalar scalar =>
                        simp [completeValue, Eager.completeValue,
                          StrongResultAligned]
                    | object fields =>
                        simp [completeValue, Eager.completeValue,
                          reuseOrCreateList?, StrongResultAligned]
                    | list items =>
                        have hitems :=
                          ih.completeValueList inner selectionSet values items
                        simpa [completeValue, Eager.completeValue,
                          reuseOrCreateList?] using
                            StrongResultAligned.catchBubbleAsNull ResponseValue.list
                              hitems
        | nonNull inner innerIh =>
            intro selectionSet value previous
            cases previous with
            | some previous =>
                cases previous with
                | null =>
                    simp [completeValue, Eager.completeValue, StrongResultAligned,
                      ErrorPresenceEquivalent]
                | scalar scalar =>
                    simp [completeValue, Eager.completeValue, StrongResultAligned]
                | object fields =>
                    simpa [completeValue, Eager.completeValue] using
                      StrongResultAligned.nonNullCompletion
                        (innerIh selectionSet value (some (.object fields)))
                | list items =>
                    simpa [completeValue, Eager.completeValue] using
                      StrongResultAligned.nonNullCompletion
                        (innerIh selectionSet value (some (.list items)))
            | none =>
                simpa [completeValue, Eager.completeValue] using
                  StrongResultAligned.nonNullCompletion
                    (innerIh selectionSet value none)
      have hlist :=
        completeValueList_canceling_eager_aligned schema resolvers variableValues
          (fuel + 1) hcomplete
      have hfield :
          ∀ source previous field,
            StrongResultAligned
              (executeField schema resolvers variableValues (fuel + 1) source
                previous field)
              (Eager.executeField schema resolvers variableValues (fuel + 1) source
                previous field) := by
        intro source previous field
        unfold executeField Eager.executeField
        split <;> rename_i hlookup
        · rw [hlookup]
          simp [StrongResultAligned]
        · rw [hlookup]
          simp only
          split <;> rename_i hreuse
          · rw [hreuse]
            simp only
            simp [StrongResultAligned, ErrorPresenceEquivalent]
          · rw [hreuse]
            simp only
            split <;> rename_i hresolve
            · rw [hresolve]
              simp only
              exact handleFieldError_strongResultAligned _
            · rw [hresolve]
              simp only
              exact hcomplete _ field.selectionSet _ previous
      refine {
        completeValue := hcomplete
        completeValueList := hlist
        executeField := hfield
        visitSubfields := ?_
      }
      intro parentType source selectionSet output
      apply
        visitSubfields_canceling_eager_aligned schema resolvers variableValues
          (fuel + 1) parentType source
      intro completionFuel previous field heq
      have hcompletionFuel : completionFuel = fuel := by omega
      subst completionFuel
      exact ih.executeField source previous field

theorem executeRootSelectionSet_canceling_eager_aligned
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues fuel parentType
          source selectionSet)
        (Eager.executeRootSelectionSet schema resolvers variableValues fuel parentType
          source selectionSet) := by
  have haligned :=
    (fuelImplementations_canceling_eager_aligned schema resolvers variableValues
      fuel).visitSubfields parentType source selectionSet (.object [])
  generalize
    hcanceling :
      visitSubfields schema resolvers variableValues fuel parentType source
          selectionSet (.object []) =
        cancelingVisited at haligned ⊢
  generalize
    heager :
      Eager.visitSubfields schema resolvers variableValues fuel parentType source
          selectionSet (.object []) =
        eagerVisited at haligned ⊢
  rcases cancelingVisited with ⟨cancelingValue, cancelingStatus⟩
  rcases eagerVisited with ⟨eagerValue, eagerStatus⟩
  cases cancelingStatus with
  | error cancelingErrors =>
      cases eagerStatus with
      | ok eagerOk =>
          simp [VisitResultAligned, visitResult, StrongResultAligned] at haligned
      | error eagerErrors =>
          have hcancelingPositive : 0 < cancelingErrors := by
            simpa [VisitResultAligned, visitResult, StrongResultAligned] using
              haligned.1
          have heagerPositive : 0 < eagerErrors := by
            simpa [VisitResultAligned, visitResult, StrongResultAligned] using
              haligned.2
          simpa [executeRootSelectionSet, Eager.executeRootSelectionSet,
            hcanceling, heager, RootSelectionResultAlignedEquivalent] using
              ErrorPresenceEquivalent.of_pos hcancelingPositive heagerPositive
  | ok cancelingOk =>
      rcases cancelingOk with ⟨cancelingUnit, cancelingErrors⟩
      cases cancelingUnit
      cases eagerStatus with
      | error eagerErrors =>
          simp [VisitResultAligned, visitResult, StrongResultAligned] at haligned
      | ok eagerOk =>
          rcases eagerOk with ⟨eagerUnit, eagerErrors⟩
          cases eagerUnit
          have hvalue : cancelingValue = eagerValue := by
            simpa [VisitResultAligned, visitResult, StrongResultAligned] using
              haligned.1
          have herrors :
              ErrorPresenceEquivalent cancelingErrors eagerErrors := by
            simpa [VisitResultAligned, visitResult, StrongResultAligned] using
              haligned.2
          subst eagerValue
          cases cancelingValue with
          | object fields =>
              have hresult :
                  fields = fields
                    ∧ ErrorPresenceEquivalent cancelingErrors eagerErrors :=
                ⟨rfl, herrors⟩
              simpa [executeRootSelectionSet, Eager.executeRootSelectionSet,
                hcanceling, heager, RootSelectionResultAlignedEquivalent] using
                  hresult
          | null =>
              simpa [executeRootSelectionSet, Eager.executeRootSelectionSet,
                hcanceling, heager, RootSelectionResultAlignedEquivalent] using
                  ErrorPresenceEquivalent.of_pos (by omega) (by omega)
          | scalar value =>
              simpa [executeRootSelectionSet, Eager.executeRootSelectionSet,
                hcanceling, heager, RootSelectionResultAlignedEquivalent] using
                  ErrorPresenceEquivalent.of_pos (by omega) (by omega)
          | list values =>
              simpa [executeRootSelectionSet, Eager.executeRootSelectionSet,
                hcanceling, heager, RootSelectionResultAlignedEquivalent] using
                  ErrorPresenceEquivalent.of_pos (by omega) (by omega)

theorem executeQueryWithFuel_canceling_eager_responseEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectIdentity)
    : responseDataAndErrorPresenceEquivalent
        (executeQueryWithFuel schema resolvers variableValues operation fuel source)
        (Eager.executeQueryWithFuel schema resolvers variableValues operation fuel
          source) := by
  unfold executeQueryWithFuel Eager.executeQueryWithFuel
  split <;> rename_i hroot
  · apply
      responseDataAndErrorPresenceEquivalent_of_selectionSetResultToResponse
    exact
      executeRootSelectionSet_canceling_eager_aligned schema resolvers
        (GraphQL.Execution.coerceVariableValues operation variableValues) fuel
        (operation.rootType schema) source operation.selectionSet
  · exact responseDataAndErrorPresenceEquivalent_of_eq rfl

end ExecutionUngroupedUncached
end Algorithms

end GraphQL
