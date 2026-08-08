import GraphQL.Algorithms.ExecutionCancelingSiblings

/-!
Semantic preservation for sibling-canceling collected execution.

The proof aligns the canceling executor with `GraphQL.Execution` at every fuel.
Successful results have the same value and error presence. Bubbling results on
both sides carry positive error counts; the spec executor may add errors from
siblings that the canceling executor does not visit.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionCancelingSiblings

open GraphQL.Execution

private def ErrorPresenceEquivalent (canceling spec : Nat) : Prop :=
  (spec = 0 -> canceling = 0) ∧ (0 < spec -> 0 < canceling)

private theorem ErrorPresenceEquivalent.refl (errors : Nat)
    : ErrorPresenceEquivalent errors errors :=
  ⟨fun hzero => hzero, fun hpositive => hpositive⟩

private theorem ErrorPresenceEquivalent.add
    {cancelingLeft specLeft cancelingRight specRight : Nat}
    (hleft : ErrorPresenceEquivalent cancelingLeft specLeft)
    (hright : ErrorPresenceEquivalent cancelingRight specRight)
    : ErrorPresenceEquivalent
        (cancelingLeft + cancelingRight) (specLeft + specRight) := by
  constructor
  · intro hzero
    have hspecLeft : specLeft = 0 := by omega
    have hspecRight : specRight = 0 := by omega
    have hcancelingLeft : cancelingLeft = 0 := hleft.1 hspecLeft
    have hcancelingRight : cancelingRight = 0 := hright.1 hspecRight
    omega
  · intro hpositive
    by_cases hspecLeft : specLeft = 0
    · have hspecRightPositive : 0 < specRight := by omega
      have hcancelingRightPositive : 0 < cancelingRight :=
        hright.2 hspecRightPositive
      omega
    · have hspecLeftPositive : 0 < specLeft := Nat.pos_of_ne_zero hspecLeft
      have hcancelingLeftPositive : 0 < cancelingLeft :=
        hleft.2 hspecLeftPositive
      omega

private def StrongResultAligned {α : Type} (canceling spec : Result α) : Prop :=
  match canceling, spec with
  | .error cancelingErrors, .error specErrors =>
      0 < cancelingErrors ∧ 0 < specErrors
  | .ok (cancelingValue, cancelingErrors), .ok (specValue, specErrors) =>
      cancelingValue = specValue ∧ ErrorPresenceEquivalent cancelingErrors specErrors
  | _, _ => False

private theorem StrongResultAligned.combine {α β γ : Type}
    (combine : α -> β -> γ)
    {cancelingLeft specLeft : Result α}
    {cancelingRight specRight : Result β}
    (hleft : StrongResultAligned cancelingLeft specLeft)
    (hright : StrongResultAligned cancelingRight specRight)
    : StrongResultAligned
        (Result.combine combine cancelingLeft cancelingRight)
        (Result.combine combine specLeft specRight) := by
  cases cancelingLeft <;> cases specLeft <;>
    cases cancelingRight <;> cases specRight <;>
    simp only [StrongResultAligned, Result.combine] at hleft hright ⊢
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · rcases hleft with ⟨hleftValue, hleftErrors⟩
    rcases hright with ⟨hrightValue, hrightErrors⟩
    exact
      ⟨by simp [hleftValue, hrightValue],
        ErrorPresenceEquivalent.add hleftErrors hrightErrors⟩

private theorem StrongResultAligned.nonNullCompletion
    {canceling spec : Result ResponseValue}
    (h : StrongResultAligned canceling spec)
    : StrongResultAligned (nonNullCompletion canceling) (nonNullCompletion spec) := by
  cases canceling <;> cases spec <;>
    simp [StrongResultAligned, ErrorPresenceEquivalent] at h ⊢
  · exact h
  · rename_i cancelingResult specResult
    rcases cancelingResult with ⟨cancelingValue, cancelingErrors⟩
    rcases specResult with ⟨specValue, specErrors⟩
    rcases h with ⟨hvalue, herrors⟩
    simp at hvalue herrors
    subst specValue
    cases cancelingValue with
    | null =>
        cases cancelingErrors with
        | zero =>
            cases specErrors with
            | zero =>
                exact ⟨Nat.zero_lt_succ 0, Nat.zero_lt_succ 0⟩
            | succ specErrors =>
                exact False.elim (Nat.not_lt_zero _
                  (herrors.2 (Nat.zero_lt_succ specErrors)))
        | succ cancelingErrors =>
            cases specErrors with
            | zero =>
                have hzero := herrors.1 rfl
                simp at hzero
            | succ specErrors =>
                exact ⟨Nat.zero_lt_succ _, Nat.zero_lt_succ _⟩
    | scalar value =>
        exact ⟨rfl, herrors⟩
    | object fields =>
        exact ⟨rfl, herrors⟩
    | list values =>
        exact ⟨rfl, herrors⟩

private theorem StrongResultAligned.catchBubbleAsNull {α : Type}
    (wrap : α -> ResponseValue)
    {canceling spec : Result α}
    (h : StrongResultAligned canceling spec)
    : StrongResultAligned
        (catchBubbleAsNull wrap canceling)
        (catchBubbleAsNull wrap spec) := by
  cases canceling <;> cases spec <;>
    simp [StrongResultAligned, ErrorPresenceEquivalent] at h ⊢
  · exact
      ⟨rfl,
        ⟨fun hspecZero => False.elim (by omega),
          fun _hspecPositive => h.1⟩⟩
  · rcases h with ⟨hvalue, herrors⟩
    exact ⟨by simp [hvalue], herrors⟩

private theorem StrongResultAligned.singleFieldResult
    (responseName : Name)
    {canceling spec : Result ResponseValue}
    (h : StrongResultAligned canceling spec)
    : StrongResultAligned
        (singleFieldResult responseName canceling)
        (singleFieldResult responseName spec) := by
  cases canceling <;> cases spec <;>
    simp [StrongResultAligned] at h ⊢
  · exact h
  · rcases h with ⟨hvalue, herrors⟩
    exact ⟨by simp [hvalue], herrors⟩

private structure FuelImplementationsAligned
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    : Prop where
  completeValue
    : ∀ fieldType fields value,
        StrongResultAligned
          (completeValue schema resolvers variableValues fuel fieldType fields value)
          (GraphQL.Execution.completeValue schema resolvers variableValues
            fuel fieldType fields value)
  completeValueList
    : ∀ itemType fields values,
        StrongResultAligned
          (completeValueList schema resolvers variableValues fuel itemType fields values)
          (GraphQL.Execution.completeValueList schema resolvers variableValues
            fuel itemType fields values)
  executeField
    : ∀ source responseName fields,
        StrongResultAligned
          (executeField schema resolvers variableValues fuel source responseName fields)
          (GraphQL.Execution.executeField schema resolvers variableValues fuel
            source responseName fields)
  executeCollectedFields
    : ∀ source groups,
        StrongResultAligned
          (executeCollectedFields schema resolvers variableValues fuel source groups)
          (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
            fuel source groups)

private theorem fuelImplementationsAligned
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    : ∀ fuel, FuelImplementationsAligned schema resolvers variableValues fuel := by
  intro fuel
  induction fuel with
  | zero =>
      have hcomplete :
          ∀ fieldType fields value,
            StrongResultAligned
              (completeValue schema resolvers variableValues 0
                fieldType fields value)
              (GraphQL.Execution.completeValue schema resolvers variableValues 0
                fieldType fields value) := by
        intro fieldType fields value
        simp [completeValue, GraphQL.Execution.completeValue,
          StrongResultAligned, outOfFuel]
      have hfield :
          ∀ source responseName fields,
            StrongResultAligned
              (executeField schema resolvers variableValues 0 source
                responseName fields)
              (GraphQL.Execution.executeField schema resolvers variableValues 0
                source responseName fields) := by
        intro source responseName fields
        cases fields <;>
          simp [executeField, GraphQL.Execution.executeField,
            StrongResultAligned, outOfFuel]
      have hcollected :
          ∀ source groups,
            StrongResultAligned
              (executeCollectedFields schema resolvers variableValues 0 source groups)
              (GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues 0 source groups) := by
        intro source groups
        induction groups with
        | nil =>
            simp [executeCollectedFields,
              GraphQL.Execution.executeCollectedFields, StrongResultAligned,
              ErrorPresenceEquivalent]
        | cons group rest ih =>
            rcases group with ⟨responseName, fields⟩
            simp only [executeCollectedFields,
              GraphQL.Execution.executeCollectedFields]
            have hhead := hfield source responseName fields
            generalize hcancelingHead :
                executeField schema resolvers variableValues 0 source
                    responseName fields =
                  cancelingHead at hhead ⊢
            generalize hspecHead :
                GraphQL.Execution.executeField schema resolvers variableValues
                    0 source responseName fields =
                  specHead at hhead ⊢
            have htail := ih
            generalize hcancelingTail :
                executeCollectedFields schema resolvers variableValues 0
                    source rest =
                  cancelingTail at htail ⊢
            generalize hspecTail :
                GraphQL.Execution.executeCollectedFields schema resolvers
                    variableValues 0 source rest =
                  specTail at htail ⊢
            cases cancelingHead <;> cases specHead <;>
              cases cancelingTail <;> cases specTail <;>
              simp only [StrongResultAligned, Result.combine] at hhead htail ⊢
            · exact ⟨hhead.1, by omega⟩
            · exact ⟨hhead.1, by omega⟩
            · exact ⟨by omega, by omega⟩
            · rcases hhead with ⟨hheadValue, hheadErrors⟩
              rcases htail with ⟨htailValue, htailErrors⟩
              exact
                ⟨by simp [hheadValue, htailValue],
                  ErrorPresenceEquivalent.add hheadErrors htailErrors⟩
      have hlist :
          ∀ itemType fields values,
            StrongResultAligned
              (completeValueList schema resolvers variableValues
                0 itemType fields values)
              (GraphQL.Execution.completeValueList schema resolvers variableValues
                0 itemType fields values) := by
        intro itemType fields values
        induction values with
        | nil =>
            simp [completeValueList,
              GraphQL.Execution.completeValueList, StrongResultAligned,
              ErrorPresenceEquivalent]
        | cons value values ih =>
            simpa [completeValueList,
              GraphQL.Execution.completeValueList] using
                StrongResultAligned.combine List.cons
                  (hcomplete itemType fields value) ih
      exact
        {
          completeValue := hcomplete
          completeValueList := hlist
          executeField := hfield
          executeCollectedFields := hcollected
        }
  | succ fuel ih =>
      have hcomplete :
          ∀ fieldType fields value,
            StrongResultAligned
              (completeValue schema resolvers variableValues (fuel + 1)
                fieldType fields value)
              (GraphQL.Execution.completeValue schema resolvers variableValues
                (fuel + 1) fieldType fields value) := by
        intro fieldType
        induction fieldType with
        | named typeName =>
            intro fields value
            cases value with
            | null =>
                simp [completeValue, GraphQL.Execution.completeValue,
                  StrongResultAligned, ErrorPresenceEquivalent]
            | scalar value =>
                by_cases hcomposite :
                    (TypeRef.named typeName).isCompositeBool schema = true
                · simp [completeValue, GraphQL.Execution.completeValue,
                    hcomposite, StrongResultAligned]
                · have hfalse :
                    (TypeRef.named typeName).isCompositeBool schema = false := by
                    cases hmatch :
                        (TypeRef.named typeName).isCompositeBool schema
                    · rfl
                    · contradiction
                  simp [completeValue, GraphQL.Execution.completeValue,
                    hfalse, StrongResultAligned, ErrorPresenceEquivalent]
            | object runtimeType ref =>
                by_cases hinclude :
                    schema.typeIncludesObjectBool typeName runtimeType = true
                · simpa [completeValue, GraphQL.Execution.completeValue,
                    hinclude] using
                      StrongResultAligned.catchBubbleAsNull ResponseValue.object
                        (ih.executeCollectedFields
                          (ResolverValue.object runtimeType ref)
                          (collectSubfields schema variableValues runtimeType
                            (ResolverValue.object runtimeType ref) fields))
                · have hfalse :
                    schema.typeIncludesObjectBool typeName runtimeType = false := by
                    cases hmatch :
                        schema.typeIncludesObjectBool typeName runtimeType
                    · rfl
                    · contradiction
                  simp [completeValue, GraphQL.Execution.completeValue,
                    hfalse, StrongResultAligned]
            | list values =>
                simp [completeValue, GraphQL.Execution.completeValue,
                  StrongResultAligned]
        | list inner innerIh =>
            intro fields value
            cases value with
            | null =>
                simp [completeValue, GraphQL.Execution.completeValue,
                  StrongResultAligned, ErrorPresenceEquivalent]
            | scalar value =>
                simp [completeValue, GraphQL.Execution.completeValue,
                  StrongResultAligned]
            | object runtimeType ref =>
                simp [completeValue, GraphQL.Execution.completeValue,
                  StrongResultAligned]
            | list values =>
                simpa [completeValue, GraphQL.Execution.completeValue] using
                  StrongResultAligned.catchBubbleAsNull ResponseValue.list
                    (ih.completeValueList inner fields values)
        | nonNull inner innerIh =>
            intro fields value
            simpa [completeValue, GraphQL.Execution.completeValue] using
              StrongResultAligned.nonNullCompletion (innerIh fields value)
      have hfield :
          ∀ source responseName fields,
            StrongResultAligned
              (executeField schema resolvers variableValues (fuel + 1) source
                responseName fields)
              (GraphQL.Execution.executeField schema resolvers variableValues
                (fuel + 1) source responseName fields) := by
        intro source responseName fields
        cases fields with
        | nil =>
            simp [executeField, GraphQL.Execution.executeField,
              StrongResultAligned]
        | cons field fields =>
            cases hlookup : schema.lookupField field.parentType field.fieldName with
            | none =>
                simp [executeField, GraphQL.Execution.executeField, hlookup,
                  StrongResultAligned]
            | some fieldDefinition =>
                cases hresolve
                      : resolvers.resolve field.parentType field.fieldName
                          field.arguments source with
                | none =>
                    have hhandle :
                        StrongResultAligned
                          (handleFieldError fieldDefinition.outputType)
                          (handleFieldError fieldDefinition.outputType) := by
                      cases fieldDefinition.outputType <;>
                        simp [handleFieldError, StrongResultAligned,
                          ErrorPresenceEquivalent]
                    simpa [executeField, GraphQL.Execution.executeField,
                      hlookup, hresolve] using
                        StrongResultAligned.singleFieldResult responseName hhandle
                | some resolved =>
                    simpa [executeField, GraphQL.Execution.executeField,
                      hlookup, hresolve] using
                        StrongResultAligned.singleFieldResult responseName
                          (ih.completeValue fieldDefinition.outputType
                            (field :: fields) resolved)
      have hcollected :
          ∀ source groups,
            StrongResultAligned
              (executeCollectedFields schema resolvers variableValues
                (fuel + 1) source groups)
              (GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues (fuel + 1) source groups) := by
        intro source groups
        induction groups with
        | nil =>
            simp [executeCollectedFields,
              GraphQL.Execution.executeCollectedFields, StrongResultAligned,
              ErrorPresenceEquivalent]
        | cons group rest ih =>
            rcases group with ⟨responseName, fields⟩
            simp only [executeCollectedFields,
              GraphQL.Execution.executeCollectedFields]
            have hhead := hfield source responseName fields
            generalize hcancelingHead :
                executeField schema resolvers variableValues (fuel + 1) source
                    responseName fields =
                  cancelingHead at hhead ⊢
            generalize hspecHead :
                GraphQL.Execution.executeField schema resolvers variableValues
                    (fuel + 1) source responseName fields =
                  specHead at hhead ⊢
            have htail := ih
            generalize hcancelingTail :
                executeCollectedFields schema resolvers variableValues
                    (fuel + 1) source rest =
                  cancelingTail at htail ⊢
            generalize hspecTail :
                GraphQL.Execution.executeCollectedFields schema resolvers
                    variableValues (fuel + 1) source rest =
                  specTail at htail ⊢
            cases cancelingHead <;> cases specHead <;>
              cases cancelingTail <;> cases specTail <;>
              simp only [StrongResultAligned, Result.combine] at hhead htail ⊢
            · exact ⟨hhead.1, by omega⟩
            · exact ⟨hhead.1, by omega⟩
            · exact ⟨by omega, by omega⟩
            · rcases hhead with ⟨hheadValue, hheadErrors⟩
              rcases htail with ⟨htailValue, htailErrors⟩
              exact
                ⟨by simp [hheadValue, htailValue],
                  ErrorPresenceEquivalent.add hheadErrors htailErrors⟩
      have hlist :
          ∀ itemType fields values,
            StrongResultAligned
              (completeValueList schema resolvers variableValues
                (fuel + 1) itemType fields values)
              (GraphQL.Execution.completeValueList schema resolvers variableValues
                (fuel + 1) itemType fields values) := by
        intro itemType fields values
        induction values with
        | nil =>
            simp [completeValueList,
              GraphQL.Execution.completeValueList, StrongResultAligned,
              ErrorPresenceEquivalent]
        | cons value values ih =>
            simpa [completeValueList,
              GraphQL.Execution.completeValueList] using
                StrongResultAligned.combine List.cons
                  (hcomplete itemType fields value) ih
      exact
        {
          completeValue := hcomplete
          completeValueList := hlist
          executeField := hfield
          executeCollectedFields := hcollected
        }

private theorem responseEquivalent_of_rootAligned
    {canceling spec : Result (List (Name × ResponseValue))}
    (h : StrongResultAligned canceling spec)
    : responseDataAndErrorPresenceEquivalent
        (selectionSetResultToResponse canceling)
        (selectionSetResultToResponse spec) := by
  cases canceling <;> cases spec <;>
    simp [StrongResultAligned, responseDataAndErrorPresenceEquivalent,
      selectionSetResultToResponse, ErrorPresenceEquivalent] at h ⊢
  · exact
      ⟨fun hspecZero => False.elim (by omega),
        fun _hspecPositive => h.1⟩
  · exact h

private theorem executeRootSelectionSet_canceling_spec_aligned
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : StrongResultAligned
        (executeRootSelectionSet schema resolvers variableValues fuel parentType
          source selectionSet)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          fuel parentType source selectionSet) := by
  simpa [executeRootSelectionSet,
    GraphQL.Execution.executeRootSelectionSet] using
      (fuelImplementationsAligned schema resolvers variableValues fuel)
        |>.executeCollectedFields source
          (collectFields schema variableValues parentType source selectionSet)

theorem executeQueryWithFuel_canceling_spec_responseEquivalent
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : responseDataAndErrorPresenceEquivalent
        (executeQueryWithFuel schema resolvers variableValues operation fuel source)
        (GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation fuel source) := by
  unfold executeQueryWithFuel GraphQL.Execution.executeQueryWithFuel
  split <;> rename_i hroot
  · apply responseEquivalent_of_rootAligned
    exact
      executeRootSelectionSet_canceling_spec_aligned schema resolvers
        (coerceVariableValues operation variableValues) fuel
        (operation.rootType schema) source operation.selectionSet
  · simp [responseDataAndErrorPresenceEquivalent]

theorem siblingCancelingExecutionPreservesSpecExecution_proof
    (schema : Schema) (operation : Operation)
    : siblingCancelingExecutionPreservesSpecExecution schema operation := by
  intro ObjectRef resolvers variableValues fuel source
  exact
    executeQueryWithFuel_canceling_spec_responseEquivalent schema resolvers
      variableValues operation fuel source

end ExecutionCancelingSiblings
end Algorithms

end GraphQL
