import GraphQL.IncrementalDelivery.Correctness

/-! Basic execution never produces a bubbling failure with zero counted errors. -/

namespace GraphQL.IncrementalDelivery.Semantics

namespace BasicErrors

open GraphQL.Execution

variable {ObjectRef : Type}

def PositiveFailure (result : Result α) : Prop :=
  ∀ errors, result = .error errors → 0 < errors

theorem catchNull (wrap : α → ResponseValue) (result : Result α)
    : PositiveFailure (catchBubbleAsNull wrap result) := by
  cases result <;> simp [PositiveFailure, catchBubbleAsNull]

theorem nonNull (result : Result ResponseValue) (h : PositiveFailure result)
    : PositiveFailure (nonNullCompletion result) := by
  cases result with
  | error errors => exact h
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value <;> cases errors <;> simp [PositiveFailure, nonNullCompletion]

theorem field (name : Name) (result : Result ResponseValue) (h : PositiveFailure result)
    : PositiveFailure (singleFieldResult name result) := by
  cases result with
  | error errors => simpa [PositiveFailure, singleFieldResult] using h
  | ok result => simp [PositiveFailure, singleFieldResult]

theorem handle (fieldType : TypeRef) : PositiveFailure (handleFieldError fieldType) := by
  cases fieldType <;> simp [PositiveFailure, handleFieldError]

theorem combine (f : α → β → γ) (left : Result α) (right : Result β)
    (hl : PositiveFailure left) (hr : PositiveFailure right)
    : PositiveFailure (Result.combine f left right) := by
  cases left <;> cases right <;>
    simp_all [PositiveFailure, Result.combine] <;> omega

theorem completeValue (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
    (fields : List ExecutableField) (value : ResolverValue ObjectRef)
    : PositiveFailure
        (GraphQL.Execution.completeValue schema resolvers variables fuel fieldType fields
          value) := by
  induction fieldType generalizing fuel with
  | nonNull inner ih =>
      cases fuel with
      | zero => simp [GraphQL.Execution.completeValue, PositiveFailure, outOfFuel]
      | succ fuel =>
          simp only [GraphQL.Execution.completeValue]
          exact nonNull _ (ih (fuel + 1))
  | named parentType =>
      cases fuel <;> cases value <;>
        simp only [GraphQL.Execution.completeValue] <;>
        first
        | exact catchNull _ _
        | (split <;> first | exact catchNull _ _ | simp [PositiveFailure])
        | simp [PositiveFailure, outOfFuel]
  | list inner ih =>
      cases fuel <;> cases value <;>
        simp only [GraphQL.Execution.completeValue] <;>
        first | exact catchNull _ _ | simp [PositiveFailure, outOfFuel]

theorem executeField (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef)
    (name : Name) (fields : List ExecutableField)
    : PositiveFailure
        (GraphQL.Execution.executeField schema resolvers variables fuel parentType source
          name fields) := by
  cases fields with
  | nil => simp [GraphQL.Execution.executeField, PositiveFailure]
  | cons head tail =>
      cases fuel with
      | zero => simp [GraphQL.Execution.executeField, PositiveFailure, outOfFuel]
      | succ fuel =>
          simp only [GraphQL.Execution.executeField]
          split
          · simp [PositiveFailure]
          · split
            · exact field _ _ (handle _)
            · split
              · exact field _ _ (handle _)
              · exact field _ _ (completeValue schema resolvers variables fuel _ _ _)

theorem executeCollectedFields (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    : PositiveFailure
        (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source groups) := by
  induction groups with
  | nil => simp [GraphQL.Execution.executeCollectedFields, PositiveFailure]
  | cons group rest ih =>
      rcases group with ⟨name, fields⟩
      simp only [GraphQL.Execution.executeCollectedFields]
      exact combine _ _ _
        (executeField schema resolvers variables fuel parentType source _ _) ih

end BasicErrors
end GraphQL.IncrementalDelivery.Semantics
