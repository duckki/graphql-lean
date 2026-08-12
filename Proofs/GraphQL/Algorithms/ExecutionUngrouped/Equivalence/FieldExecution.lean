import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Response
import Proofs.GraphQL.Execution.Data

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

def completeResolvedValue {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (fieldType : TypeRef) (selectionSet : List Selection)
    (resolved : ResolverValue ObjectIdentity) (previous? : Option ResponseValue)
    : Result ResponseValue :=
  match reusablePreviousValue? schema fieldType previous? with
  | some previous => .ok (previous, 0)
  | none =>
      match fieldType with
      | .nonNull inner =>
          nonNullCompletion
            (completeResolvedValue schema resolvers variableValues
              completionDepth inner selectionSet resolved previous?)
      | .list _inner =>
          completeValue schema resolvers variableValues completionDepth
            fieldType selectionSet resolved previous?
      | .named _typeName =>
          completeValue schema resolvers variableValues completionDepth
            fieldType selectionSet resolved previous?

def terminalPreviousValue? : Option ResponseValue -> Option ResponseValue
  | some .null => some .null
  | some (.scalar value) => some (.scalar value)
  | _ => none

def executeFieldVisitResult
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (previous? : Option ResponseValue)
    (field : ExecutableField)
    : Result ResponseValue :=
  executeField schema resolvers variableValues depth source previous? field

theorem resultValueOrNull_fieldVisitResult_eq_executeField
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (previous? : Option ResponseValue)
    (field : ExecutableField)
    : resultValueOrNull
        (executeFieldVisitResult schema resolvers variableValues depth source
          previous? field)
      = resultValueOrNull
          (executeField schema resolvers variableValues depth source previous?
            field) := by
  rfl

@[simp]
theorem combineVisitStatus_visitOk_right (status : VisitStatus)
    : combineVisitStatus status visitOk = status := by
  cases status with
  | error errors =>
      simp [combineVisitStatus, visitOk, Result.combine,
        GraphQL.Execution.Result.combine]
  | ok result =>
      rcases result with ⟨u, errors⟩
      cases u
      simp [combineVisitStatus, visitOk, Result.combine,
        GraphQL.Execution.Result.combine]

@[simp]
theorem combineVisitStatus_visitOk_left (status : VisitStatus)
    : combineVisitStatus visitOk status = status := by
  cases status with
  | error errors =>
      simp [combineVisitStatus, visitOk, Result.combine,
        GraphQL.Execution.Result.combine]
  | ok result =>
      rcases result with ⟨u, errors⟩
      cases u
      simp [combineVisitStatus, visitOk, Result.combine,
        GraphQL.Execution.Result.combine]

@[simp]
theorem combineVisitStatus_assoc (left middle right : VisitStatus)
    : combineVisitStatus (combineVisitStatus left middle) right
      = combineVisitStatus left (combineVisitStatus middle right) := by
  cases left with
  | error leftErrors =>
      cases middle with
      | error middleErrors =>
          cases right with
          | error rightErrors =>
              simp [combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine, Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨u, rightErrors⟩
              cases u
              simp [combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine, Nat.add_assoc]
      | ok middleResult =>
          rcases middleResult with ⟨u, middleErrors⟩
          cases u
          cases right with
          | error rightErrors =>
              simp [combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine, Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨u, rightErrors⟩
              cases u
              simp [combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine, Nat.add_assoc]
  | ok leftResult =>
      rcases leftResult with ⟨u, leftErrors⟩
      cases u
      cases middle with
      | error middleErrors =>
          cases right with
          | error rightErrors =>
              simp [combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine, Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨u, rightErrors⟩
              cases u
              simp [combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine, Nat.add_assoc]
      | ok middleResult =>
          rcases middleResult with ⟨u, middleErrors⟩
          cases u
          cases right with
          | error rightErrors =>
              simp [combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine, Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨u, rightErrors⟩
              cases u
              simp [combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine, Nat.add_assoc]

@[simp]
theorem combineVisitStatus_comm (left right : VisitStatus)
    : combineVisitStatus left right = combineVisitStatus right left := by
  cases left with
  | error leftErrors =>
      cases right with
      | error rightErrors =>
          simp [combineVisitStatus, Result.combine,
            GraphQL.Execution.Result.combine, Nat.add_comm]
      | ok rightResult =>
          rcases rightResult with ⟨unitValue, rightErrors⟩
          cases unitValue
          simp [combineVisitStatus, Result.combine,
            GraphQL.Execution.Result.combine, Nat.add_comm]
  | ok leftResult =>
      rcases leftResult with ⟨unitValue, leftErrors⟩
      cases unitValue
      cases right with
      | error rightErrors =>
          simp [combineVisitStatus, Result.combine,
            GraphQL.Execution.Result.combine, Nat.add_comm]
      | ok rightResult =>
          rcases rightResult with ⟨unitValue, rightErrors⟩
          cases unitValue
          simp [combineVisitStatus, Result.combine,
            GraphQL.Execution.Result.combine, Nat.add_comm]

theorem reusablePreviousValue?_some_eq (schema : Schema)
    : ∀ (fieldType : TypeRef) (previous? : Option ResponseValue)
          (previous : ResponseValue),
        reusablePreviousValue? schema fieldType previous? = some previous
        -> previous? = some previous := by
  intro fieldType previous? previous h
  cases previous? with
  | none =>
      simp [reusablePreviousValue?] at h
  | some original =>
      cases original with
      | null =>
          simp [reusablePreviousValue?] at h
          cases h
          rfl
      | scalar value =>
          by_cases hcomposite : fieldType.isCompositeBool schema
          · simp [reusablePreviousValue?, hcomposite] at h
          · simp [reusablePreviousValue?, hcomposite] at h
            cases h
            rfl
      | object fields =>
          by_cases hcomposite : fieldType.isCompositeBool schema
          · simp [reusablePreviousValue?, hcomposite] at h
          · simp [reusablePreviousValue?, hcomposite] at h
            cases h
            rfl
      | list values =>
          by_cases hcomposite : fieldType.isCompositeBool schema
          · simp [reusablePreviousValue?, hcomposite] at h
          · simp [reusablePreviousValue?, hcomposite] at h
            cases h
            rfl

theorem reusablePreviousValue?_none (schema : Schema)
    : ∀ fieldType : TypeRef, reusablePreviousValue? schema fieldType none = none := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      simp [reusablePreviousValue?]
  | list inner ih =>
      simp [reusablePreviousValue?]
  | nonNull inner ih =>
      simp [reusablePreviousValue?]

theorem reusablePreviousValue?_null (schema : Schema)
    : ∀ fieldType : TypeRef,
        reusablePreviousValue? schema fieldType (some .null) = some .null := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      simp [reusablePreviousValue?]
  | list inner ih =>
      simp [reusablePreviousValue?]
  | nonNull inner ih =>
      simp [reusablePreviousValue?]

theorem reusablePreviousValue?_scalar (schema : Schema) (value : String)
    : ∀ fieldType : TypeRef,
        fieldType.isCompositeBool schema = false
        -> reusablePreviousValue? schema fieldType (some (.scalar value))
            = some (.scalar value) := by
  intro fieldType hcomposite
  simp [reusablePreviousValue?, hcomposite]

theorem completeResolvedValue_previous_null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (fieldType : TypeRef) (selectionSet : List Selection)
    (resolved : ResolverValue ObjectIdentity)
    : completeResolvedValue schema resolvers variableValues depth fieldType
        selectionSet resolved (some .null)
      = .ok (.null, 0) := by
  unfold completeResolvedValue
  rw [reusablePreviousValue?_null schema fieldType]

theorem completeResolvedValue_previous_scalar
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (fieldType : TypeRef) (selectionSet : List Selection)
    (resolved : ResolverValue ObjectIdentity) (value : String)
    (hcomposite : fieldType.isCompositeBool schema = false)
    : completeResolvedValue schema resolvers variableValues depth fieldType
        selectionSet resolved (some (.scalar value))
      = .ok (.scalar value, 0) := by
  unfold completeResolvedValue
  rw [reusablePreviousValue?_scalar schema value fieldType hcomposite]

theorem completeResolvedValue_nonNull_eq_nonNullCompletion_of_previous_ne_null
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (inner : TypeRef) (selectionSet : List Selection)
    (resolved : ResolverValue ObjectIdentity)
    (previous? : Option ResponseValue)
    (hprevious : previous? ≠ some .null)
    : completeResolvedValue schema resolvers variableValues depth (.nonNull inner)
        selectionSet resolved previous?
      = nonNullCompletion
          (completeResolvedValue schema resolvers variableValues depth inner
            selectionSet resolved previous?) := by
  cases previous? with
  | none =>
      simp [completeResolvedValue, reusablePreviousValue?]
  | some previous =>
      cases previous with
      | null =>
          exact False.elim (hprevious rfl)
      | scalar value =>
          by_cases hcomposite : inner.isCompositeBool schema = true
          · have houterComposite :
                (TypeRef.nonNull inner).isCompositeBool schema = true := by
              simpa [TypeRef.isCompositeBool, TypeRef.namedType] using
                hcomposite
            simp [completeResolvedValue, reusablePreviousValue?,
              houterComposite]
          · have hinnerNonComposite :
                inner.isCompositeBool schema = false := by
              cases h : inner.isCompositeBool schema <;>
                simp [h] at hcomposite ⊢
            have houterNonComposite :
                (TypeRef.nonNull inner).isCompositeBool schema = false := by
              simpa [TypeRef.isCompositeBool, TypeRef.namedType] using
                hinnerNonComposite
            have hinnerCompleted :
                completeResolvedValue schema resolvers variableValues depth inner
                  selectionSet resolved (some (.scalar value)) =
                .ok (.scalar value, 0) :=
              completeResolvedValue_previous_scalar schema resolvers
                variableValues depth inner selectionSet resolved value
                hinnerNonComposite
            simp [completeResolvedValue, reusablePreviousValue?,
              houterNonComposite, hinnerCompleted, nonNullCompletion]
      | object fields =>
          by_cases hcomposite : inner.isCompositeBool schema = true
          · have houterComposite :
                (TypeRef.nonNull inner).isCompositeBool schema = true := by
              simpa [TypeRef.isCompositeBool, TypeRef.namedType] using
                hcomposite
            simp [completeResolvedValue, reusablePreviousValue?,
              houterComposite]
          · have hinnerNonComposite :
                inner.isCompositeBool schema = false := by
              cases h : inner.isCompositeBool schema <;>
                simp [h] at hcomposite ⊢
            have houterNonComposite :
                (TypeRef.nonNull inner).isCompositeBool schema = false := by
              simpa [TypeRef.isCompositeBool, TypeRef.namedType] using
                hinnerNonComposite
            have hinnerReuse :
                reusablePreviousValue? schema inner
                    (some (.object fields)) =
                  some (.object fields) := by
              simp [reusablePreviousValue?, hinnerNonComposite]
            have hinnerCompleted :
                completeResolvedValue schema resolvers variableValues depth inner
                  selectionSet resolved (some (.object fields)) =
                .ok (.object fields, 0) := by
              unfold completeResolvedValue
              rw [hinnerReuse]
            simp [completeResolvedValue, reusablePreviousValue?,
              houterNonComposite, hinnerCompleted, nonNullCompletion]
      | list values =>
          by_cases hcomposite : inner.isCompositeBool schema = true
          · have houterComposite :
                (TypeRef.nonNull inner).isCompositeBool schema = true := by
              simpa [TypeRef.isCompositeBool, TypeRef.namedType] using
                hcomposite
            simp [completeResolvedValue, reusablePreviousValue?,
              houterComposite]
          · have hinnerNonComposite :
                inner.isCompositeBool schema = false := by
              cases h : inner.isCompositeBool schema <;>
                simp [h] at hcomposite ⊢
            have houterNonComposite :
                (TypeRef.nonNull inner).isCompositeBool schema = false := by
              simpa [TypeRef.isCompositeBool, TypeRef.namedType] using
                hinnerNonComposite
            have hinnerReuse :
                reusablePreviousValue? schema inner (some (.list values)) =
                  some (.list values) := by
              simp [reusablePreviousValue?, hinnerNonComposite]
            have hinnerCompleted :
                completeResolvedValue schema resolvers variableValues depth inner
                  selectionSet resolved (some (.list values)) =
                .ok (.list values, 0) := by
              unfold completeResolvedValue
              rw [hinnerReuse]
            simp [completeResolvedValue, reusablePreviousValue?,
              houterNonComposite, hinnerCompleted, nonNullCompletion]

theorem completeResolvedValue_nonNull_ok_of_inner_ok
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (inner : TypeRef) (selectionSet : List Selection)
    (resolved : ResolverValue ObjectIdentity) (previous? : Option ResponseValue)
    (value : ResponseValue) (errors : Nat)
    (hinner
      : completeResolvedValue schema resolvers variableValues depth inner
          selectionSet resolved previous?
        = .ok (value, errors))
    (hnonNull : value ≠ .null)
    : completeResolvedValue schema resolvers variableValues depth (.nonNull inner)
        selectionSet resolved previous?
      = .ok (value, errors) := by
  cases hreuse : reusablePreviousValue? schema (.nonNull inner) previous? with
  | some previous =>
      have hprevious :
          previous? = some previous :=
        reusablePreviousValue?_some_eq schema (.nonNull inner) previous?
          previous hreuse
      cases hprevious
      have hinner' :
          completeResolvedValue schema resolvers variableValues depth inner
            selectionSet resolved (some previous) = .ok (previous, 0) := by
        cases previous with
        | null =>
            exact completeResolvedValue_previous_null schema resolvers
              variableValues depth inner selectionSet resolved
        | scalar scalarValue =>
            have hreuseInner :
                reusablePreviousValue? schema inner (some (.scalar scalarValue)) =
                  some (.scalar scalarValue) := by
              have houterNonComposite :
                  (TypeRef.nonNull inner).isCompositeBool schema = false := by
                cases hcomposite :
                    (TypeRef.nonNull inner).isCompositeBool schema <;>
                  simp [reusablePreviousValue?, hcomposite] at hreuse ⊢
              have hinnerNonComposite :
                  inner.isCompositeBool schema = false := by
                simpa [TypeRef.isCompositeBool, TypeRef.namedType] using
                  houterNonComposite
              simp [reusablePreviousValue?, hinnerNonComposite]
            unfold completeResolvedValue
            rw [hreuseInner]
        | object fields =>
            have hreuseInner :
                reusablePreviousValue? schema inner (some (.object fields)) =
                  some (.object fields) := by
              have houterNonComposite :
                  (TypeRef.nonNull inner).isCompositeBool schema = false := by
                cases hcomposite :
                    (TypeRef.nonNull inner).isCompositeBool schema <;>
                  simp [reusablePreviousValue?, hcomposite] at hreuse ⊢
              have hinnerNonComposite :
                  inner.isCompositeBool schema = false := by
                simpa [TypeRef.isCompositeBool, TypeRef.namedType] using
                  houterNonComposite
              simp [reusablePreviousValue?, hinnerNonComposite]
            unfold completeResolvedValue
            rw [hreuseInner]
        | list values =>
            have hreuseInner :
                reusablePreviousValue? schema inner (some (.list values)) =
                  some (.list values) := by
              have houterNonComposite :
                  (TypeRef.nonNull inner).isCompositeBool schema = false := by
                cases hcomposite :
                    (TypeRef.nonNull inner).isCompositeBool schema <;>
                  simp [reusablePreviousValue?, hcomposite] at hreuse ⊢
              have hinnerNonComposite :
                  inner.isCompositeBool schema = false := by
                simpa [TypeRef.isCompositeBool, TypeRef.namedType] using
                  houterNonComposite
              simp [reusablePreviousValue?, hinnerNonComposite]
            unfold completeResolvedValue
            rw [hreuseInner]
      rw [hinner'] at hinner
      cases hinner
      simp [completeResolvedValue, hreuse]
  | none =>
      simp [completeResolvedValue, hreuse, hinner, nonNullCompletion]

theorem terminalPreviousValue?_some_eq
    : ∀ (previous? : Option ResponseValue) (previous : ResponseValue),
        terminalPreviousValue? previous? = some previous
        -> previous? = some previous := by
  intro previous? previous h
  cases previous? with
  | none =>
      simp [terminalPreviousValue?] at h
  | some original =>
      cases original <;> simp [terminalPreviousValue?] at h <;>
        cases h <;> rfl

theorem reusableOrComplete_eq_completeResolvedValue
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (selectionSet : List Selection) (resolved : ResolverValue ObjectIdentity)
    : ∀ (fieldType : TypeRef) (previous : ResponseValue),
        (match reusablePreviousValue? schema fieldType (some previous) with
          | some previous => .ok (previous, 0)
          | none =>
              completeValue schema resolvers variableValues (depth + 1) fieldType
                selectionSet resolved (some previous))
        = completeResolvedValue schema resolvers variableValues (depth + 1) fieldType
            selectionSet resolved (some previous) := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      intro previous
      cases previous with
      | null =>
          simp [completeResolvedValue, reusablePreviousValue?]
      | scalar value =>
          by_cases hcomposite : (TypeRef.named typeName).isCompositeBool schema
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite,
              completeValue]
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite]
      | object fields =>
          by_cases hcomposite : (TypeRef.named typeName).isCompositeBool schema
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite]
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite]
      | list values =>
          by_cases hcomposite : (TypeRef.named typeName).isCompositeBool schema
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite]
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite]
  | list inner ih =>
      intro previous
      cases previous with
      | null =>
          simp [completeResolvedValue, reusablePreviousValue?_null]
      | scalar value =>
          by_cases hcomposite : inner.list.isCompositeBool schema
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite,
              completeValue]
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite]
      | object fields =>
          by_cases hcomposite : inner.list.isCompositeBool schema
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite]
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite]
      | list values =>
          by_cases hcomposite : inner.list.isCompositeBool schema
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite]
          · simp [completeResolvedValue, reusablePreviousValue?, hcomposite]
  | nonNull inner ih =>
      intro previous
      cases houter : reusablePreviousValue? schema (.nonNull inner) (some previous) with
      | some reused =>
          have hreused :
              some previous = some reused :=
            reusablePreviousValue?_some_eq schema (.nonNull inner)
              (some previous) reused houter
          cases hreused
          simp [completeResolvedValue, houter]
      | none =>
          have hinner := ih previous
          have hinnerNone :
              reusablePreviousValue? schema inner (some previous) = none := by
            cases previous <;>
              simp [reusablePreviousValue?, TypeRef.isCompositeBool,
                TypeRef.namedType] at houter ⊢ <;>
              exact houter
          have hinnerEq :
              completeValue schema resolvers variableValues (depth + 1)
                  inner selectionSet resolved (some previous) =
                completeResolvedValue schema resolvers variableValues (depth + 1)
                  inner selectionSet resolved (some previous) := by
            simpa [hinnerNone] using hinner
          cases previous with
          | null =>
              simp [reusablePreviousValue?] at houter
          | scalar value =>
              have hcomplete :
                  completeValue schema resolvers variableValues (depth + 1)
                      inner selectionSet resolved (some (.scalar value)) =
                    .error 1 := by
                simp [completeValue]
              have hresolved :
                  completeResolvedValue schema resolvers variableValues
                      (depth + 1) inner selectionSet resolved
                      (some (.scalar value)) =
                    .error 1 := by
                simpa [hcomplete] using hinnerEq.symm
              simp [completeResolvedValue, houter, completeValue,
                nonNullCompletion, hresolved]
          | object fields =>
              simp [completeResolvedValue, houter, completeValue,
                nonNullCompletion, hinnerEq]
          | list values =>
              simp [completeResolvedValue, houter, completeValue,
                nonNullCompletion, hinnerEq]

theorem executeField_resolved_eq_completeResolvedValue
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (fieldDefinition : FieldDefinition) (resolved : ResolverValue ObjectIdentity)
    (previous : ResponseValue)
    (hlookup : schema.lookupField field.parentType field.fieldName = some fieldDefinition)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = some resolved)
    : executeField schema resolvers variableValues (depth + 1) source (some previous)
        field
      = completeResolvedValue schema resolvers variableValues (depth + 1)
          fieldDefinition.outputType field.selectionSet resolved (some previous) := by
  cases previous with
  | null =>
      simp [executeField, hlookup, reusablePreviousValue?_null,
        completeResolvedValue_previous_null]
  | scalar value =>
      unfold executeField
      rw [hlookup, hresolve]
      exact reusableOrComplete_eq_completeResolvedValue schema resolvers
        variableValues depth field.selectionSet resolved
        fieldDefinition.outputType (.scalar value)
  | object fields =>
      unfold executeField
      rw [hlookup, hresolve]
      exact reusableOrComplete_eq_completeResolvedValue schema resolvers
        variableValues depth field.selectionSet resolved
        fieldDefinition.outputType (.object fields)
  | list values =>
      unfold executeField
      rw [hlookup, hresolve]
      exact reusableOrComplete_eq_completeResolvedValue schema resolvers
        variableValues depth field.selectionSet resolved
        fieldDefinition.outputType (.list values)

theorem executeField_empty_output
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    : executeField schema resolvers variableValues depth source none field
      = match schema.lookupField field.parentType field.fieldName with
        | none => .error 1
        | some fieldDefinition =>
            match resolvers.resolve field.parentType field.fieldName
                    field.arguments source with
            | none => handleFieldError fieldDefinition.outputType
            | some resolved =>
                completeValue schema resolvers variableValues depth
                  fieldDefinition.outputType field.selectionSet resolved none := by
  unfold executeField
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      simp []
  | some fieldDefinition =>
      simp [reusablePreviousValue?_none]
      rfl

theorem executeField_object_fresh_eq_empty_output
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (fields : List (Name × ResponseValue))
    (hfresh : field.responseName ∉ fields.map Prod.fst)
    : executeField schema resolvers variableValues depth source
        (responseObjectField? field.responseName (.object fields))
        field
      = executeField schema resolvers variableValues depth source none field := by
  have hlookup :
      responseObjectField? field.responseName (.object fields) = none := by
    simp [responseObjectField?,
      lookupResponseField?_none_of_not_mem field.responseName fields hfresh]
  simp [hlookup]

theorem executeField_reentry_singleton
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (previous : ResponseValue)
    : executeField schema resolvers variableValues depth source (some previous) field
      = match schema.lookupField field.parentType field.fieldName with
        | none => .error 1
        | some fieldDefinition =>
            match reusablePreviousValue? schema fieldDefinition.outputType
                    (some previous) with
            | some previous => .ok (previous, 0)
            | none =>
                match resolvers.resolve field.parentType field.fieldName
                        field.arguments source with
                | none => handleFieldError fieldDefinition.outputType
                | some resolved =>
                    completeValue schema resolvers variableValues depth
                      fieldDefinition.outputType field.selectionSet resolved
                      (some previous) := by
  unfold executeField
  rfl

theorem executeField_reentry_of_lookup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (fields : List (Name × ResponseValue)) (previous : ResponseValue)
    (hlookup : responseObjectField? field.responseName (.object fields) = some previous)
    : executeField schema resolvers variableValues depth source (some previous) field
      = executeField schema resolvers variableValues depth source
          (responseObjectField? field.responseName (.object fields))
          field := by
  simp [hlookup]

theorem executeField_object_append_of_lookup_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (fields suffix : List (Name × ResponseValue)) (previous : ResponseValue)
    (hlookup : responseObjectField? field.responseName (.object fields) = some previous)
    : executeField schema resolvers variableValues depth source
        (responseObjectField? field.responseName (.object (fields ++ suffix)))
        field
      = executeField schema resolvers variableValues depth source
          (responseObjectField? field.responseName (.object fields))
          field := by
  have hlookupAppend :
      responseObjectField? field.responseName (.object (fields ++ suffix)) =
        some previous :=
    responseObjectField?_object_append_of_some_left field.responseName fields
      suffix previous hlookup
  simp [hlookup, hlookupAppend]

theorem executeField_object_append_of_mem_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (fields suffix : List (Name × ResponseValue))
    (hmem : field.responseName ∈ fields.map Prod.fst)
    : executeField schema resolvers variableValues depth source
        (responseObjectField? field.responseName (.object (fields ++ suffix)))
        field
      = executeField schema resolvers variableValues depth source
          (responseObjectField? field.responseName (.object fields))
          field := by
  rcases lookupResponseField?_some_of_mem field.responseName fields hmem with
    ⟨previous, hlookup⟩
  exact
    executeField_object_append_of_lookup_eq schema resolvers variableValues
      depth source field fields suffix previous
      (by simpa [responseObjectField?] using hlookup)

theorem executeField_reentry_after_merge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (fields : List (Name × ResponseValue)) (incoming : ResponseValue)
    : let output :=
        mergeResponseFieldIntoObject field.responseName incoming (.object fields)
      executeField schema resolvers variableValues depth source
        (responseObjectField? field.responseName output)
        field
      = executeField schema resolvers variableValues depth source
          (match responseObjectField? field.responseName (.object fields) with
            | some existing => some (mergeResponse existing incoming)
            | none => some incoming)
          field := by
    intro output
    simp [output, responseObjectField?_mergeResponseFieldIntoObject_same]
    cases responseObjectField? field.responseName (.object fields) <;> rfl

theorem completeValue_null_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (previous? : Option ResponseValue)
    : resultValueOrNull
        (completeValue schema resolvers variableValues (depth + 1) parentType
          selectionSet (.null : ResolverValue ObjectIdentity) previous?)
      = GraphQL.Execution.completeValueData schema resolvers variableValues (depth + 1)
          parentType fields (.null : ResolverValue ObjectIdentity) := by
  cases previous? with
  | none =>
      simp [resultValueOrNull, GraphQL.Algorithms.ExecutionUngroupedUncached.Eager.completeValue,
        GraphQL.Execution.completeValueData,
        GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD]
  | some previous =>
      cases previous <;>
        simp [resultValueOrNull,
          GraphQL.Algorithms.ExecutionUngroupedUncached.Eager.completeValue,
          GraphQL.Execution.completeValueData,
          GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD]

theorem completeValue_zero_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (value : ResolverValue ObjectIdentity) (previous? : Option ResponseValue)
    : resultValueOrNull
        (completeValue schema resolvers variableValues 0 parentType selectionSet
          value previous?)
      = GraphQL.Execution.completeValueData schema resolvers variableValues 0
          parentType fields value := by
  cases value
  <;> cases previous? with
  | none =>
      simp [GraphQL.Algorithms.ExecutionUngroupedUncached.Eager.completeValue,
        GraphQL.Execution.completeValueData, GraphQL.Execution.completeValue,
        GraphQL.Execution.Result.getD, resultValueOrNull, outOfFuel]
  | some previous =>
      cases previous <;>
        simp [GraphQL.Algorithms.ExecutionUngroupedUncached.Eager.completeValue,
          GraphQL.Execution.completeValueData, GraphQL.Execution.completeValue,
          GraphQL.Execution.Result.getD, resultValueOrNull, outOfFuel]

theorem completeValue_scalar_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (value : String) (previous? : Option ResponseValue)
    (hprevious : previous? = none)
    : resultValueOrNull
        (completeValue schema resolvers variableValues (depth + 1) parentType
          selectionSet (.scalar value : ResolverValue ObjectIdentity) previous?)
      = GraphQL.Execution.completeValueData schema resolvers variableValues (depth + 1)
          parentType fields (.scalar value : ResolverValue ObjectIdentity) := by
  subst previous?
  by_cases hcomposite :
      (TypeRef.named parentType).isCompositeBool schema = true <;>
    simp [resultValueOrNull,
      GraphQL.Algorithms.ExecutionUngroupedUncached.Eager.completeValue,
      GraphQL.Execution.completeValueData,
      GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD,
      hcomposite]

theorem completeValue_object_eq_visitSubfields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) (previous? : Option ResponseValue)
    : completeValue schema resolvers variableValues (depth + 1) parentType
        selectionSet (.object runtimeType identity) previous?
      = match previous? with
        | none =>
            if schema.typeIncludesObjectBool parentType runtimeType then
              let visited :=
                visitSubfields schema resolvers variableValues depth runtimeType
                  (.object runtimeType identity) selectionSet (.object [])
              catchVisitBubbleAsNull visited.fst visited.snd
            else
              .error 1
        | some .null => .ok (.null, 0)
        | some previous@(.object _fields) =>
            if schema.typeIncludesObjectBool parentType runtimeType then
              let visited :=
                visitSubfields schema resolvers variableValues depth runtimeType
                  (.object runtimeType identity) selectionSet
                  previous
              catchVisitBubbleAsNull visited.fst visited.snd
            else
              .error 1
        | _ => .error 1 := by
  cases previous? with
  | none =>
      simp [GraphQL.Algorithms.ExecutionUngroupedUncached.Eager.completeValue,
        reuseOrCreateObject?]
  | some previous =>
      cases previous <;>
        simp [GraphQL.Algorithms.ExecutionUngroupedUncached.Eager.completeValue,
          reuseOrCreateObject?]

def scalarCompletionAtDepth (schema : Schema) (parentType : Name)
    (depth : Nat) (value : String)
    : ResponseValue :=
  match depth with
  | 0 => .null
  | _ + 1 =>
      if (TypeRef.named parentType).isCompositeBool schema then
        .null
      else
        .scalar value

theorem completeValue_scalar_any_depth_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    (value : String) (previous? : Option ResponseValue)
    (hprevious : depth = 0 ∨ previous? = none)
    : resultValueOrNull
        (completeValue schema resolvers variableValues depth parentType selectionSet
          (.scalar value : ResolverValue ObjectIdentity) previous?)
      = GraphQL.Execution.completeValueData schema resolvers variableValues depth
          parentType fields (.scalar value : ResolverValue ObjectIdentity) := by
  cases depth with
  | zero =>
      exact completeValue_zero_eq_spec schema resolvers variableValues
        parentType selectionSet fields (.scalar value) previous?
  | succ depth =>
      exact completeValue_scalar_eq_spec schema resolvers variableValues depth
        parentType selectionSet fields value previous? (by
          rcases hprevious with hzero | hprevious
          · contradiction
          · exact hprevious)

theorem completeValue_scalar_any_depth_eq_scalar
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection)
    (value : String) (previous? : Option ResponseValue)
    : resultValueOrNull
        (completeValue schema resolvers variableValues depth parentType selectionSet
          (.scalar value : ResolverValue ObjectIdentity) previous?)
      = match previous? with
        | none => scalarCompletionAtDepth schema parentType depth value
        | some _ => .null := by
  cases depth with
  | zero =>
      cases previous? with
      | none =>
          simp [completeValue, outOfFuel, resultValueOrNull, scalarCompletionAtDepth]
      | some previous =>
          cases previous <;>
            simp [completeValue, outOfFuel, resultValueOrNull]
  | succ depth =>
      cases previous? with
      | none =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true <;>
            simp [completeValue, resultValueOrNull, scalarCompletionAtDepth,
              hcomposite]
      | some previous =>
          cases previous <;>
            simp [completeValue, resultValueOrNull]

theorem spec_completeValue_scalar_any_depth_eq_scalar
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (fields : List ExecutableField) (value : String)
    : GraphQL.Execution.completeValueData schema resolvers variableValues depth
        parentType fields (.scalar value : ResolverValue ObjectIdentity)
      = scalarCompletionAtDepth schema parentType depth value := by
  cases depth with
  | zero =>
      simp [GraphQL.Execution.completeValueData, GraphQL.Execution.completeValue,
        GraphQL.Execution.Result.getD, outOfFuel, scalarCompletionAtDepth]
  | succ depth =>
      by_cases hcomposite :
          (TypeRef.named parentType).isCompositeBool schema = true <;>
        simp [GraphQL.Execution.completeValueData, GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD, scalarCompletionAtDepth, hcomposite]

theorem completeValue_duplicate_scalar_merge_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection)
    (fields : List ExecutableField) (value : String)
    (hspecNull : scalarCompletionAtDepth schema parentType depth value = .null)
    : let first :=
        resultValueOrNull
          (completeValue schema resolvers variableValues depth parentType
            firstSelectionSet (.scalar value : ResolverValue ObjectIdentity)
            none)
      mergeResponse first
        (resultValueOrNull
          (completeValue schema resolvers variableValues depth parentType
            secondSelectionSet (.scalar value : ResolverValue ObjectIdentity)
            (some first)))
      = GraphQL.Execution.completeValueData schema resolvers variableValues depth
          parentType fields (.scalar value : ResolverValue ObjectIdentity) := by
  cases depth with
  | zero =>
      simp [completeValue_scalar_any_depth_eq_scalar,
        spec_completeValue_scalar_any_depth_eq_scalar, scalarCompletionAtDepth,
        mergeResponse]
  | succ depth =>
      by_cases hcomposite :
          (TypeRef.named parentType).isCompositeBool schema = true <;>
        simp [scalarCompletionAtDepth, hcomposite] at hspecNull <;>
        simp [completeValue_scalar_any_depth_eq_scalar,
          spec_completeValue_scalar_any_depth_eq_scalar, scalarCompletionAtDepth,
          mergeResponse, hcomposite]

theorem completeValue_duplicate_null_merge_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection)
    (fields : List ExecutableField)
    : let first :=
        resultValueOrNull
          (completeValue schema resolvers variableValues depth parentType
            firstSelectionSet (.null : ResolverValue ObjectIdentity)
            none)
      mergeResponse first
        (resultValueOrNull
          (completeValue schema resolvers variableValues depth parentType
            secondSelectionSet (.null : ResolverValue ObjectIdentity)
            (some first)))
      = GraphQL.Execution.completeValueData schema resolvers variableValues depth
          parentType fields (.null : ResolverValue ObjectIdentity) := by
  cases depth <;>
    simp [resultValueOrNull, GraphQL.Algorithms.ExecutionUngroupedUncached.Eager.completeValue,
      GraphQL.Execution.completeValueData, GraphQL.Execution.completeValue,
      GraphQL.Execution.Result.getD, outOfFuel, mergeResponse]

theorem completeValue_scalar_list_fold_fst
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection)
    (values : List String) (acc : List ResponseValue)
    : (List.foldl
        (fun (state : List ResponseValue × List ResponseValue)
            (value : ResolverValue ObjectIdentity) =>
          (
            resultValueOrNull
              (completeValue schema resolvers variableValues depth parentType
                selectionSet value
                (match state.snd with
                  | [] => none
                  | previous :: _rest => some previous))
            :: state.fst,
            match state.snd with
            | [] => []
            | _previous :: rest => rest
          ))
        (acc, [])
        (values.map (fun value => (.scalar value : ResolverValue ObjectIdentity)))).fst
      = (values.map (scalarCompletionAtDepth schema parentType depth)).reverse
        ++ acc := by
  induction values generalizing acc with
  | nil =>
      simp
  | cons value rest ih =>
      simpa [completeValue_scalar_any_depth_eq_scalar, List.append_assoc]
        using ih (scalarCompletionAtDepth schema parentType depth value :: acc)

theorem completeValue_scalar_list_fold_reverse
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection)
    (values : List String)
    : (List.foldl
        (fun (state : List ResponseValue × List ResponseValue)
            (value : ResolverValue ObjectIdentity) =>
          (
            resultValueOrNull
              (completeValue schema resolvers variableValues depth parentType
                selectionSet value
                (match state.snd with
                  | [] => none
                  | previous :: _rest => some previous))
            :: state.fst,
            match state.snd with
            | [] => []
            | _previous :: rest => rest
          ))
        ([], [])
        (values.map
          (fun value => (.scalar value : ResolverValue ObjectIdentity)))).fst.reverse
      = values.map (scalarCompletionAtDepth schema parentType depth) := by
  rw [completeValue_scalar_list_fold_fst schema resolvers variableValues depth
    parentType selectionSet values []]
  simp

theorem spec_completeValue_scalar_list_map
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (fields : List ExecutableField) (values : List String)
    : List.map
        ((fun value =>
            GraphQL.Execution.completeValueData schema resolvers variableValues depth
              parentType fields value)
          ∘ fun value => (.scalar value : ResolverValue ObjectIdentity))
        values
      = values.map (scalarCompletionAtDepth schema parentType depth) := by
  induction values with
  | nil =>
      simp
  | cons value rest ih =>
      simp [Function.comp_apply,
        spec_completeValue_scalar_any_depth_eq_scalar, ih]

theorem completeValue_list_fold_empty_previous_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    : ∀ (values : List (ResolverValue ObjectIdentity)) (acc : List ResponseValue),
        (∀ value,
          value ∈ values
          -> resultValueOrNull
                (completeValue schema resolvers variableValues depth parentType
                  selectionSet value none)
              = GraphQL.Execution.completeValueData schema resolvers variableValues
                  depth parentType fields value)
        -> (List.foldl
              (fun (state : List ResponseValue × List ResponseValue)
                  (value : ResolverValue ObjectIdentity) =>
                (
                  resultValueOrNull
                    (completeValue schema resolvers variableValues depth parentType
                      selectionSet value
                      (match state.snd with
                        | [] => none
                        | previous :: _rest => some previous))
                  :: state.fst,
                  match state.snd with
                  | [] => []
                  | _previous :: rest => rest
                ))
              (acc, [])
              values).fst
            = (values.map
                (fun value =>
                  GraphQL.Execution.completeValueData schema resolvers variableValues
                    depth parentType fields value)).reverse
              ++ acc
  | [], acc, _hvalues => by
      simp
  | value :: rest, acc, hvalues => by
      have hvalue :
          resultValueOrNull
            (completeValue schema resolvers variableValues depth parentType
              selectionSet value none) =
          GraphQL.Execution.completeValueData schema resolvers variableValues depth
            parentType fields value :=
        hvalues value (by simp)
      have hrest :
          ∀ restValue, restValue ∈ rest ->
            resultValueOrNull
              (completeValue schema resolvers variableValues depth parentType
                selectionSet restValue none) =
            GraphQL.Execution.completeValueData schema resolvers variableValues depth
              parentType fields restValue := by
        intro restValue hmem
        exact hvalues restValue (by simp [hmem])
      simp [hvalue,
        completeValue_list_fold_empty_previous_eq_spec schema resolvers
          variableValues depth parentType selectionSet fields rest
          (GraphQL.Execution.completeValueData schema resolvers variableValues
            depth parentType fields value :: acc)
          hrest,
        List.append_assoc]

theorem completeValue_list_fold_empty_previous_eq_map
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (selectionSet : List Selection)
    : ∀ (values : List (ResolverValue ObjectIdentity)) (acc : List ResponseValue),
        (List.foldl
          (fun (state : List ResponseValue × List ResponseValue)
              (value : ResolverValue ObjectIdentity) =>
            (
              resultValueOrNull
                (completeValue schema resolvers variableValues depth parentType
                  selectionSet value
                  (match state.snd with
                    | [] => none
                    | previous :: _rest => some previous))
              :: state.fst,
              match state.snd with
              | [] => []
              | _previous :: rest => rest
            ))
          (acc, [])
          values).fst
        = (values.map
            (fun value =>
              resultValueOrNull
                (completeValue schema resolvers variableValues depth parentType
                  selectionSet value none))).reverse
          ++ acc
  | [], acc => by
      simp
  | value :: rest, acc => by
      simp [completeValue_list_fold_empty_previous_eq_map schema resolvers
        variableValues depth parentType selectionSet rest
        (resultValueOrNull
          (completeValue schema resolvers variableValues depth parentType
            selectionSet value none) :: acc), List.append_assoc]

theorem completeValue_list_fold_previous_map_eq_map
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (firstSelectionSet secondSelectionSet : List Selection)
    : ∀ (values : List (ResolverValue ObjectIdentity)) (acc : List ResponseValue),
        (List.foldl
          (fun (state : List ResponseValue × List ResponseValue)
              (value : ResolverValue ObjectIdentity) =>
            (
              resultValueOrNull
                (completeValue schema resolvers variableValues depth parentType
                  secondSelectionSet value
                  (match state.snd with
                    | [] => none
                    | previous :: _rest => some previous))
              :: state.fst,
              match state.snd with
              | [] => []
              | _previous :: rest => rest
            ))
          (
            acc,
            values.map
              (fun value =>
                resultValueOrNull
                  (completeValue schema resolvers variableValues depth parentType
                    firstSelectionSet value none))
          )
          values).fst
        = (values.map
            (fun value =>
              resultValueOrNull
                (completeValue schema resolvers variableValues depth parentType
                  secondSelectionSet value
                  (some
                    (resultValueOrNull
                      (completeValue schema resolvers variableValues depth parentType
                        firstSelectionSet value none)))))).reverse
          ++ acc
  | [], acc => by
      simp
  | value :: rest, acc => by
      simp [completeValue_list_fold_previous_map_eq_map schema resolvers
        variableValues depth parentType firstSelectionSet secondSelectionSet
        rest
        (resultValueOrNull
          (completeValue schema resolvers variableValues depth parentType
            secondSelectionSet value
            (some (resultValueOrNull
              (completeValue schema resolvers variableValues depth parentType
                firstSelectionSet value none)))) :: acc),
        List.append_assoc]

theorem mergeResponseLists_map_of_forall
    {α : Type} (values : List α)
    (left right merged : α -> ResponseValue)
    : (∀ value, value ∈ values -> mergeResponse (left value) (right value) = merged value)
      -> mergeResponseLists (values.map left) (values.map right) = values.map merged := by
  intro hvalues
  induction values with
  | nil =>
      simp [mergeResponseLists]
  | cons value rest ih =>
      have hvalue : mergeResponse (left value) (right value) = merged value :=
        hvalues value (by simp)
      have hrest :
          ∀ restValue, restValue ∈ rest ->
            mergeResponse (left restValue) (right restValue) =
              merged restValue := by
        intro restValue hmem
        exact hvalues restValue (by simp [hmem])
      simp [mergeResponseLists, hvalue, ih hrest]

theorem visitSelection_field_directives_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : visitSelection schema resolvers variableValues depth parentType source
        (.field responseName fieldName arguments directives selectionSet) output
      = (output, visitOk) := by
  unfold visitSelection
  simp [hblocked]

theorem visitSelection_field_depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : visitSelection schema resolvers variableValues 0 parentType source
        (.field responseName fieldName arguments directives selectionSet) output
      = let previous? := responseObjectField? responseName output
        let fieldResult :=
          match previous? with
          | some previous => .ok (previous, 0)
          | none => outOfFuel
        mergeResponseFieldResult responseName fieldResult output := by
  unfold visitSelection
  simp [hallowed, outOfFuel]
  rfl

theorem visitSelection_field_allowed_succ
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : visitSelection schema resolvers variableValues (depth + 1) parentType source
        (.field responseName fieldName arguments directives selectionSet) output
      = let previous? := responseObjectField? responseName output
        let field :=
          executableField parentType responseName fieldName arguments selectionSet
        mergeResponseFieldResult responseName
          (executeField schema resolvers variableValues depth source previous? field)
          output := by
  unfold visitSelection
  simp [hallowed]

theorem visitSelection_field_allowed_succ_fresh_eq_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × ResponseValue))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh : responseName ∉ fields.map Prod.fst)
    : visitSelection schema resolvers variableValues (depth + 1)
        parentType source
        (.field responseName fieldName arguments directives selectionSet)
        (.object fields)
      = let fieldResult :=
          executeField schema resolvers variableValues depth source none
            (executableField parentType responseName fieldName arguments selectionSet)
        (
          .object (fields ++ [(responseName, resultValueOrNull fieldResult)]),
          resultStatus fieldResult
        ) := by
  rw [visitSelection_field_allowed_succ schema resolvers variableValues depth
    parentType source responseName fieldName arguments directives selectionSet
    (.object fields) hallowed]
  have hlookup :
      responseObjectField? responseName (.object fields) = none := by
    simp [responseObjectField?,
      lookupResponseField?_none_of_not_mem responseName fields hfresh]
  simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
    hlookup,
    mergeResponseField_of_not_mem responseName
      (resultValueOrNull
        (executeField schema resolvers variableValues depth source none
        (executableField parentType responseName fieldName arguments
          selectionSet)))
      fields hfresh]

theorem visitSubfields_single_field_allowed_succ_fresh_eq_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × ResponseValue))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh : responseName ∉ fields.map Prod.fst)
    : visitSubfields schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet]
        (.object fields)
      = let fieldResult :=
          executeField schema resolvers variableValues depth source none
            (executableField parentType responseName fieldName arguments selectionSet)
        (
          .object (fields ++ [(responseName, resultValueOrNull fieldResult)]),
          resultStatus fieldResult
        ) := by
  have hselection :=
    visitSelection_field_allowed_succ_fresh_eq_append schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet fields hallowed hfresh
  simp [visitSubfields, hselection]

theorem visitSubfields_executableFieldSelections_singleton_succ
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    : visitSubfields schema resolvers variableValues (depth + 1) parentType
        source (executableFieldSelections [field]) (.object [])
      = let fieldResult :=
          executeField schema resolvers variableValues depth source none
            (executableField parentType field.responseName field.fieldName
              field.arguments field.selectionSet)
        (
          .object [(field.responseName, resultValueOrNull fieldResult)],
          resultStatus fieldResult
        ) := by
  simpa [executableFieldSelections, executableFieldSelection] using
    visitSubfields_single_field_allowed_succ_fresh_eq_append schema resolvers
      variableValues depth parentType source field.responseName field.fieldName
      field.arguments [] field.selectionSet [] rfl (by simp)

theorem executeRootSelectionSet_single_field_allowed_succ_eq_executeField_empty
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet]
      = GraphQL.Execution.singleFieldResult responseName
          (executeField schema resolvers variableValues depth source none
            (executableField parentType responseName fieldName arguments
              selectionSet)) := by
  unfold executeRootSelectionSet
  rw [visitSubfields_single_field_allowed_succ_fresh_eq_append schema
    resolvers variableValues depth parentType source responseName fieldName
    arguments directives selectionSet [] hallowed (by simp)]
  cases hfield
        : executeField schema resolvers variableValues depth source none
            (executableField parentType responseName fieldName arguments
              selectionSet) with
  | error errors =>
      simp [GraphQL.Execution.singleFieldResult, resultStatus]
  | ok result =>
      rcases result with ⟨response, errors⟩
      simp [GraphQL.Execution.singleFieldResult, resultValueOrNull, resultStatus, visitOk]

theorem visitSubfields_single_field_allowed_succ_fresh_appends_executeRootSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × ResponseValue))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh : responseName ∉ fields.map Prod.fst)
    : visitSubfields schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet]
        (.object fields)
      = let fieldResult :=
          executeField schema resolvers variableValues depth source none
            (executableField parentType responseName fieldName arguments selectionSet)
        (
          .object (fields ++ [(responseName, resultValueOrNull fieldResult)]),
          resultStatus fieldResult
        ) := by
  exact
    visitSubfields_single_field_allowed_succ_fresh_eq_append schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet fields hallowed hfresh

theorem visitSelection_field_eq_visitSubfields_collectedExecutableFields_collectSelection
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : ResponseValue)
    : visitSelection schema resolvers variableValues depth parentType source
        (.field responseName fieldName arguments directives selectionSet) output
      = visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues parentType
                source
                (.field responseName fieldName arguments directives selectionSet))))
          output := by
  by_cases hallowed :
      selectionDirectivesAllowBool variableValues directives = true
  · cases depth with
    | zero =>
        simp [visitSelection_field_depth_zero schema resolvers variableValues
          parentType source responseName fieldName arguments directives
          selectionSet output hallowed]
        simp [visitSubfields, GraphQL.Execution.collectSelection,
          collectedExecutableFields, executableFieldSelections,
          executableFieldSelection, hallowed]
        simp [visitSelection_field_depth_zero schema resolvers variableValues
          parentType source responseName fieldName arguments [] selectionSet
          output (selectionDirectivesAllowBool_empty variableValues)]
    | succ depth =>
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          depth parentType source responseName fieldName arguments directives
          selectionSet output hallowed]
        simp [visitSubfields, visitSelection, executeField,
          GraphQL.Execution.collectSelection, collectedExecutableFields,
          executableFieldSelections, executableFieldSelection, executableField,
          selectionDirectivesAllowBool_empty, hallowed]
  · have hfalse :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases hmatch : selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    rw [visitSelection_field_directives_blocked schema resolvers variableValues
      depth parentType source responseName fieldName arguments directives
      selectionSet output hfalse]
    simp [visitSubfields, GraphQL.Execution.collectSelection,
      collectedExecutableFields, executableFieldSelections, hfalse]

theorem visitSelection_field_allowed_succ_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (fields : List (Name × ResponseValue))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : ResponseMergeReady (.object fields)
      -> ResponseMergeReady
          (resultValueOrNull
            (executeField schema resolvers variableValues depth source
              (responseObjectField? responseName (.object fields))
              (executableField parentType responseName fieldName arguments selectionSet)))
      -> ResponseMergeReady
          (visitSelection schema resolvers variableValues (depth + 1)
            parentType source
            (.field responseName fieldName arguments directives selectionSet)
            (.object fields)).fst := by
    intro hfieldsReady hfieldReady
    rw [visitSelection_field_allowed_succ schema resolvers variableValues depth
      parentType source responseName fieldName arguments directives selectionSet
      (.object fields) hallowed]
    simpa [mergeResponseFieldResult, mergeResponseFieldIntoObject] using
      mergeResponseField_object_ready_of_ready responseName
        (resultValueOrNull
          (executeField schema resolvers variableValues depth source
            (responseObjectField? responseName (.object fields))
            (executableField parentType responseName fieldName arguments
              selectionSet)))
        fields hfieldsReady hfieldReady

theorem visitSelection_field_allowed_succ_absorbs
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
      -> ResponseAbsorbs (.object fields)
          (visitSelection schema resolvers variableValues (depth + 1)
            parentType source
            (.field responseName fieldName arguments directives selectionSet)
            (.object fields)).fst := by
    intro hfieldsReady hcollisionAbsorbs
    rw [visitSelection_field_allowed_succ schema resolvers variableValues depth
      parentType source responseName fieldName arguments directives selectionSet
      (.object fields) hallowed]
    simpa [mergeResponseFieldResult, mergeResponseFieldIntoObject] using
      mergeResponseField_object_absorbs responseName
        (resultValueOrNull
          (executeField schema resolvers variableValues depth source
            (responseObjectField? responseName (.object fields))
            (executableField parentType responseName fieldName arguments
              selectionSet)))
        fields hfieldsReady hcollisionAbsorbs

theorem visitSelection_field_allowed_succ_absorbs_of_fresh
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
      -> ResponseAbsorbs (.object fields)
          (visitSelection schema resolvers variableValues (depth + 1)
            parentType source
            (.field responseName fieldName arguments directives selectionSet)
            (.object fields)).fst := by
  intro hfieldsReady
  apply visitSelection_field_allowed_succ_absorbs schema resolvers
    variableValues depth parentType source responseName fieldName arguments
    directives selectionSet fields hallowed hfieldsReady
  intro existing hmem
  exact False.elim (hfresh (by
    simpa [List.mem_map] using ⟨existing, hmem⟩))

theorem visitSubfields_single_field_allowed_succ_absorbs
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
      -> ResponseAbsorbs (.object fields)
          (visitSubfields schema resolvers variableValues (depth + 1)
            parentType source
            [.field responseName fieldName arguments directives selectionSet]
            (.object fields)).fst := by
  intro hfieldsReady hcollisionAbsorbs
  simpa [visitSubfields] using
    visitSelection_field_allowed_succ_absorbs schema resolvers variableValues
      depth parentType source responseName fieldName arguments directives
      selectionSet fields hallowed hfieldsReady hcollisionAbsorbs

theorem visitSubfields_single_field_allowed_succ_absorbs_of_fresh
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
      -> ResponseAbsorbs (.object fields)
          (visitSubfields schema resolvers variableValues (depth + 1)
            parentType source
            [.field responseName fieldName arguments directives selectionSet]
            (.object fields)).fst := by
  intro hfieldsReady
  simpa [visitSubfields] using
    visitSelection_field_allowed_succ_absorbs_of_fresh schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet fields hallowed hfresh hfieldsReady

theorem visitSelection_inline_none_directives_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : visitSelection schema resolvers variableValues depth parentType source
        (.inlineFragment none directives selectionSet) output
      = (output, visitOk) := by
  unfold visitSelection
  simp [hblocked]

theorem visitSelection_inline_some_directives_blocked
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : ResponseValue)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : visitSelection schema resolvers variableValues depth parentType source
        (.inlineFragment (some typeCondition) directives selectionSet) output
      = (output, visitOk) := by
  unfold visitSelection
  simp [hblocked]

theorem visitSelection_inline_some_type_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : ResponseValue)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply : doesFragmentTypeApplyBool schema parentType source typeCondition = false)
    : visitSelection schema resolvers variableValues depth parentType source
        (.inlineFragment (some typeCondition) directives selectionSet) output
      = (output, visitOk) := by
  unfold visitSelection
  simp [hallowed, hnotApply]

theorem
    visitSelection_inline_none_eq_visitSubfields_collectedExecutableFields_collectSelection
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : ResponseValue)
    (hbody
      : selectionDirectivesAllowBool variableValues directives = true
        -> visitSubfields schema resolvers variableValues depth parentType source
              selectionSet output
            = visitSubfields schema resolvers variableValues depth parentType source
                (executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues parentType
                      source selectionSet)))
                output)
    : visitSelection schema resolvers variableValues depth parentType source
        (.inlineFragment none directives selectionSet) output
      = visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues parentType
                source (.inlineFragment none directives selectionSet))))
          output := by
  by_cases hallowed :
      selectionDirectivesAllowBool variableValues directives = true
  · simp [visitSelection, GraphQL.Execution.collectSelection, hallowed]
    exact hbody hallowed
  · have hfalse :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases hmatch : selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    rw [visitSelection_inline_none_directives_blocked schema resolvers
      variableValues depth parentType source directives selectionSet output
      hfalse]
    simp [visitSubfields, GraphQL.Execution.collectSelection,
      collectedExecutableFields, executableFieldSelections, hfalse]

theorem
    visitSelection_inline_some_eq_visitSubfields_collectedExecutableFields_collectSelection
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (typeCondition : Name)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hbody
      : selectionDirectivesAllowBool variableValues directives = true
        -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
        -> visitSubfields schema resolvers variableValues depth parentType source
              selectionSet output
            = visitSubfields schema resolvers variableValues depth parentType source
                (executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues parentType
                      source selectionSet)))
                output)
    : visitSelection schema resolvers variableValues depth parentType source
        (.inlineFragment (some typeCondition) directives selectionSet) output
      = visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues parentType
                source
                (.inlineFragment (some typeCondition) directives selectionSet))))
          output := by
  by_cases hallowed :
      selectionDirectivesAllowBool variableValues directives = true
  · by_cases happly :
        doesFragmentTypeApplyBool schema parentType source typeCondition = true
    · simp [visitSelection, GraphQL.Execution.collectSelection, hallowed,
        happly]
      exact hbody hallowed happly
    · have hfalse :
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            false := by
        cases hmatch :
            doesFragmentTypeApplyBool schema parentType source typeCondition
        · rfl
        · contradiction
      rw [visitSelection_inline_some_type_not_apply schema resolvers
        variableValues depth parentType source typeCondition directives
        selectionSet output hallowed hfalse]
      simp [visitSubfields, GraphQL.Execution.collectSelection,
        collectedExecutableFields, executableFieldSelections, hallowed, hfalse]
  · have hfalse :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases hmatch : selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    rw [visitSelection_inline_some_directives_blocked schema resolvers
      variableValues depth parentType source typeCondition directives
      selectionSet output hfalse]
    simp [visitSubfields, GraphQL.Execution.collectSelection,
      collectedExecutableFields, executableFieldSelections, hfalse]

theorem visitSelection_eq_visitSubfields_collectedExecutableFields_collectSelection
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection) (output : ResponseValue)
    (hbody
      : match selection with
        | .field _responseName _fieldName _arguments _directives _selectionSet =>
            True
        | .inlineFragment none directives selectionSet =>
            selectionDirectivesAllowBool variableValues directives = true
            -> visitSubfields schema resolvers variableValues depth parentType
                  source selectionSet output
                = visitSubfields schema resolvers variableValues depth parentType
                    source
                    (executableFieldSelections
                      (collectedExecutableFields
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source selectionSet)))
                    output
        | .inlineFragment (some typeCondition) directives selectionSet =>
            selectionDirectivesAllowBool variableValues directives = true
            -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
            -> visitSubfields schema resolvers variableValues depth parentType
                  source selectionSet output
                = visitSubfields schema resolvers variableValues depth parentType
                    source
                    (executableFieldSelections
                      (collectedExecutableFields
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source selectionSet)))
                    output)
    : visitSelection schema resolvers variableValues depth parentType source
        selection output
      = visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues parentType
                source selection)))
          output := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      exact
        visitSelection_field_eq_visitSubfields_collectedExecutableFields_collectSelection
          schema resolvers variableValues depth parentType source responseName
          fieldName arguments directives selectionSet output
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          exact
            visitSelection_inline_none_eq_visitSubfields_collectedExecutableFields_collectSelection
              schema resolvers variableValues depth parentType source directives
              selectionSet output hbody
      | some typeCondition =>
          exact
            visitSelection_inline_some_eq_visitSubfields_collectedExecutableFields_collectSelection
              schema resolvers variableValues depth parentType source
              typeCondition directives selectionSet output hbody

theorem visitSubfields_single_eq_flattened_collectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection) (output : ResponseValue)
    (hbody
      : match selection with
        | .field _responseName _fieldName _arguments _directives _selectionSet =>
            True
        | .inlineFragment none directives selectionSet =>
            selectionDirectivesAllowBool variableValues directives = true
            -> visitSubfields schema resolvers variableValues depth parentType
                  source selectionSet output
                = visitSubfields schema resolvers variableValues depth parentType
                    source
                    (executableFieldSelections
                      (collectedExecutableFields
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source selectionSet)))
                    output
        | .inlineFragment (some typeCondition) directives selectionSet =>
            selectionDirectivesAllowBool variableValues directives = true
            -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
            -> visitSubfields schema resolvers variableValues depth parentType
                  source selectionSet output
                = visitSubfields schema resolvers variableValues depth parentType
                    source
                    (executableFieldSelections
                      (collectedExecutableFields
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source selectionSet)))
                    output)
    : visitSubfields schema resolvers variableValues depth parentType source
        [selection] output
      = visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source [selection])))
          output := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      by_cases hallowed :
          selectionDirectivesAllowBool variableValues directives = true
      · simp [visitSubfields, GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups, collectedExecutableFields, executableFieldSelections, executableFieldSelection, hallowed]
        cases depth <;>
          simp [visitSelection, executableField, hallowed,
            selectionDirectivesAllowBool_empty]
      · have hblocked :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h : selectionDirectivesAllowBool variableValues directives with
          | false => rfl
          | true => exact False.elim (hallowed h)
        simp only [visitSubfields]
        rw [visitSelection_field_directives_blocked schema resolvers
          variableValues depth parentType source responseName fieldName
          arguments directives selectionSet output hblocked]
        simp [visitSubfields, GraphQL.Execution.collectFields,
          GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
          collectedExecutableFields, executableFieldSelections, hblocked, visitOk,
          combineVisitStatus, GraphQL.Execution.Result.combine]
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          by_cases hallowed :
              selectionDirectivesAllowBool variableValues directives = true
          · simp [visitSubfields, visitSelection, GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups, executableFieldSelections, hallowed] at hbody ⊢
            exact hbody
          · have hblocked :
                selectionDirectivesAllowBool variableValues directives = false := by
              cases h :
                  selectionDirectivesAllowBool variableValues directives with
              | false => rfl
              | true => exact False.elim (hallowed h)
            simp [visitSubfields, visitSelection,
              GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
              GraphQL.Execution.mergeExecutableGroups, collectedExecutableFields,
              executableFieldSelections, hblocked, visitOk, combineVisitStatus,
              GraphQL.Execution.Result.combine]
      | some typeCondition =>
          by_cases hallowed :
              selectionDirectivesAllowBool variableValues directives = true
          · by_cases happly :
                doesFragmentTypeApplyBool schema parentType source typeCondition =
                  true
            · simp [visitSubfields, visitSelection, GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups, executableFieldSelections, hallowed, happly] at hbody ⊢
              exact hbody
            · have hnotApply :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition = false := by
                cases h :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition with
                | false => rfl
                | true => exact False.elim (happly h)
              simp [visitSubfields, visitSelection,
                GraphQL.Execution.collectFields,
                GraphQL.Execution.collectSelection,
                GraphQL.Execution.mergeExecutableGroups, collectedExecutableFields,
                executableFieldSelections, hallowed, hnotApply, visitOk,
                combineVisitStatus, Result.combine,
                GraphQL.Execution.Result.combine]
          · have hblocked :
                selectionDirectivesAllowBool variableValues directives = false := by
              cases h :
                  selectionDirectivesAllowBool variableValues directives with
              | false => rfl
              | true => exact False.elim (hallowed h)
            simp [visitSubfields, visitSelection,
              GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
              GraphQL.Execution.mergeExecutableGroups, collectedExecutableFields,
              executableFieldSelections, hblocked, visitOk, combineVisitStatus,
              GraphQL.Execution.Result.combine]

theorem visitSubfields_nil_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    (output : ResponseValue)
    : ResponseMergeReady output
      -> ResponseAbsorbs output
          (visitSubfields schema resolvers variableValues depth parentType source
            [] output).fst := by
  intro hready
  simpa [visitSubfields] using ResponseAbsorbs_refl_of_ready output hready

theorem visitSelection_field_blocked_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : ResponseMergeReady output
      -> ResponseAbsorbs output
          (visitSelection schema resolvers variableValues depth parentType source
            (.field responseName fieldName arguments directives selectionSet)
            output).fst := by
  intro hready
  rw [visitSelection_field_directives_blocked schema resolvers variableValues
    depth parentType source responseName fieldName arguments directives
    selectionSet output hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem visitSelection_field_depth_zero_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : ResponseMergeReady output
      -> ResponseAbsorbs output
          (visitSelection schema resolvers variableValues 0 parentType source
            (.field responseName fieldName arguments directives selectionSet)
            output).fst := by
  intro hready
  rw [visitSelection_field_depth_zero schema resolvers variableValues
    parentType source responseName fieldName arguments directives selectionSet
    output hallowed]
  cases output with
  | null =>
      simpa [responseObjectField?, mergeResponseFieldResult,
        mergeResponseFieldIntoObject, outOfFuel] using
        ResponseAbsorbs_refl_of_ready .null hready
  | scalar value =>
      simpa [responseObjectField?, mergeResponseFieldResult,
        mergeResponseFieldIntoObject, outOfFuel] using
        ResponseAbsorbs_refl_of_ready (.scalar value) hready
  | list values =>
      simpa [responseObjectField?, mergeResponseFieldResult,
        mergeResponseFieldIntoObject, outOfFuel] using
        ResponseAbsorbs_refl_of_ready (.list values) hready
  | object fields =>
      cases hprevious : responseObjectField? responseName (.object fields) with
      | none =>
          have hfield :
              ResponseAbsorbs (.object fields)
                (.object (mergeResponseField responseName .null fields)) := by
            apply mergeResponseField_object_absorbs responseName .null fields
            · exact hready
            · intro existing hmem
              have hkey : responseName ∈ fields.map Prod.fst := by
                exact List.mem_map.mpr ⟨(responseName, existing), hmem, rfl⟩
              have hlookupNone :
                  lookupResponseField? responseName fields = none := by
                simpa [responseObjectField?] using hprevious
              rcases lookupResponseField?_some_of_mem responseName fields hkey
                with ⟨found, hlookup⟩
              rw [hlookupNone] at hlookup
              contradiction
          simpa [hprevious, mergeResponseFieldResult, resultValueOrNull,
            mergeResponseFieldIntoObject, outOfFuel] using hfield
      | some previous =>
          have hpreviousMem :
              (responseName, previous) ∈ fields := by
            exact lookupResponseField?_some_mem responseName previous fields
              (by simpa [responseObjectField?] using hprevious)
          have hpreviousReady :
              ResponseMergeReady previous :=
            ResponseMergeReady_object_field fields responseName previous
              hready hpreviousMem
          have hfield :
              ResponseAbsorbs (.object fields)
                (.object (mergeResponseField responseName previous fields)) := by
            exact mergeResponseField_object_absorbs responseName previous fields
              hready (by
                intro existing hmem
                exact ResponseAbsorbs_merge_of_ready existing previous
                  (ResponseMergeReady_object_field fields responseName existing
                    hready hmem)
                  hpreviousReady)
          simpa [hprevious, mergeResponseFieldResult, resultValueOrNull,
            mergeResponseFieldIntoObject, outOfFuel] using hfield

theorem visitSelection_inline_none_blocked_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (output : ResponseValue)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : ResponseMergeReady output
      -> ResponseAbsorbs output
          (visitSelection schema resolvers variableValues depth parentType source
            (.inlineFragment none directives selectionSet) output).fst := by
  intro hready
  rw [visitSelection_inline_none_directives_blocked schema resolvers
    variableValues depth parentType source directives selectionSet output
    hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem visitSelection_inline_some_blocked_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : ResponseValue)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : ResponseMergeReady output
      -> ResponseAbsorbs output
          (visitSelection schema resolvers variableValues depth parentType source
            (.inlineFragment (some typeCondition) directives selectionSet)
            output).fst := by
  intro hready
  rw [visitSelection_inline_some_directives_blocked schema resolvers
    variableValues depth parentType source typeCondition directives
    selectionSet output hblocked]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem visitSelection_inline_some_not_apply_absorbs_of_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (output : ResponseValue)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply : doesFragmentTypeApplyBool schema parentType source typeCondition = false)
    : ResponseMergeReady output
      -> ResponseAbsorbs output
          (visitSelection schema resolvers variableValues depth parentType source
            (.inlineFragment (some typeCondition) directives selectionSet)
            output).fst := by
  intro hready
  rw [visitSelection_inline_some_type_not_apply schema resolvers variableValues
    depth parentType source typeCondition directives selectionSet output
    hallowed hnotApply]
  exact ResponseAbsorbs_refl_of_ready output hready

theorem visitSubfields_append_equivalence
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ (left right : List Selection) (output : ResponseValue),
        visitSubfields schema resolvers variableValues depth parentType source
          (left ++ right) output
        = let leftResult :=
            visitSubfields schema resolvers variableValues depth parentType source
              left output
          let rightResult :=
            visitSubfields schema resolvers variableValues depth parentType source
              right leftResult.fst
          (rightResult.fst, combineVisitStatus leftResult.snd rightResult.snd)
  | [], _right, _output => by
      simp [visitSubfields]
  | _selection :: rest, right, output => by
      simp [visitSubfields,
        visitSubfields_append_equivalence schema resolvers variableValues depth
          parentType source rest right, combineVisitStatus_assoc]

def VisitSubfieldsFlatCollects
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (output : ResponseValue)
    : Prop :=
  visitSubfields schema resolvers variableValues depth parentType source
    selectionSet output
  = visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet)))
      output

def VisitSubfieldsFlatCollectsAllOutputs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : Prop :=
  ∀ output,
    VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
      source selectionSet output

def VisitSubfieldsRawFlatCollects
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (output : ResponseValue)
    : Prop :=
  visitSubfields schema resolvers variableValues depth parentType source
    selectionSet output
  = visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet)))
      output

def VisitSubfieldsRawFlatCollectsAllOutputs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : Prop :=
  ∀ output,
    VisitSubfieldsRawFlatCollects schema resolvers variableValues depth
      parentType source selectionSet output

theorem VisitSubfieldsFlatCollects.of_raw
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (output : ResponseValue)
    (hraw
      : VisitSubfieldsRawFlatCollects schema resolvers variableValues depth
          parentType source selectionSet output)
    : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source selectionSet output := by
  unfold VisitSubfieldsRawFlatCollects at hraw
  unfold VisitSubfieldsFlatCollects
  rw [hraw]

theorem VisitSubfieldsFlatCollectsAllOutputs.of_raw
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hraw
      : VisitSubfieldsRawFlatCollectsAllOutputs schema resolvers variableValues
          depth parentType source selectionSet)
    : VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
        parentType source selectionSet := by
  intro output
  exact VisitSubfieldsFlatCollects.of_raw schema resolvers variableValues depth
    parentType source selectionSet output (hraw output)

theorem VisitSubfieldsRawFlatCollects_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (output : ResponseValue)
    : VisitSubfieldsRawFlatCollects schema resolvers variableValues depth
        parentType source [] output := by
  simp [VisitSubfieldsRawFlatCollects, GraphQL.Execution.collectFields,
    collectedExecutableFields, executableFieldSelections]

theorem VisitSubfieldsRawFlatCollectsAllOutputs_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : VisitSubfieldsRawFlatCollectsAllOutputs schema resolvers variableValues
        depth parentType source [] := by
  intro output
  exact VisitSubfieldsRawFlatCollects_nil schema resolvers variableValues depth
    parentType source output

theorem VisitSubfieldsRawFlatCollects_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left right : List Selection) (output : ResponseValue)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source right))
    (hrightNodup
      : GraphQL.NormalForm.executableGroupNamesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType source right))
    (hleft
      : VisitSubfieldsRawFlatCollects schema resolvers variableValues depth
          parentType source left output)
    (hright
      : VisitSubfieldsRawFlatCollects schema resolvers variableValues depth
          parentType source right
          (visitSubfields schema resolvers variableValues depth parentType source
            (executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source left)))
            output).fst)
    : VisitSubfieldsRawFlatCollects schema resolvers variableValues depth
        parentType source (left ++ right) output := by
  unfold VisitSubfieldsRawFlatCollects at hleft hright ⊢
  have hflatAppend :
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (left ++ right))) =
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source left)) ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source right)) := by
    rw [GraphQL.NormalForm.collectFields_append]
    rw [collectedExecutableFields_mergeExecutableGroups_eq_append_of_namesDisjoint
      (GraphQL.Execution.collectFields schema variableValues parentType source
        left)
      (GraphQL.Execution.collectFields schema variableValues parentType source
        right)
      hdisjoint hrightNodup]
    simp [executableFieldSelections, List.map_append]
  rw [visitSubfields_append_equivalence]
  rw [hflatAppend]
  rw [visitSubfields_append_equivalence]
  rw [hleft]
  let flatLeftResult :=
    visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source left)))
      output
  have hright' :
      visitSubfields schema resolvers variableValues depth parentType source
        right flatLeftResult.fst =
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source right)))
        flatLeftResult.fst := by
    simpa [flatLeftResult] using hright
  cases flatLeftResult with
  | mk flatLeftOutput flatLeftStatus =>
      simp [flatLeftResult] at hright' ⊢
      rw [hright']
      constructor <;> rfl

theorem VisitSubfieldsRawFlatCollectsAllOutputs_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left right : List Selection)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source right))
    (hrightNodup
      : GraphQL.NormalForm.executableGroupNamesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType source right))
    (hleft
      : VisitSubfieldsRawFlatCollectsAllOutputs schema resolvers variableValues
          depth parentType source left)
    (hright
      : VisitSubfieldsRawFlatCollectsAllOutputs schema resolvers variableValues
          depth parentType source right)
    : VisitSubfieldsRawFlatCollectsAllOutputs schema resolvers variableValues
        depth parentType source (left ++ right) := by
  intro output
  apply VisitSubfieldsRawFlatCollects_append_of_namesDisjoint schema resolvers
    variableValues depth parentType source left right output hdisjoint
    hrightNodup
  · exact hleft output
  · exact hright
      (visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source left)))
        output).fst

theorem VisitSubfieldsFlatCollects_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity) (output : ResponseValue)
    : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source [] output := by
  simp [VisitSubfieldsFlatCollects, GraphQL.Execution.collectFields,
    collectedExecutableFields, executableFieldSelections]

theorem VisitSubfieldsFlatCollectsAllOutputs_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
        parentType source [] := by
  intro output
  exact VisitSubfieldsFlatCollects_nil schema resolvers variableValues depth
    parentType source output

theorem VisitSubfieldsFlatCollects_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection) (output : ResponseValue)
    (hbody
      : match selection with
        | .field _responseName _fieldName _arguments _directives _selectionSet =>
            True
        | .inlineFragment none directives selectionSet =>
            selectionDirectivesAllowBool variableValues directives = true
            -> VisitSubfieldsFlatCollects schema resolvers variableValues depth
                parentType source selectionSet output
        | .inlineFragment (some typeCondition) directives selectionSet =>
            selectionDirectivesAllowBool variableValues directives = true
            -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
            -> VisitSubfieldsFlatCollects schema resolvers variableValues depth
                parentType source selectionSet output)
    : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source [selection] output := by
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  exact visitSubfields_single_eq_flattened_collectFields schema resolvers
    variableValues depth parentType source selection output hbody

theorem VisitSubfieldsFlatCollectsAllOutputs_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection)
    (hbody
      : match selection with
        | .field _responseName _fieldName _arguments _directives _selectionSet =>
            True
        | .inlineFragment none directives selectionSet =>
            selectionDirectivesAllowBool variableValues directives = true
            -> VisitSubfieldsFlatCollectsAllOutputs schema resolvers
                variableValues depth parentType source selectionSet
        | .inlineFragment (some typeCondition) directives selectionSet =>
            selectionDirectivesAllowBool variableValues directives = true
            -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
            -> VisitSubfieldsFlatCollectsAllOutputs schema resolvers
                variableValues depth parentType source selectionSet)
    : VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
        parentType source [selection] := by
  intro output
  apply VisitSubfieldsFlatCollects_single schema resolvers variableValues depth
    parentType source selection output
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      exact trivial
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          intro hallowed
          exact hbody hallowed output
      | some typeCondition =>
          intro hallowed happly
          exact hbody hallowed happly output

theorem VisitSubfieldsFlatCollects_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left right : List Selection) (output : ResponseValue)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source right))
    (hrightNodup
      : GraphQL.NormalForm.executableGroupNamesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType source right))
    (hleft
      : VisitSubfieldsRawFlatCollects schema resolvers variableValues depth
          parentType source left output)
    (hright
      : VisitSubfieldsRawFlatCollects schema resolvers variableValues depth
          parentType source right
          (visitSubfields schema resolvers variableValues depth parentType source
            (executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source left)))
            output).fst)
    : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source (left ++ right) output := by
  exact
    VisitSubfieldsFlatCollects.of_raw schema resolvers variableValues depth
      parentType source (left ++ right) output
      (VisitSubfieldsRawFlatCollects_append_of_namesDisjoint schema resolvers
        variableValues depth parentType source left right output hdisjoint
        hrightNodup hleft hright)

theorem VisitSubfieldsFlatCollectsAllOutputs_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left right : List Selection)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source right))
    (hrightNodup
      : GraphQL.NormalForm.executableGroupNamesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType source right))
    (hleft
      : VisitSubfieldsRawFlatCollectsAllOutputs schema resolvers variableValues
          depth parentType source left)
    (hright
      : VisitSubfieldsRawFlatCollectsAllOutputs schema resolvers variableValues
          depth parentType source right)
    : VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
        parentType source (left ++ right) := by
  intro output
  apply VisitSubfieldsFlatCollects_append_of_namesDisjoint schema resolvers
    variableValues depth parentType source left right output hdisjoint
    hrightNodup
  · exact hleft output
  · exact hright
      (visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source left)))
        output).fst

theorem VisitSubfieldsFlatCollects_executableFieldSelections_same_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (fields : List ExecutableField)
    (output : ResponseValue)
    (hresponse : ∀ field, field ∈ fields -> field.responseName = responseName)
    (hparent : ∀ field, field ∈ fields -> field.parentType = parentType)
    : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source (executableFieldSelections fields) output := by
  unfold VisitSubfieldsFlatCollects
  rw [collectFields_executableFieldSelections_same_group schema variableValues
    parentType source responseName fields hresponse hparent]
  cases fields <;> simp [collectedExecutableFields]

theorem VisitSubfieldsFlatCollects_executableFieldSelections_collectedExecutableFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (output : ResponseValue)
    (hnodup : PairKeysNodup groups)
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponse : CollectedGroupsResponseName groups)
    (hparent : CollectedGroupsParent parentType groups)
    : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source (executableFieldSelections (collectedExecutableFields groups))
        output := by
  unfold VisitSubfieldsFlatCollects
  rw [collectFields_executableFieldSelections_collectedExecutableFields schema
    variableValues parentType source groups hnodup hnonempty hresponse hparent]

theorem VisitSubfieldsFlatCollects_executableFieldSelections_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (output : ResponseValue)
    : VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)))
        output := by
  unfold VisitSubfieldsFlatCollects
  rw [collectFields_executableFieldSelections_collectedExecutableFields_collectFields]

mutual
  theorem visitSelection_responseObjectField?_of_not_mem_collectSelection
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (responseName : Name)
      : ∀ (selection : Selection) (output : ResponseValue),
          responseName
            ∉ (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection).map
                Prod.fst
          -> responseObjectField? responseName
                (visitSelection schema resolvers variableValues depth parentType
                  source selection output).fst
              = responseObjectField? responseName output := by
    intro selection output hnot
    cases selection with
    | field fieldResponseName fieldName arguments directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · have hne : responseName ≠ fieldResponseName := by
            intro heq
            apply hnot
            simp [GraphQL.Execution.collectSelection, hallowed, heq]
          cases depth with
          | zero =>
              cases output with
              | null =>
                  simp [visitSelection, hallowed, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, responseObjectField?]
              | scalar value =>
                  simp [visitSelection, hallowed, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, responseObjectField?]
              | list values =>
                  simp [visitSelection, hallowed, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, responseObjectField?]
              | object fields =>
                  cases hprevious :
                      lookupResponseField? fieldResponseName fields with
                  | none =>
                      simpa [visitSelection, hallowed, mergeResponseFieldResult,
                        resultValueOrNull, outOfFuel,
                        mergeResponseFieldIntoObject, responseObjectField?,
                        hprevious] using
                        responseObjectField?_mergeResponseFieldIntoObject_other
                          responseName fieldResponseName .null fields hne
                  | some previous =>
                      simpa [visitSelection, hallowed, mergeResponseFieldResult,
                        resultValueOrNull,
                        mergeResponseFieldIntoObject, responseObjectField?,
                        hprevious] using
                        responseObjectField?_mergeResponseFieldIntoObject_other
                          responseName fieldResponseName previous fields hne
          | succ depth' =>
              cases output with
              | null =>
                  simp [visitSelection, hallowed, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, responseObjectField?]
              | scalar value =>
                  simp [visitSelection, hallowed, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, responseObjectField?]
              | list values =>
                  simp [visitSelection, hallowed, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, responseObjectField?]
              | object fields =>
                  cases hprevious :
                      lookupResponseField? fieldResponseName fields with
                  | none =>
                      simp [visitSelection, hallowed, mergeResponseFieldResult,
                        mergeResponseFieldIntoObject, responseObjectField?,
                        hprevious]
                      simpa [hprevious] using
                        lookupResponseField?_mergeResponseField_other
                          responseName fieldResponseName
                          (resultValueOrNull
                            (executeField schema resolvers variableValues depth'
                              source
                              (lookupResponseField? fieldResponseName fields)
                              (executableField parentType fieldResponseName
                                fieldName arguments selectionSet)))
                          fields hne
                  | some previous =>
                      cases previous with
                      | null =>
                          simp [visitSelection, hallowed,
                            mergeResponseFieldResult,
                            mergeResponseFieldIntoObject,
                            responseObjectField?, hprevious]
                          simpa [hprevious] using
                            lookupResponseField?_mergeResponseField_other
                              responseName fieldResponseName
                              (resultValueOrNull
                                (executeField schema resolvers variableValues
                                  depth' source
                                  (lookupResponseField? fieldResponseName
                                    fields)
                                  (executableField parentType fieldResponseName
                                    fieldName arguments selectionSet)))
                              fields hne
                      | scalar value =>
                          simp [visitSelection, hallowed,
                            mergeResponseFieldResult,
                            mergeResponseFieldIntoObject,
                            responseObjectField?, hprevious]
                          simpa [hprevious] using
                            lookupResponseField?_mergeResponseField_other
                              responseName fieldResponseName
                              (resultValueOrNull
                                (executeField schema resolvers variableValues
                                  depth' source
                                  (lookupResponseField? fieldResponseName
                                    fields)
                                  (executableField parentType fieldResponseName
                                    fieldName arguments selectionSet)))
                              fields hne
                      | object objectFields =>
                          simp [visitSelection, hallowed,
                            mergeResponseFieldResult,
                            mergeResponseFieldIntoObject,
                            responseObjectField?, hprevious]
                          simpa [hprevious] using
                            lookupResponseField?_mergeResponseField_other
                              responseName fieldResponseName
                              (resultValueOrNull
                                (executeField schema resolvers variableValues
                                  depth' source
                                  (lookupResponseField? fieldResponseName
                                    fields)
                                  (executableField parentType fieldResponseName
                                    fieldName arguments selectionSet)))
                              fields hne
                      | list values =>
                          simp [visitSelection, hallowed,
                            mergeResponseFieldResult,
                            mergeResponseFieldIntoObject,
                            responseObjectField?, hprevious]
                          simpa [hprevious] using
                            lookupResponseField?_mergeResponseField_other
                              responseName fieldResponseName
                              (resultValueOrNull
                                (executeField schema resolvers variableValues
                                  depth' source
                                  (lookupResponseField? fieldResponseName
                                    fields)
                                  (executableField parentType fieldResponseName
                                    fieldName arguments selectionSet)))
                              fields hne
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false :=
            by
              cases h :
                  selectionDirectivesAllowBool variableValues directives with
              | false => rfl
              | true => exact False.elim (hallowed h)
          unfold visitSelection
          simp [hblocked]
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases typeCondition with
          | none =>
              have hbody :
                  responseName ∉
                      (GraphQL.Execution.collectFields schema
                        variableValues parentType source selectionSet).map
                        Prod.fst := by
                simpa [GraphQL.Execution.collectSelection, hallowed]
                  using hnot
              simpa [visitSelection, hallowed] using
                visitSubfields_responseObjectField?_of_not_mem_collectFields
                  schema resolvers variableValues depth parentType source
                  responseName selectionSet output hbody
          | some typeCondition =>
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · have hbody :
                  responseName ∉
                      (GraphQL.Execution.collectFields schema
                        variableValues parentType source selectionSet).map
                        Prod.fst := by
                    simpa [GraphQL.Execution.collectSelection, hallowed,
                      happly] using hnot
                simpa [visitSelection, hallowed, happly] using
                  visitSubfields_responseObjectField?_of_not_mem_collectFields
                    schema resolvers variableValues depth parentType source
                    responseName selectionSet output hbody
              · simp [visitSelection, hallowed, happly]
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false :=
            by
              cases h :
                  selectionDirectivesAllowBool variableValues directives with
              | false => rfl
              | true => exact False.elim (hallowed h)
          cases typeCondition <;>
            (unfold visitSelection; simp [hblocked])

  theorem visitSubfields_responseObjectField?_of_not_mem_collectFields
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (responseName : Name)
      : ∀ (selectionSet : List Selection) (output : ResponseValue),
          responseName
            ∉ (GraphQL.Execution.collectFields schema variableValues parentType
                source selectionSet).map
                Prod.fst
          -> responseObjectField? responseName
                (visitSubfields schema resolvers variableValues depth parentType
                  source selectionSet output).fst
              = responseObjectField? responseName output := by
    intro selectionSet output hnot
    cases selectionSet with
    | nil =>
        simp [visitSubfields]
    | cons selection rest =>
        have hnotHead :
            responseName ∉
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection).map Prod.fst := by
          intro hmem
          apply hnot
          simp [GraphQL.Execution.collectFields,
            mergeExecutableGroups_key_mem, hmem]
        have hnotRest :
            responseName ∉
              (GraphQL.Execution.collectFields schema variableValues
                parentType source rest).map Prod.fst := by
          intro hmem
          apply hnot
          simp [GraphQL.Execution.collectFields,
            mergeExecutableGroups_key_mem, hmem]
        simp [visitSubfields]
        rw [
          visitSubfields_responseObjectField?_of_not_mem_collectFields
            schema resolvers variableValues depth parentType source
            responseName rest
            (visitSelection schema resolvers variableValues depth
              parentType source selection output).fst hnotRest
        ]
        exact
          visitSelection_responseObjectField?_of_not_mem_collectSelection
            schema resolvers variableValues depth parentType source
            responseName selection output hnotHead
end

theorem mergeResponseFieldIntoObject_commutes_with_appended_visitSubfields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (incoming : ResponseValue)
    (fields suffix : List (Name × ResponseValue))
    (hpresent : responseName ∈ fields.map Prod.fst)
    (hbase
      : (visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (.object fields)).fst
        = .object (fields ++ suffix))
    (hmerged
      : (visitSubfields schema resolvers variableValues depth parentType source
          selectionSet
          (mergeResponseFieldIntoObject responseName incoming (.object fields))).fst
        = .object (mergeResponseField responseName incoming fields ++ suffix))
    : mergeResponseFieldIntoObject responseName incoming
        (visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (.object fields)).fst
      = (visitSubfields schema resolvers variableValues depth parentType source
          selectionSet
          (mergeResponseFieldIntoObject responseName incoming (.object fields))).fst := by
  rw [hbase, hmerged]
  simp [mergeResponseFieldIntoObject,
    mergeResponseField_append_of_mem_left responseName incoming fields suffix
      hpresent]

mutual
  theorem visitSelection_preserves_object_core
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selection : Selection) (fields : List (Name × ResponseValue)),
          ∃ outputFields,
            (visitSelection schema resolvers variableValues depth parentType source
              selection (.object fields)).fst
            = .object outputFields := by
    intro selection fields
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases depth with
          | zero =>
              cases hprevious :
                  responseObjectField? responseName (.object fields) with
              | none =>
                  refine ⟨mergeResponseField responseName .null fields, ?_⟩
                  simp [visitSelection, hallowed, hprevious,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    resultValueOrNull, outOfFuel]
              | some previous =>
                  refine ⟨mergeResponseField responseName previous fields, ?_⟩
                  simp [visitSelection, hallowed, hprevious,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    resultValueOrNull]
          | succ depth' =>
              cases hprevious :
                  responseObjectField? responseName (.object fields) with
              | none =>
                  refine
                    ⟨mergeResponseField responseName
                      (resultValueOrNull
                        (executeField schema resolvers variableValues depth'
                          source
                          (responseObjectField? responseName (.object fields))
                          (executableField parentType responseName fieldName
                            arguments selectionSet)))
                        fields, ?_⟩
                  simp [visitSelection, hallowed, hprevious,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject]
              | some previous =>
                  cases previous with
                  | null =>
                      refine
                        ⟨mergeResponseField responseName
                          (resultValueOrNull
                            (executeField schema resolvers variableValues depth'
                              source
                              (responseObjectField? responseName (.object fields))
                              (executableField parentType responseName fieldName
                                arguments selectionSet)))
                            fields, ?_⟩
                      simp [visitSelection, hallowed, hprevious,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject]
                  | scalar value =>
                      refine
                        ⟨mergeResponseField responseName
                          (resultValueOrNull
                            (executeField schema resolvers variableValues depth'
                              source
                              (responseObjectField? responseName (.object fields))
                              (executableField parentType responseName fieldName
                                arguments selectionSet)))
                            fields, ?_⟩
                      simp [visitSelection, hallowed, hprevious,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject]
                  | object objectFields =>
                      refine
                        ⟨mergeResponseField responseName
                          (resultValueOrNull
                            (executeField schema resolvers variableValues depth'
                              source
                              (responseObjectField? responseName (.object fields))
                              (executableField parentType responseName fieldName
                                arguments selectionSet)))
                            fields, ?_⟩
                      simp [visitSelection, hallowed, hprevious,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject]
                  | list values =>
                      refine
                        ⟨mergeResponseField responseName
                          (resultValueOrNull
                            (executeField schema resolvers variableValues depth'
                              source
                              (responseObjectField? responseName (.object fields))
                              (executableField parentType responseName fieldName
                                arguments selectionSet)))
                            fields, ?_⟩
                      simp [visitSelection, hallowed, hprevious,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject]
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false :=
            by
              cases h :
                  selectionDirectivesAllowBool variableValues directives with
              | false => rfl
              | true => exact False.elim (hallowed h)
          exact
            ⟨fields, by
              unfold visitSelection
              simp [hblocked]⟩
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases typeCondition with
          | none =>
              rcases
                visitSubfields_preserves_object_core schema resolvers
                  variableValues depth parentType source selectionSet fields
              with ⟨outputFields, hvisit⟩
              exact ⟨outputFields, by simp [visitSelection, hallowed, hvisit]⟩
          | some typeCondition =>
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · rcases
                  visitSubfields_preserves_object_core schema resolvers
                    variableValues depth parentType source selectionSet fields
                with ⟨outputFields, hvisit⟩
                exact
                  ⟨outputFields, by
                    simp [visitSelection, hallowed, happly, hvisit]⟩
              · exact ⟨fields, by simp [visitSelection, hallowed, happly]⟩
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false :=
            by
              cases h :
                  selectionDirectivesAllowBool variableValues directives with
              | false => rfl
              | true => exact False.elim (hallowed h)
          cases typeCondition with
          | none =>
              exact ⟨fields, by unfold visitSelection; simp [hblocked]⟩
          | some _typeCondition =>
              exact ⟨fields, by unfold visitSelection; simp [hblocked]⟩

  theorem visitSubfields_preserves_object_core
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (depth : Nat) (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selectionSet : List Selection) (fields : List (Name × ResponseValue)),
          ∃ outputFields,
            (visitSubfields schema resolvers variableValues depth parentType source
              selectionSet (.object fields)).fst
            = .object outputFields := by
    intro selectionSet fields
    cases selectionSet with
    | nil =>
        exact ⟨fields, by simp [visitSubfields]⟩
    | cons selection rest =>
        rcases
          visitSelection_preserves_object_core schema resolvers variableValues
            depth parentType source selection fields
        with ⟨headFields, hhead⟩
        rcases
          visitSubfields_preserves_object_core schema resolvers variableValues
            depth parentType source rest headFields
        with ⟨tailFields, htail⟩
        exact
          ⟨tailFields, by
            simp [visitSubfields]
            rw [hhead]
            simpa using htail⟩
end

theorem executeRootSelectionSet_eq_spec_of_flatCollects_and_flattened_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues depth
          parentType source selectionSet (.object []))
    (hflatSpec
      : executeRootSelectionSet schema resolvers variableValues depth parentType
          source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source selectionSet)))
        = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
            depth parentType source
            (executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source selectionSet))))
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet := by
  let flatSelectionSet :=
    executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType
          source selectionSet))
  have hdirectRoot :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source flatSelectionSet := by
    unfold VisitSubfieldsFlatCollects at hdirect
    unfold executeRootSelectionSet
    rw [hdirect]
  have hflatSpec' :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source flatSelectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source flatSelectionSet := by
    simpa [flatSelectionSet] using hflatSpec
  have hspecFlat :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source flatSelectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source selectionSet := by
    simpa [flatSelectionSet] using
      specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields_collectFields
        schema resolvers variableValues depth parentType source selectionSet
  exact hdirectRoot.trans (hflatSpec'.trans hspecFlat)

def ExecutableFieldsFlatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    : Prop :=
  executeRootSelectionSet schema resolvers variableValues depth parentType source
    (executableFieldSelections fields)
  = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (executableFieldSelections fields)

def ExecutableGroupsFlatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues depth
    parentType source (collectedExecutableFields groups)

def ExecutableFieldsFlatSpecAlignedEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    : Prop :=
  RootSelectionResultAlignedEquivalent
    (executeRootSelectionSet schema resolvers variableValues depth parentType
      source (executableFieldSelections fields))
    (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
      depth parentType source (executableFieldSelections fields))

def ExecutableGroupsFlatSpecAlignedEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ExecutableFieldsFlatSpecAlignedEquivalent schema resolvers variableValues depth
    parentType source (collectedExecutableFields groups)

theorem ExecutableFieldsFlatSpecAlignedEquivalent.of_exact
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {fields : List ExecutableField}
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues depth
        parentType source fields
      -> ExecutableFieldsFlatSpecAlignedEquivalent schema resolvers variableValues
          depth parentType source fields := by
  intro hexact
  exact RootSelectionResultAlignedEquivalent.of_eq hexact

theorem ExecutableGroupsFlatSpecAlignedEquivalent.of_exact
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
        parentType source groups
      -> ExecutableGroupsFlatSpecAlignedEquivalent schema resolvers variableValues
          depth parentType source groups := by
  intro hexact
  exact ExecutableFieldsFlatSpecAlignedEquivalent.of_exact hexact

def ExecutableFieldsMergedComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (_resolved : Option (ResolverValue ObjectIdentity))
    : Prop :=
  executeRootSelectionSet schema resolvers variableValues (depth + 1)
    parentType source (executableFieldSelections (field :: fields))
  = GraphQL.Execution.executeField schema resolvers variableValues (depth + 1)
      source responseName (field :: fields)

def ExecutableFieldsMergedResponse
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (_resolved : Option (ResolverValue ObjectIdentity))
    : Prop :=
  executeRootSelectionSet schema resolvers variableValues (depth + 1)
    parentType source (executableFieldSelections (field :: fields))
  = GraphQL.Execution.executeField schema resolvers variableValues (depth + 1)
      source responseName (field :: fields)

theorem visitSubfields_eq_object_singleton_of_executeRootSelectionSet_eq_singleton
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (responseName : Name)
    (response : ResponseValue) (errors : Nat)
    (hroot
      : executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet
        = .ok ([(responseName, response)], errors))
    : (visitSubfields schema resolvers variableValues depth parentType source
        selectionSet (.object [])).fst
      = .object [(responseName, response)] := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object_core schema resolvers variableValues depth
      parentType source selectionSet []
  unfold executeRootSelectionSet at hroot
  cases hvisit
        : visitSubfields schema resolvers variableValues depth parentType source
            selectionSet (.object []) with
  | mk output status =>
      rw [hvisit] at hfields hroot
      simp at hfields
      cases hfields
      cases status with
      | error rootErrors =>
          simp at hroot
      | ok status =>
          rcases status with ⟨unitValue, rootErrors⟩
          simp at hroot
          simpa using hroot.1

theorem ExecutableFieldsMergedComplete_of_MergedResponse
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    : ExecutableFieldsMergedResponse schema resolvers variableValues depth
        parentType source responseName field fields resolved
      -> ExecutableFieldsMergedComplete schema resolvers variableValues depth
          parentType source responseName field fields resolved := by
  intro hresponse
  exact hresponse

theorem ExecutableFieldsMergedResponse_of_MergedComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved
      -> ExecutableFieldsMergedResponse schema resolvers variableValues depth
          parentType source responseName field fields resolved := by
  intro hmerged
  exact hmerged

theorem executeRootSelectionSet_eq_spec_of_flatCollects_and_flatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues depth
          parentType source selectionSet (.object []))
    (hflatSpec
      : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues depth
          parentType source
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)))
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet := by
  unfold ExecutableFieldsFlatSpecEquivalent at hflatSpec
  exact executeRootSelectionSet_eq_spec_of_flatCollects_and_flattened_spec
    schema resolvers variableValues depth parentType source selectionSet
    hdirect hflatSpec

theorem executeRootSelectionSet_aligned_of_flatCollects_and_flatSpecAligned
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues depth
          parentType source selectionSet (.object []))
    (hflatSpec
      : ExecutableFieldsFlatSpecAlignedEquivalent schema resolvers variableValues
          depth parentType source
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)))
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet) := by
  let flatSelectionSet :=
    executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType
          source selectionSet))
  have hdirectRoot :
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet =
      executeRootSelectionSet schema resolvers variableValues depth parentType
        source flatSelectionSet := by
    unfold VisitSubfieldsFlatCollects at hdirect
    unfold executeRootSelectionSet
    rw [hdirect]
  have hflatSpec' :
      RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues depth
          parentType source flatSelectionSet)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues depth parentType source flatSelectionSet) := by
    simpa [ExecutableFieldsFlatSpecAlignedEquivalent, flatSelectionSet] using
      hflatSpec
  have hspecFlat :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source flatSelectionSet =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source selectionSet := by
    simpa [flatSelectionSet] using
      specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields_collectFields
        schema resolvers variableValues depth parentType source selectionSet
  exact
    RootSelectionResultAlignedEquivalent.trans
      (RootSelectionResultAlignedEquivalent.of_eq hdirectRoot)
      (RootSelectionResultAlignedEquivalent.trans hflatSpec'
        (RootSelectionResultAlignedEquivalent.of_eq hspecFlat))

theorem executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues depth
          parentType source selectionSet (.object []))
    (hgroups
      : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
          parentType source
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet))
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet := by
  unfold ExecutableGroupsFlatSpecEquivalent at hgroups
  exact executeRootSelectionSet_eq_spec_of_flatCollects_and_flatSpecEquivalent
    schema resolvers variableValues depth parentType source selectionSet
    hdirect hgroups

theorem executeRootSelectionSet_aligned_of_flatCollects_and_groupFlatSpecAligned
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues depth
          parentType source selectionSet (.object []))
    (hgroups
      : ExecutableGroupsFlatSpecAlignedEquivalent schema resolvers variableValues
          depth parentType source
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet))
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet) := by
  unfold ExecutableGroupsFlatSpecAlignedEquivalent at hgroups
  exact
    executeRootSelectionSet_aligned_of_flatCollects_and_flatSpecAligned
      schema resolvers variableValues depth parentType source selectionSet
      hdirect hgroups

theorem ExecutableFieldsFlatSpecEquivalent_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues depth
        parentType source [] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  simp [executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
    executableFieldSelections, GraphQL.Execution.collectFields,
    GraphQL.Execution.executeCollectedFields, visitSubfields, visitOk]

theorem ExecutableGroupsFlatSpecEquivalent_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
        parentType source [] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simpa [collectedExecutableFields] using
    ExecutableFieldsFlatSpecEquivalent_nil schema resolvers variableValues depth
      parentType source

theorem executeRootSelectionSet_eq_spec_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = [])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues depth
          parentType source selectionSet (.object []))
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet := by
  have hgroups :
      ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues depth
        parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) := by
    rw [hcollect]
    exact ExecutableGroupsFlatSpecEquivalent_nil schema resolvers variableValues
      depth parentType source
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues depth parentType source selectionSet
      hdirect hgroups

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
