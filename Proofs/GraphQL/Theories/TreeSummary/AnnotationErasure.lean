import Proofs.GraphQL.Theories.TreeSummary.ExactCases.Soundness
import Proofs.GraphQL.Theories.TreeSummary.Syntactic.Soundness

/-! Erasing resolver-call annotations preserves ordinary GraphQL execution. -/

namespace GraphQL
namespace TreeSummary

open GraphQL.Execution
open GraphQL.AnnotatedExecution

private def annotatedResponseFieldsResultToResponse
    : Result (List AnnotatedResponseField) -> Result (List (Name × ResponseValue))
  | .error errors => .error errors
  | .ok (fields, errors) =>
      .ok (annotatedResponseFieldsToResponseFields fields, errors)

private def annotatedResponseValueResultToResponse
    : Result AnnotatedResponseValue -> Result ResponseValue
  | .error errors => .error errors
  | .ok (value, errors) => .ok (value.toResponseValue, errors)

private def annotatedResponseValuesResultToResponse
    : Result (List AnnotatedResponseValue) -> Result (List ResponseValue)
  | .error errors => .error errors
  | .ok (values, errors) =>
      .ok (annotatedResponseValuesToResponseValues values, errors)

private theorem annotatedResponseFieldsToResponseFields_append
    (left right : List AnnotatedResponseField)
    : annotatedResponseFieldsToResponseFields (left ++ right)
      = annotatedResponseFieldsToResponseFields left
        ++ annotatedResponseFieldsToResponseFields right := by
  induction left with
  | nil => simp [annotatedResponseFieldsToResponseFields]
  | cons field rest ih =>
      cases field
      simp [annotatedResponseFieldsToResponseFields, ih]

private theorem combineAnnotatedResponseFields_toResponse
    (left right : Result (List AnnotatedResponseField))
    : annotatedResponseFieldsResultToResponse (Result.combine List.append left right)
      = Result.combine List.append (annotatedResponseFieldsResultToResponse left)
          (annotatedResponseFieldsResultToResponse right) := by
  cases left with
  | error leftErrors => cases right <;> rfl
  | ok left =>
      rcases left with ⟨left, leftErrors⟩
      cases right with
      | error rightErrors => rfl
      | ok right =>
          rcases right with ⟨right, rightErrors⟩
          simp [annotatedResponseFieldsResultToResponse,
            annotatedResponseFieldsToResponseFields_append, Result.combine]

private theorem combineAnnotatedResponseValues_toResponse
    (left : Result AnnotatedResponseValue)
    (right : Result (List AnnotatedResponseValue))
    : annotatedResponseValuesResultToResponse (Result.combine List.cons left right)
      = Result.combine List.cons (annotatedResponseValueResultToResponse left)
          (annotatedResponseValuesResultToResponse right) := by
  cases left with
  | error leftErrors => cases right <;> rfl
  | ok left =>
      rcases left with ⟨left, leftErrors⟩
      cases right with
      | error rightErrors => rfl
      | ok right =>
          rcases right with ⟨right, rightErrors⟩
          simp [annotatedResponseValueResultToResponse,
            annotatedResponseValuesResultToResponse, Result.combine,
            annotatedResponseValuesToResponseValues]

private theorem singleAnnotatedResponseFieldResult_toResponse
    (schema : Schema) (variableValues : VariableValues)
    (definition : FieldDefinition) (responseName : Name) (field : ExecutableField)
    (completed : Result AnnotatedResponseValue)
    : annotatedResponseFieldsResultToResponse
        (singleAnnotatedResponseFieldResult schema variableValues definition responseName
          field completed)
      = singleFieldResult responseName
          (annotatedResponseValueResultToResponse completed) := by
  cases completed with
  | error errors => rfl
  | ok completed =>
      rcases completed with ⟨outcome, errors⟩
      simp [singleAnnotatedResponseFieldResult, annotatedResponseFieldsResultToResponse,
        annotatedResponseValueResultToResponse, singleFieldResult,
        annotatedResponseFieldsToResponseFields]

private theorem completeNonNullAnnotatedResponseValue_toResponse
    (completed : Result AnnotatedResponseValue)
    : annotatedResponseValueResultToResponse
        (completeNonNullAnnotatedResponseValue completed)
      = nonNullCompletion (annotatedResponseValueResultToResponse completed) := by
  cases completed with
  | error errors => rfl
  | ok completed =>
      rcases completed with ⟨outcome, errors⟩
      cases outcome <;> cases errors <;>
        simp [completeNonNullAnnotatedResponseValue, annotatedResponseValueResultToResponse,
          nonNullCompletion, AnnotatedResponseValue.toResponseValue]

private theorem catchAnnotatedResponseBubbleObject_toResponse
    (runtimeType : Name)
    (completed : Result (List AnnotatedResponseField))
    : annotatedResponseValueResultToResponse
        (catchAnnotatedResponseBubbleAsNull (AnnotatedResponseValue.object runtimeType)
          completed)
      = catchBubbleAsNull ResponseValue.object
          (annotatedResponseFieldsResultToResponse completed) := by
  cases completed with
  | error errors =>
      simp [catchAnnotatedResponseBubbleAsNull, annotatedResponseValueResultToResponse,
        annotatedResponseFieldsResultToResponse, catchBubbleAsNull,
        AnnotatedResponseValue.toResponseValue]
  | ok completed =>
      rcases completed with ⟨outcome, errors⟩
      simp [catchAnnotatedResponseBubbleAsNull, annotatedResponseValueResultToResponse,
        annotatedResponseFieldsResultToResponse, catchBubbleAsNull,
        AnnotatedResponseValue.toResponseValue]

private theorem catchAnnotatedResponseBubbleList_toResponse
    (completed : Result (List AnnotatedResponseValue))
    : annotatedResponseValueResultToResponse
        (catchAnnotatedResponseBubbleAsNull AnnotatedResponseValue.list completed)
      = catchBubbleAsNull ResponseValue.list
          (annotatedResponseValuesResultToResponse completed) := by
  cases completed with
  | error errors =>
      simp [catchAnnotatedResponseBubbleAsNull, annotatedResponseValueResultToResponse,
        annotatedResponseValuesResultToResponse, catchBubbleAsNull,
        AnnotatedResponseValue.toResponseValue]
  | ok completed =>
      rcases completed with ⟨outcome, errors⟩
      simp [catchAnnotatedResponseBubbleAsNull, annotatedResponseValueResultToResponse,
        annotatedResponseValuesResultToResponse, catchBubbleAsNull,
        AnnotatedResponseValue.toResponseValue]

private theorem annotatedResponseExecution_toResponse_all
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    : (∀ fuel source groups,
        annotatedResponseFieldsResultToResponse
          (executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
            source groups)
        = executeCollectedFields schema resolvers variableValues fuel source groups)
      ∧ (∀ fuel source responseName fields,
          annotatedResponseFieldsResultToResponse
            (executeQueryAnnotatedField schema resolvers variableValues fuel source
              responseName fields)
          = GraphQL.Execution.executeField schema resolvers variableValues fuel source
              responseName fields)
      ∧ (∀ fuel fieldType fields value,
          annotatedResponseValueResultToResponse
            (completeAnnotatedResponseValue schema resolvers variableValues fuel fieldType
              fields value)
          = GraphQL.Execution.completeValue schema resolvers variableValues fuel fieldType
              fields value)
      ∧ (∀ fuel itemType fields values,
          annotatedResponseValuesResultToResponse
            (completeAnnotatedResponseValueList schema resolvers variableValues fuel
              itemType fields values)
          = GraphQL.Execution.completeValueList schema resolvers variableValues fuel
              itemType fields values) := by
  apply executeQueryAnnotatedCollectedFields.mutual_induct schema resolvers variableValues
  all_goals
    simp_all [executeQueryAnnotatedCollectedFields, executeQueryAnnotatedField,
      completeAnnotatedResponseValue, completeAnnotatedResponseValueList,
      executeCollectedFields, GraphQL.Execution.executeField,
      GraphQL.Execution.completeValue, GraphQL.Execution.completeValueList,
      singleFieldResult, catchBubbleAsNull, nonNullCompletion,
      handleFieldError, combineAnnotatedResponseFields_toResponse,
      combineAnnotatedResponseValues_toResponse, singleAnnotatedResponseFieldResult_toResponse,
      completeNonNullAnnotatedResponseValue_toResponse,
      catchAnnotatedResponseBubbleObject_toResponse,
      catchAnnotatedResponseBubbleList_toResponse, outOfFuel]
  all_goals
    simp_all [annotatedResponseFieldsResultToResponse, annotatedResponseValueResultToResponse,
      annotatedResponseValuesResultToResponse, AnnotatedResponseValue.toResponseValue,
      annotatedResponseFieldsToResponseFields, annotatedResponseValuesToResponseValues]
  case case6 =>
    intro source responseName field definition hlookup hresolve
    cases definition.outputType <;>
      simp [AnnotatedResponseValue.toResponseValue]
  case case7 =>
    intro source responseName field definition hlookup coercedArguments hcoerce hresolve
    cases definition.outputType <;>
      simp [AnnotatedResponseValue.toResponseValue]

private theorem executeQueryAnnotatedCollectedFields_toResponse
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    : annotatedResponseFieldsResultToResponse
        (executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel source
          groups)
      = executeCollectedFields schema resolvers variableValues fuel source groups :=
  (annotatedResponseExecution_toResponse_all schema resolvers variableValues).1 fuel
    source groups

-- Removing resolver-call definitions from the annotated response gives exactly
-- specification execution at the same fuel.
theorem executeQueryAnnotatedWithFuel_toResponse
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
        source).toResponse
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation
          fuel source := by
  simp only [executeQueryAnnotatedWithFuel, GraphQL.Execution.executeQueryWithFuel]
  let coercedVariableValues := coerceVariableValues operation variableValues
  let groups :=
    collectFields schema coercedVariableValues (operation.rootType schema) source
      operation.selectionSet
  have hresponse :=
    executeQueryAnnotatedCollectedFields_toResponse schema resolvers
      coercedVariableValues fuel source groups
  cases hroot : rootSourceAppliesBool schema operation source with
  | false =>
      simp [AnnotatedResponse.toResponse, AnnotatedResponseValue.toResponseValue]
  | true =>
      simp only [if_true]
      cases hannotated
            : executeQueryAnnotatedCollectedFields schema resolvers
                coercedVariableValues fuel source groups with
      | error errors =>
          rw [hannotated] at hresponse
          simp [annotatedResponseFieldsResultToResponse] at hresponse
          simp [Execution.executeRootSelectionSet, groups,
            coercedVariableValues, ← hresponse, AnnotatedResponse.toResponse,
            AnnotatedResponseValue.toResponseValue, selectionSetResultToResponse]
      | ok completed =>
          rcases completed with ⟨fields, errors⟩
          rw [hannotated] at hresponse
          simp [annotatedResponseFieldsResultToResponse] at hresponse
          simp [Execution.executeRootSelectionSet, groups,
            coercedVariableValues, ← hresponse, AnnotatedResponse.toResponse,
            AnnotatedResponseValue.toResponseValue, selectionSetResultToResponse]

theorem executeQueryAnnotated_toResponse
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : (executeQueryAnnotated schema resolvers variableValues operation source).toResponse
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  exact executeQueryAnnotatedWithFuel_toResponse schema resolvers variableValues
    operation (executeQueryFuelBound schema operation) source

theorem executeQueryAnnotated_equal (schema : Schema) (operation : Operation)
    : ExecuteQueryAnnotatedEqual schema operation := by
  intro ObjectRef resolvers variableValues source
  exact executeQueryAnnotated_toResponse schema resolvers variableValues operation source

end TreeSummary
end GraphQL
