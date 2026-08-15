import GraphQL.Execution

/-! Annotated responses and the concrete executor that produces them.

`AnnotatedResponse` has the same recursive shape as GraphQL response data, but every
object field retains its concrete resolved field provenance: parent type, field name,
original arguments, and the argument-coercion result.
Removing that metadata produces ordinary `Execution.Response` data.

The executor constructs this response directly. Condition resolutions and merged runtime
field groups are execution history, not part of the concrete semantics observed by an
analysis.
-/

namespace GraphQL
namespace AnnotatedExecution

open GraphQL.Execution

universe u v

-----------------------------------------------------------------------------------------
-- Annotated responses
-----------------------------------------------------------------------------------------

-- The concrete field provenance represented by one response field. `coercedArguments`
-- distinguishes successful coercion from failure before resolver invocation.
structure ResolvedFieldProvenance where
  parentType : Name
  fieldName : Name
  originalArguments : List Argument
  coercedArguments : ArgumentCoercionResult
deriving Repr

mutual
  inductive AnnotatedResponseValue where
    | null
    | scalar (value : String)
    | object (runtimeType : Name) (fields : List AnnotatedResponseField)
    | list (values : List AnnotatedResponseValue)
  deriving Repr

  inductive AnnotatedResponseField where
    | resolved
      (responseName : Name)
      (provenance : ResolvedFieldProvenance)
      (value : AnnotatedResponseValue)
  deriving Repr
end

structure AnnotatedResponse where
  data : AnnotatedResponseValue
  errors : Nat := 0
deriving Repr

namespace AnnotatedResponseField

def responseName : AnnotatedResponseField -> Name
  | .resolved responseName _provenance _value => responseName

def provenance : AnnotatedResponseField -> ResolvedFieldProvenance
  | .resolved _responseName provenance _value => provenance

def value : AnnotatedResponseField -> AnnotatedResponseValue
  | .resolved _responseName _provenance value => value

end AnnotatedResponseField

-- Resolved field provenance retained for the representative of one collected
-- response-name group. This small constructor is the trusted boundary for the metadata
-- added by annotated execution.
def resolvedFieldProvenance (schema : Schema) (variableValues : VariableValues)
    (definition : FieldDefinition) (field : ExecutableField)
    : ResolvedFieldProvenance :=
  {
    parentType := field.parentType
    fieldName := field.fieldName
    originalArguments := field.arguments
    coercedArguments :=
      coerceArgumentValues schema variableValues definition.arguments field.arguments
  }

-----------------------------------------------------------------------------------------
-- Annotated execution
-----------------------------------------------------------------------------------------

def completeNonNullAnnotatedResponseValue (completed : Result AnnotatedResponseValue)
    : Result AnnotatedResponseValue :=
  match completed with
  | .error errors => .error errors
  | .ok (outcome, errors) =>
      match outcome with
      | .null =>
          .error
          <| match errors with
              | 0 => 1
              | errors + 1 => errors + 1
      | _ => .ok (outcome, errors)

def singleAnnotatedResponseFieldResult
    (schema : Schema) (variableValues : VariableValues) (definition : FieldDefinition)
    (responseName : Name) (field : ExecutableField)
    (completed : Result AnnotatedResponseValue)
    : Result (List AnnotatedResponseField) :=
  match completed with
  | .error errors => .error errors
  | .ok (value, errors) =>
      .ok
        (
          [.resolved responseName
            (resolvedFieldProvenance schema variableValues definition field) value],
          errors
        )

def catchAnnotatedResponseBubbleAsNull
    (wrap : α -> AnnotatedResponseValue)
    (completed : Result α)
    : Result AnnotatedResponseValue :=
  match completed with
  | .error errors => .ok (.null, errors)
  | .ok (outcome, errors) =>
      .ok (wrap outcome, errors)

mutual
  def executeQueryAnnotatedCollectedFields
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (source : ResolverValue ObjectRef)
      : List (Name × List ExecutableField) -> Result (List AnnotatedResponseField)
    | [] => .ok ([], 0)
    | (responseName, fields) :: rest =>
        let head :=
          executeQueryAnnotatedField schema resolvers variableValues fuel source
            responseName fields
        let tail :=
          executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel source
            rest
        Result.combine List.append head tail

  def executeQueryAnnotatedField
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (source : ResolverValue ObjectRef)
      (responseName : Name)
      : List ExecutableField -> Result (List AnnotatedResponseField)
    | [] => .error 1
    | field :: rest =>
        match fuel with
        | 0 => .error 1
        | fuel' + 1 =>
            match schema.lookupField field.parentType field.fieldName with
            | none => .error 1
            | some definition =>
                match coerceArgumentValues schema variableValues definition.arguments
                        field.arguments with
                | .error =>
                    let completed : Result AnnotatedResponseValue :=
                      match definition.outputType with
                      | .nonNull _inner => .error 1
                      | _ => .ok (.null, 1)
                    singleAnnotatedResponseFieldResult schema variableValues definition
                      responseName field completed
                | .success coercedArguments =>
                    match resolveFieldValue resolvers field.parentType field.fieldName
                            coercedArguments source with
                    | none =>
                        let completed : Result AnnotatedResponseValue :=
                          match definition.outputType with
                          | .nonNull _inner => .error 1
                          | _ => .ok (.null, 1)
                        singleAnnotatedResponseFieldResult schema variableValues
                          definition responseName field completed
                    | some resolved =>
                        singleAnnotatedResponseFieldResult schema variableValues
                          definition responseName field
                          (completeAnnotatedResponseValue schema resolvers variableValues
                            fuel' definition.outputType (field :: rest) resolved)

  def completeAnnotatedResponseValue
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : Nat -> TypeRef -> List ExecutableField -> ResolverValue ObjectRef
        -> Result AnnotatedResponseValue
    | 0, _fieldType, _fields, _value =>
        .error 1
    | fuel, .nonNull inner, fields, value =>
        completeNonNullAnnotatedResponseValue
          (completeAnnotatedResponseValue schema resolvers variableValues fuel inner
            fields value)
    | _fuel + 1, _fieldType, _fields, .null =>
        .ok (.null, 0)
    | _fuel + 1, .named typeName, _fields, .scalar value =>
        if (TypeRef.named typeName).isCompositeBool schema then
          .error 1
        else
          .ok (.scalar value, 0)
    | fuel + 1, .named parentType, fields, source@(.object runtimeType _ref) =>
        if schema.typeIncludesObjectBool parentType runtimeType then
          let childGroups :=
            collectSubfields schema variableValues runtimeType source fields
          let completed :=
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
              source childGroups
          catchAnnotatedResponseBubbleAsNull
            (AnnotatedResponseValue.object runtimeType) completed
        else
          .error 1
    | fuel + 1, .list inner, fields, .list values =>
        let completed :=
          completeAnnotatedResponseValueList schema resolvers variableValues fuel inner
            fields values
        catchAnnotatedResponseBubbleAsNull AnnotatedResponseValue.list completed
    | _fuel + 1, .named _typeName, _fields, .list _values =>
        .error 1
    | _fuel + 1, .list _inner, _fields, _value =>
        .error 1

  def completeAnnotatedResponseValueList
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (itemType : TypeRef) (fields : List ExecutableField)
      : List (ResolverValue ObjectRef) -> Result (List AnnotatedResponseValue)
    | [] => .ok ([], 0)
    | value :: values =>
        let head :=
          completeAnnotatedResponseValue schema resolvers variableValues fuel itemType
            fields value
        let tail :=
          completeAnnotatedResponseValueList schema resolvers variableValues fuel itemType
            fields values
        Result.combine List.cons head tail
end

def executeQueryAnnotatedWithFuel
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : AnnotatedResponse :=
  let coercedVariableValues := coerceVariableValues operation variableValues
  if rootSourceAppliesBool schema operation source then
    match executeQueryAnnotatedCollectedFields schema resolvers coercedVariableValues fuel
            source
            (collectFields schema coercedVariableValues (operation.rootType schema) source
              operation.selectionSet) with
    | .error errors =>
        { data := .null, errors }
    | .ok (fields, errors) =>
        let runtimeType := (runtimeObjectType? source).getD (operation.rootType schema)
        { data := .object runtimeType fields, errors }
  else
    { data := .null, errors := 1 }

-- Default annotated-response entry point using the same public fuel bound as
-- `Execution.executeQuery`.
def executeQueryAnnotated
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : AnnotatedResponse :=
  executeQueryAnnotatedWithFuel schema resolvers variableValues operation
    (executeQueryFuelBound schema operation) source

-----------------------------------------------------------------------------------------
-- Annotated-response execution correctness statements
-----------------------------------------------------------------------------------------

mutual
  def AnnotatedResponseValue.toResponseValue (annotated : AnnotatedResponseValue)
      : ResponseValue :=
    match annotated with
    | .null => .null
    | .scalar value => .scalar value
    | .object _runtimeType fields =>
        .object (annotatedResponseFieldsToResponseFields fields)
    | .list values => .list (annotatedResponseValuesToResponseValues values)
  termination_by sizeOf annotated
  decreasing_by all_goals simp_wf <;> omega

  def annotatedResponseValuesToResponseValues (annotated : List AnnotatedResponseValue)
      : List ResponseValue :=
    match annotated with
    | [] => []
    | value :: rest =>
        value.toResponseValue :: annotatedResponseValuesToResponseValues rest
  termination_by sizeOf annotated
  decreasing_by all_goals simp_wf <;> omega

  def annotatedResponseFieldsToResponseFields (fields : List AnnotatedResponseField)
      : List (Name × ResponseValue) :=
    match fields with
    | [] => []
    | .resolved responseName _definition value :: rest =>
        (responseName, value.toResponseValue)
        :: annotatedResponseFieldsToResponseFields rest
  termination_by sizeOf fields
  decreasing_by all_goals simp_wf <;> omega
end

def AnnotatedResponse.toResponse (annotated : AnnotatedResponse) : Response :=
  { data := annotated.data.toResponseValue, errors := annotated.errors }

-- Removing resolved field provenance from `executeQueryAnnotated` gives exactly
-- `Execution.executeQuery`. Its theorem witness is `executeQueryAnnotated_equal` in
-- `Proofs.GraphQL.Theories.AnnotatedExecution`.
def ExecuteQueryAnnotatedEqual (schema : Schema) (operation : Operation) : Prop :=
  ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef),
    (executeQueryAnnotated schema resolvers variableValues operation source).toResponse
    = executeQuery schema resolvers variableValues operation source

-----------------------------------------------------------------------------------------
-- Termination theorems over annotated responses.
-----------------------------------------------------------------------------------------

namespace AnnotatedResponseValue

mutual
  -- Counts value nodes. Object fields contribute the size of their values; the object
  -- node itself supplies the strict decrease needed when descending into a field.
  def structuralSize : AnnotatedResponseValue -> Nat
    | .null => 1
    | .scalar _ => 1
    | .object _ fields => 1 + fieldListStructuralSize fields
    | .list values => 1 + valueListStructuralSize values

  def fieldListStructuralSize : List AnnotatedResponseField -> Nat
    | [] => 0
    | .resolved _ _ value :: fields =>
        structuralSize value + fieldListStructuralSize fields

  def valueListStructuralSize : List AnnotatedResponseValue -> Nat
    | [] => 0
    | value :: values => structuralSize value + valueListStructuralSize values
end

theorem structuralSize_lt_of_object_field_mem {name provenance value runtimeType}
    {fields : List AnnotatedResponseField}
    (member : .resolved name provenance value ∈ fields)
    : value.structuralSize
      < (AnnotatedResponseValue.object runtimeType fields).structuralSize := by
  induction fields with
  | nil => simp at member
  | cons field fields ih =>
      cases field with
      | resolved fieldName fieldProvenance fieldValue =>
          simp only [List.mem_cons] at member
          rcases member with h | h
          · injection h with _ _ hvalue
            subst value
            change fieldValue.structuralSize
              < 1 + (fieldValue.structuralSize
                + AnnotatedResponseValue.fieldListStructuralSize fields)
            omega
          · have hlt := ih h
            change value.structuralSize
              < 1 + AnnotatedResponseValue.fieldListStructuralSize fields at hlt
            change value.structuralSize
              < 1 + (fieldValue.structuralSize
                + AnnotatedResponseValue.fieldListStructuralSize fields)
            omega

private theorem size_lt_list_head (value : AnnotatedResponseValue)
    (values : List AnnotatedResponseValue)
    : value.structuralSize
      < (AnnotatedResponseValue.list (value :: values)).structuralSize := by
  simp [AnnotatedResponseValue.structuralSize,
    AnnotatedResponseValue.valueListStructuralSize]
  omega

private theorem size_lt_list_tail (value : AnnotatedResponseValue)
    (values : List AnnotatedResponseValue)
    : (AnnotatedResponseValue.list values).structuralSize
      < (AnnotatedResponseValue.list (value :: values)).structuralSize := by
  cases value <;> simp [AnnotatedResponseValue.structuralSize,
    AnnotatedResponseValue.valueListStructuralSize] <;> omega

private theorem size_lt_list_of_mem {value}
    {values : List AnnotatedResponseValue}
    (member : value ∈ values)
    : value.structuralSize < (AnnotatedResponseValue.list values).structuralSize := by
  induction values with
  | nil => simp at member
  | cons head values ih =>
      simp only [List.mem_cons] at member
      rcases member with h | h
      · subst value
        exact size_lt_list_head head values
      · have hlt := ih h
        exact Nat.lt_trans hlt (size_lt_list_tail head values)

theorem structuralSize_lt_of_list_get? {value} {index : Nat}
    {values : List AnnotatedResponseValue}
    (found : values[index]? = some value)
    : value.structuralSize < (AnnotatedResponseValue.list values).structuralSize := by
  induction values generalizing index with
  | nil => simp at found
  | cons head values ih =>
      cases index with
      | zero =>
          simp at found
          subst value
          exact size_lt_list_head head values
      | succ index =>
          simp at found
          exact Nat.lt_trans (ih found) (size_lt_list_tail head values)

end AnnotatedResponseValue

end AnnotatedExecution
end GraphQL
