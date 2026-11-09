import Proofs.GraphQL.Execution.InputDefaults
import GraphQL.NamedFragment.Execution
import Proofs.GraphQL.Validation.FieldMerge
import Tests.GraphQL.Execution

/-! Opaque custom-scalar inputs, defaults, wrapper rules, and executable argument preparation. -/

open GraphQL GraphQL.Execution

namespace GraphQL.Tests.CustomScalars

local instance : BEq ConstInputValue where
  beq left right :=
    InputValue.structuralEquivalentBool left.toInputValue right.toInputValue

local instance : BEq InputCoercionResult where
  beq
    | .undefined, .undefined | .error, .error => true
    | .success left, .success right => left == right
    | _, _ => false

local instance : BEq CoercedArgument where
  beq left right := left.name == right.name && left.value == right.value

local instance : BEq ArgumentCoercionResult where
  beq
    | .error, .error => true
    | .success left, .success right => left == right
    | _, _ => false

local instance : BEq ResponseValue where
  beq := GraphQL.Tests.Execution.responseEqBool

local instance : BEq Response where
  beq left right := left.data == right.data && left.errors == right.errors

def payload : ConstInputValue :=
  .object [("k", .int 1), ("nested", .object []), ("items", .list [.null, .boolean true])]

def schema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .customScalar { name := "JSON" },
        .enum { name := "Status", values := ["PUBLIC"] },
        .inputObject
          {
            name := "Options"
            inputFields :=
              [
                {
                  name := "payload",
                  inputType := .named "JSON",
                  defaultValue := some payload
                },
                {
                  name := "limit",
                  inputType := .named "Int",
                  defaultValue := some (.int 7)
                }
              ]
          },
        .object
          {
            name := "Query"
            fields :=
              [{
                name := "f",
                outputType := .named "JSON"
                arguments :=
                  [{
                    name := "a",
                    inputType := .nonNull (.named "JSON")
                    defaultValue := some payload
                  }]
              }]
          }
      ]
  }

theorem jsonInput : (TypeRef.named "JSON").isInputType schema :=
  ⟨.customScalar { name := "JSON" }, rfl, trivial⟩

theorem payload_default_valid
    : Schema.ConstInputValueIsCorrectType schema payload (.named "JSON") :=
  .objectCustomScalar _ _ { name := "JSON" } jsonInput rfl

theorem payload_literal_valid
    : Validation.ValueIsCorrectTypeAtLocation schema [] payload.toInputValue
        (.named "JSON") none :=
  .objectCustomScalar _ _ _ { name := "JSON" } jsonInput rfl ⟨payload, rfl⟩

theorem payload_list_default_valid
    : Schema.ConstInputValueIsCorrectType schema payload (.list (.named "JSON")) :=
  .objectAsListItem _ _ jsonInput
    (.intro _ _ (.objectCustomScalar _ _ { name := "JSON" } jsonInput rfl))

theorem payload_list_literal_valid
    : Validation.ValueIsCorrectTypeAtLocation schema [] payload.toInputValue
        (.list (.named "JSON")) none :=
  .objectAsListItem _ _ _ jsonInput
    (.intro _ _
      (.objectCustomScalar _ _ _ { name := "JSON" } jsonInput rfl ⟨payload, rfl⟩))

theorem payload_nonNull_default_valid
    : Schema.ConstInputValueIsCorrectType schema payload (.nonNull (.named "JSON")) :=
  .nonNull _ _ jsonInput (by simp [payload]) payload_default_valid

theorem payload_nonNull_literal_valid
    : Validation.ValueIsCorrectTypeAtLocation schema [] payload.toInputValue
        (.nonNull (.named "JSON")) (some payload) :=
  .nonNull _ _ _ jsonInput
    (by simp [payload, ConstInputValue.toInputValue])
    (by intro name; simp [payload, ConstInputValue.toInputValue])
    payload_literal_valid

theorem argument_default_wellFormed
    : SchemaWellFormedness.inputValueDefinitionWellFormed schema
        {
          name := "a", inputType := .nonNull (.named "JSON"), defaultValue := some payload
        } :=
  ⟨jsonInput, payload_nonNull_default_valid⟩

theorem variable_default_valid
    : Validation.variableDefinitionValid schema
        {
          name := "x", typeRef := .nonNull (.named "JSON"), defaultValue := some payload
        } :=
  ⟨jsonInput, payload_nonNull_default_valid⟩

def resolvers : Resolvers :=
  {
    resolve := fun _ _ _ _ => some (.scalar "ok")
    resolve_argumentsEquivalent := by intros; rfl
  }

def operation (arguments : List Argument) : Operation :=
  { selectionSet := [.field "f" "f" arguments [] []] }

theorem literal_operation_valid
    : Validation.operationDefinitionValid schema
        (operation [{ name := "a", value := payload.toInputValue }]) := by
  have jsonOutput : schema.isOutputType "JSON" :=
    ⟨.customScalar { name := "JSON" }, rfl, trivial⟩
  have jsonLeaf : schema.isLeafType "JSON" :=
    ⟨.customScalar { name := "JSON" }, rfl, trivial⟩
  let field : FieldMerge.ScopedField :=
    { parentType := "Query"
      responseName := "f"
      fieldName := "f"
      arguments := [{ name := "a", value := payload.toInputValue }]
      outputType := .named "JSON"
      selectionSet := [] }
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨_, rfl, trivial⟩
  · simp [operation, Validation.variableDefinitionsValid]
  · simp [operation]
  · unfold Validation.selectionSetValid
    intro selection member
    cases List.mem_singleton.mp member
    unfold Validation.selectionValid
    refine ⟨by simp [Validation.directivesValid], _, rfl, ?_, ?_⟩
    · refine ⟨by decide, ?_, ?_⟩
      · intro argument member
        cases List.mem_singleton.mp member
        exact ⟨_, rfl, payload_nonNull_literal_valid⟩
      · intro definition member required
        cases List.mem_singleton.mp member
        simp [Validation.isRequiredArgument, Validation.isRequiredInputValueDefinition,
          InputValueDefinition.isRequired] at required
    · unfold Validation.fieldSelectionSetValid
      exact ⟨jsonOutput, Or.inl ⟨jsonLeaf, rfl⟩⟩
  · apply FieldMerge.FieldsInSetCanMerge.intro
    dsimp only
    intro left leftMember right rightMember _
    have hcollect : FieldMerge.collectFields schema
        ((operation [{ name := "a", value := payload.toInputValue }]).rootType schema)
        (operation [{ name := "a", value := payload.toInputValue }]).selectionSet = [field] := by
      simp [FieldMerge.collectFields, operation, Operation.rootType, OperationType.rootType,
        Schema.lookupField, Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
        schema, field, TypeDefinition.name, TypeDefinition.fields?, BuiltinScalar.name, List.find?]
    rw [hcollect] at leftMember rightMember
    cases List.mem_singleton.mp leftMember
    cases List.mem_singleton.mp rightMember
    apply FieldMerge.fieldsForNameCanMerge_self_of_children
    · exact ⟨jsonOutput, jsonOutput, fun _ => rfl⟩
    · decide
    · exact .intro _ [] (by simp [FieldMerge.collectFields])
  · simp [Validation.operationVariablesUsed, operation]

def check [BEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  if actual != expected then
    throw (IO.userError s!"{label}: {reprStr actual}; expected {reprStr expected}")

def run : IO Unit := do
  check "opaque object literal"
    (coerceInputValue schema [] (.named "JSON") payload.toInputValue) (.success payload)
  check "non-null opaque object"
    (coerceInputValue schema [] (.nonNull (.named "JSON")) payload.toInputValue)
    (.success payload)
  check "whole variable payload"
    (coerceInputValue schema [("x", payload)] (.named "JSON") (.variable "x"))
    (.success payload)
  check "null remains nullable" (coerceInputValue schema [] (.named "JSON") .null)
    (.success .null)
  check "null rejected at non-null"
    (coerceInputValue schema [] (.nonNull (.named "JSON")) .null) .error
  check "string payload" (coerceInputValue schema [] (.named "JSON") (.string "s"))
    (.success (.string "s"))
  check "list payload stays a scalar payload"
    (coerceInputValue schema [] (.named "JSON") (.list [payload.toInputValue]))
    (.success (.list [payload]))
  check "object singleton at list location"
    (coerceInputValue schema [] (.list (.named "JSON")) payload.toInputValue)
    (.success (.list [payload]))
  check "list of non-null custom scalars"
    (coerceInputValue schema [] (.list (.nonNull (.named "JSON")))
      (.list [payload.toInputValue]))
    (.success (.list [payload]))
  check "input-object defaults surrounding opaque custom scalar"
    (coerceInputValue schema [] (.named "Options") (.object []))
    (.success (.object [("payload", payload), ("limit", .int 7)]))
  check "explicit opaque field receives no internal defaults"
    (coerceInputValue schema [] (.named "Options") (.object [("payload", .object [])]))
    (.success (.object [("payload", .object []), ("limit", .int 7)]))
  check "unknown surrounding input field rejected"
    (coerceInputValue schema [] (.named "Options") (.object [("unknown", .int 1)])) .error
  for name in ["String", "Int", "Boolean", "ID", "Status", "Query", "Missing"] do
    check (name ++ " does not become an opaque object input")
      (coerceInputValue schema [] (.named name) payload.toInputValue) .error
  check "unresolved nested variable is not an opaque constant"
    (coerceInputValue schema [("x", .int 1)] (.named "JSON")
      (.object [("k", .variable "x")])) .error
  let expected : Response := { data := .object [("f", .scalar "ok")], errors := 0 }
  check "execute object literal and custom scalar result"
    (executeQuery schema resolvers []
      (operation [{ name := "a", value := payload.toInputValue }]) (.object "Query" ()))
    expected
  check "execute argument default"
    (executeQuery schema resolvers [] (operation []) (.object "Query" ())) expected
  let variableOperation :=
    {
      operation [{ name := "a", value := .variable "x" }] with
        variableDefinitions :=
          [{
            name := "x",
            typeRef := .nonNull (.named "JSON")
            defaultValue := some payload
          }]
    }
  check "execute supplied object variable"
    (executeQuery schema resolvers [("x", payload)] variableOperation
      (.object "Query" ())) expected
  check "execute opaque variable default"
    (executeQuery schema resolvers [] variableOperation (.object "Query" ())) expected
  check "materialized argument payload preserved"
    (coerceArgumentValues schema []
      [{ name := "a", inputType := .nonNull (.named "JSON") }]
      [{ name := "a", value := payload.toInputValue }])
    (.success [{ name := "a", value := payload }])
  let namedOperation : GraphQL.NamedFragment.Operation :=
    {
      selectionSet :=
        [.field "f" "f" [{ name := "a", value := payload.toInputValue }] [] []]
    }
  check "named-fragment executor accepts opaque payload"
    (GraphQL.NamedFragment.Execution.executeQuery schema resolvers [] namedOperation
      (.object "Query" ()))
    expected

theorem opaque_payload_preserved (values : VariableValues) (value : ConstInputValue)
    : coerceInputValue schema values (.named "JSON") value.toInputValue
      = .success value :=
  coerceInputValue_customScalar_const schema values "JSON" { name := "JSON" } value rfl

theorem reordered_payload_arguments_equivalent
    : ArgumentCoercionResult.equivalent
        (coerceArgumentValues schema [] [{ name := "a", inputType := .named "JSON" }]
          [{ name := "a", value := .object [("k", .int 1), ("nested", .object [])] }])
        (coerceArgumentValues schema [] [{ name := "a", inputType := .named "JSON" }]
          [{
            name := "a", value := .object [("nested", .object []), ("k", .int 1)]
          }]) := by
  apply coerceArgumentValues_equivalent_of_equivalent <;> decide

#eval run

#print axioms opaque_payload_preserved
#print axioms coerceInputValueBounded_success_of_valid_of_defaults

end GraphQL.Tests.CustomScalars
