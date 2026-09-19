import GraphQL.Theories.ExecutionReadiness
import Proofs.GraphQL.Theories.ExecutionReadiness.Checker

namespace GraphQL.Tests.ExecutionReadiness

private def requiredArg : InputValueDefinition :=
  { name := "a", inputType := .nonNull (.named "Int") }

private def f : FieldDefinition :=
  { name := "f", outputType := .named "String", arguments := [requiredArg] }

private def dead : FieldDefinition :=
  { name := "dead", outputType := .nonNull (.named "Empty") }

private def schema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .interface
          {
            name := "I",
            fields :=
              [{
                f with
                  arguments := [{ requiredArg with defaultValue := some (.int 1) }]
              }]
          },
        .interface
          {
            name := "Empty", fields := [{ name := "name", outputType := .named "String" }]
          },
        .object
          {
            name := "Query",
            interfaces := ["I"],
            fields :=
              [
                f,
                dead,
                { name := "id", outputType := .nonNull (.named "String") },
                { name := "box", outputType := .named "Node" },
                { name := "boxes", outputType := .list (.named "Node") },
                { name := "abstract", outputType := .named "I" },
                { name := "nullableDead", outputType := .named "Empty" },
                { name := "listDead", outputType := .list (.nonNull (.named "Empty")) },
                {
                  name := "requiredListDead",
                  outputType := .nonNull (.list (.nonNull (.named "Empty")))
                },
                {
                  name := "withDefault",
                  outputType := .named "String",
                  arguments := [{ requiredArg with defaultValue := some (.int 1) }]
                }
              ]
          },
        .object { name := "Node", interfaces := ["I"], fields := [f, dead] }
      ]
  }

private def field (name : Name) (children : List Selection := [])
    (directives : List DirectiveApplication := []) (arguments : List Argument := [])
    : Selection :=
  .field name name arguments directives children

private def nameSelection : List Selection := [field "name"]

private def variables : List VariableDefinition :=
  [
    { name := "x", typeRef := .nonNull (.named "Boolean") },
    { name := "y", typeRef := .nonNull (.named "Boolean") }
  ]

private def check (selections : List Selection) (definitions := variables) :=
  checkExecutionError schema
    { selectionSet := selections, variableDefinitions := definitions }

-- Concrete implementations can drop a default present on the interface.
example : check [.inlineFragment (some "I") [] [field "f"]] = ⟨1, 0⟩ := by cbv
example : check [field "abstract" [field "f"]] = ⟨2, 0⟩ := by cbv
example : check [field "f", field "dead" nameSelection] = ⟨1, 1⟩ := by cbv
example : (check [field "f", field "dead" nameSelection]).errorCount = 2 := by cbv
example : (check [field "id", field "withDefault"]).isSuccess = true := by cbv

-- Empty abstract returns require inhabitants only for singular non-null outputs.
example : check [field "dead" nameSelection] = ⟨0, 1⟩ := by cbv

example
    : check
        [
          field "nullableDead" nameSelection,
          field "listDead" nameSelection,
          field "requiredListDead" nameSelection
        ]
      = ⟨0, 0⟩ := by cbv

-- Counts are local: a parent's recursive validation must not duplicate its child's error.
example : check [field "box" [field "f"]] = ⟨1, 0⟩ := by cbv

example
    : check
        [
          field "box" [field "dead" nameSelection],
          field "boxes" [field "dead" nameSelection]
        ]
      = ⟨0, 2⟩ := by cbv

-- Type conditions stay intersected with the actual enclosing runtime object.
example
    : check [.inlineFragment (some "Node") [] [field "f", field "dead" nameSelection]]
      = ⟨0, 0⟩ := by cbv

example
    : check [.inlineFragment (some "I") [] [.inlineFragment (some "Node") [] [field "f"]]]
      = ⟨0, 0⟩ := by cbv

example
    : check [field "box" [.inlineFragment (some "Query") [] [field "f"]]] = ⟨0, 0⟩ := by
  cbv

example
    : check [field "abstract" [.inlineFragment (some "Query") [] [field "f"]]]
      = ⟨1, 0⟩ := by cbv

-- Constant-false and contradictory Boolean paths are pruned before either count.
example
    : check
        [
          field "f" [] [.skip (.boolean true)],
          field "dead" nameSelection [.include (.boolean false)]
        ]
      = ⟨0, 0⟩ := by cbv

example
    : check [field "dead" nameSelection [.include (.variable "x"), .skip (.variable "x")]]
      = ⟨0, 0⟩ := by cbv

example
    : check
        [field "box" [field "f" [] [.skip (.variable "x")]] [.include (.variable "x")]]
      = ⟨0, 0⟩ := by cbv

example
    : check
        [.inlineFragment none [.include (.variable "x")]
          [field "box" [field "dead" nameSelection [.skip (.variable "x")]]]]
      = ⟨0, 0⟩ := by cbv

example
    : check
        [field "box" [field "f" [] [.include (.variable "y")]] [.include (.variable "x")]]
      = ⟨1, 0⟩ := by cbv

-- Independent siblings do not constrain one another; defaults remain overridable.
example
    : check
        [field "f" [] [.include (.variable "x")], field "f" [] [.skip (.variable "x")]]
      = ⟨2, 0⟩ := by cbv

example
    : check [field "f" [] [.include (.variable "x")]]
        [{
          name := "x",
          typeRef := .nonNull (.named "Boolean"),
          defaultValue := some (.boolean false)
        }]
      = ⟨1, 0⟩ := by cbv

-- Supplied arguments rely on prior validation at the declared interface location.
-- In particular, its default permits a nullable variable even when Query.f has none.
example
    : check
        [.inlineFragment (some "I") []
          [field "f" [] [] [{ name := "a", value := .variable "a" }]]]
        [{ name := "a", typeRef := .named "Int" }]
      = ⟨0, 0⟩ := by cbv

example
    : check
        [.inlineFragment (some "I") []
          [field "f" [] [] [{ name := "a", value := .int 1 }]]]
      = ⟨0, 0⟩ := by cbv

-- Nullable arguments do not need defaults; non-null lists do when omitted.
example
    : omittedNonNullArgumentsHaveDefaultsBool
        [{ requiredArg with inputType := .named "Int" }] []
      = true := by cbv

example
    : omittedNonNullArgumentsHaveDefaultsBool
        [{ requiredArg with inputType := .nonNull (.list (.named "Int")) }] []
      = false := by cbv

example
    : omittedNonNullArgumentsHaveDefaultsBool
        [{
          requiredArg with
            inputType := .nonNull (.list (.named "Int"))
            defaultValue := some (.list [])
        }] []
      = true := by cbv

-- The checker certifies both predicates even when a pruned field cannot execute safely.
private def skippedOperation : Operation :=
  { selectionSet := [field "dead" nameSelection [.skip (.boolean true)]] }

example
    : operationCompositeFieldTypesInhabited schema skippedOperation
      ∧ operationCoercibleInPossibleTypes schema skippedOperation := by
  exact checkExecutionError_sound (by cbv)

-- Parent and child conditions use the same environment throughout the predicates.
private def contradictoryOperation : Operation :=
  {
    variableDefinitions := variables
    selectionSet :=
      [field "box"
        [field "dead" nameSelection [.skip (.variable "x")]]
        [.include (.variable "x")]]
  }

example
    : operationCompositeFieldTypesInhabited schema contradictoryOperation
      ∧ operationCoercibleInPossibleTypes schema contradictoryOperation := by
  exact checkExecutionError_isSuccess_sound (by cbv)

-- An enabled uninhabited output still violates the predicate.
example
    : ¬ operationCompositeFieldTypesInhabited schema
          {
            selectionSet := [field "dead" nameSelection [.include (.variable "x")]]
          } := by
  intro h
  have hfields := h [("x", .boolean true)]
  unfold selectionSetCompositeFieldTypesInhabited at hfields
  have hfield := hfields _ List.mem_cons_self
  unfold selectionCompositeFieldTypesInhabited at hfield
  have hreturn := (hfield rfl dead rfl rfl).1
  exact hreturn rfl

-- An interface fragment preserves the concrete root; other implementations are
-- irrelevant unless reached through an abstract field return.
private def concreteScopeSchema : Schema :=
  {
    queryType := "Ready"
    types :=
      [
        .interface
          {
            name := "I",
            fields :=
              [{
                f with
                  arguments := [{ requiredArg with defaultValue := some (.int 1) }]
              }]
          },
        .object
          {
            name := "Ready",
            interfaces := ["I"],
            fields :=
              [{
                f with
                  arguments := [{ requiredArg with defaultValue := some (.int 1) }]
              }]
          },
        .object { name := "Missing", interfaces := ["I"], fields := [f] }
      ]
  }

example
    : operationCompositeFieldTypesInhabited concreteScopeSchema
        { selectionSet := [.inlineFragment (some "I") [] [field "f"]] }
      ∧ operationCoercibleInPossibleTypes concreteScopeSchema
          { selectionSet := [.inlineFragment (some "I") [] [field "f"]] } := by
  exact checkExecutionError_sound (by cbv)

end GraphQL.Tests.ExecutionReadiness
