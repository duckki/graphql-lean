import GraphQL.NamedFragment.Execution
import GraphQL.Algorithms.ExecutionCancelingSiblings
import GraphQL.Theories.AnnotatedExecution
import GraphQL.Theories.ConditionTree.Execution
import GraphQL.Algorithms.ExecutionUngrouped
import GraphQL.Algorithms.ExecutionUngroupedUncached
import GraphQL.Algorithms.ExecutionBreadth
import GraphQL.IncrementalDelivery.Execution
import Tests.GraphQL.Execution

/-! Nullable completion errors stay at their response positions in every executor.
Non-null wrappers propagate one counted error through fields, objects, and lists.
-/

open GraphQL GraphQL.Execution

namespace GraphQL.Tests.CompletionErrors

local instance : BEq ResponseValue where
  beq := GraphQL.Tests.Execution.responseEqBool

local instance : BEq Response where
  beq left right := left.data == right.data && left.errors == right.errors

local instance : BEq (Result ResponseValue) where
  beq
    | .error left, .error right => left == right
    | .ok (left, leftErrors), .ok (right, rightErrors) =>
        left == right && leftErrors == rightErrors
    | _, _ => false

def schemaFor (fieldType : TypeRef) : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .interface
          { name := "Node", fields := [{ name := "id", outputType := .named "ID" }] },
        .object
          {
            name := "A",
            fields := [{ name := "id", outputType := .named "ID" }],
            interfaces := ["Node"]
          },
        .object { name := "B", fields := [{ name := "id", outputType := .named "ID" }] },
        .object
          {
            name := "Query",
            fields :=
              [
                { name := "f", outputType := fieldType },
                { name := "hello", outputType := .named "String" }
              ]
          }
      ]
  }

def resolvers (value : Option (ResolverValue PUnit)) : Resolvers :=
  {
    resolve :=
      fun parent field _ _ =>
        match parent, field with
        | "Query", "f" => value
        | _, "hello" => some (.scalar "ok")
        | _, "id" => some (.scalar "1")
        | _, _ => none
    resolve_argumentsEquivalent := by intros; rfl
  }

def operationFor (fieldType : TypeRef) : Operation :=
  {
    selectionSet :=
      [
        .field "f" "f" [] []
          (if fieldType.namedType == "Node" then [.field "id" "id" [] [] []] else []),
        .field "hello" "hello" [] [] []
      ]
  }

def query (fieldType : TypeRef) (value : Option (ResolverValue PUnit)) : Response :=
  executeQuery (schemaFor fieldType) (resolvers value) [] (operationFor fieldType)
    (.object "Query" ())

def check [BEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  if actual != expected then
    throw
      (IO.userError s!"{label}:\nactual: {reprStr actual}\nexpected: {reprStr expected}")

def mismatchCases : List (String × TypeRef × ResolverValue PUnit) :=
  [
    ("scalar/composite", .named "Node", .scalar "x"),
    ("wrong runtime type", .named "Node", .object "B" ()),
    ("list/named", .named "String", .list []),
    ("non-list/list", .list (.named "String"), .scalar "x")
  ]

def nestedSchema (parentNonNull childNonNull : Bool) : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Parent",
            fields :=
              [
                {
                  name := "bad",
                  outputType :=
                    if childNonNull then .nonNull (.named "String") else .named "String"
                },
                { name := "innerSibling", outputType := .named "String" }
              ]
          },
        .object
          {
            name := "Query",
            fields :=
              [
                {
                  name := "parent",
                  outputType :=
                    if parentNonNull then .nonNull (.named "Parent") else .named "Parent"
                },
                { name := "hello", outputType := .named "String" }
              ]
          }
      ]
  }

def nestedResolvers : Resolvers :=
  {
    resolve :=
      fun parent field _ _ =>
        match parent, field with
        | "Query", "parent" => some (.object "Parent" ())
        | "Parent", "bad" => some (.list [])
        | _, _ => some (.scalar "ok")
    resolve_argumentsEquivalent := by intros; rfl
  }

def nestedOperation : Operation :=
  {
    selectionSet :=
      [
        .field "parent" "parent" [] []
          [.field "bad" "bad" [] [] [], .field "innerSibling" "innerSibling" [] [] []],
        .field "hello" "hello" [] [] []
      ]
  }

def run : IO Unit := do
  for (label, fieldType, value) in mismatchCases do
    let complete := completeValue (schemaFor fieldType) (resolvers (some value)) [] 20
    check (label ++ ": nullable completion") (complete fieldType [] value)
      (.ok (.null, 1))
    check (label ++ ": non-null completion") (complete (.nonNull fieldType) [] value)
      (.error 1)
    check (label ++ ": nullable list/item")
      (complete (.list fieldType) [] (.list [value])) (.ok (.list [.null], 1))
    check (label ++ ": non-null list, nullable item")
      (complete (.nonNull (.list fieldType)) [] (.list [value])) (.ok (.list [.null], 1))
    check (label ++ ": nullable list, non-null item")
      (complete (.list (.nonNull fieldType)) [] (.list [value])) (.ok (.null, 1))
    check (label ++ ": non-null list/item")
      (complete (.nonNull (.list (.nonNull fieldType))) [] (.list [value])) (.error 1)
    check (label ++ ": nullable query field") (query fieldType (some value))
      { data := .object [("f", .null), ("hello", .scalar "ok")], errors := 1 }
    check (label ++ ": non-null query field") (query (.nonNull fieldType) (some value))
      { data := .null, errors := 1 }
  check "nullable resolver null" (query (.named "String") (some .null))
    { data := .object [("f", .null), ("hello", .scalar "ok")], errors := 0 }
  check "non-null resolver null" (query (.nonNull (.named "String")) (some .null))
    { data := .null, errors := 1 }
  check "nullable resolver failure" (query (.named "String") none)
    { data := .object [("f", .null), ("hello", .scalar "ok")], errors := 1 }
  check "non-null resolver failure" (query (.nonNull (.named "String")) none)
    { data := .null, errors := 1 }
  check "nullable ancestor catches non-null child"
    (executeQuery (nestedSchema false true) nestedResolvers [] nestedOperation
      (.object "Query" ()))
    { data := .object [("parent", .null), ("hello", .scalar "ok")], errors := 1 }
  check "non-null ancestor propagates non-null child"
    (executeQuery (nestedSchema true true) nestedResolvers [] nestedOperation
      (.object "Query" ()))
    { data := .null, errors := 1 }
  check "non-null ancestor keeps nullable child error"
    (executeQuery (nestedSchema true false) nestedResolvers [] nestedOperation
      (.object "Query" ()))
    {
      data :=
        .object
          [
            ("parent", .object [("bad", .null), ("innerSibling", .scalar "ok")]),
            ("hello", .scalar "ok")
          ],
      errors := 1
    }
  check "non-null introduces missing error" (nonNullCompletion (.ok (.null, 0)))
    (.error 1)
  check "non-null preserves existing error" (nonNullCompletion (.ok (.null, 1)))
    (.error 1)
  check "non-null preserves multiple errors" (nonNullCompletion (.ok (.null, 2)))
    (.error 2)
  check "non-null preserves success with child errors"
    (nonNullCompletion (.ok (.scalar "ok", 2))) (.ok (.scalar "ok", 2))

def runOtherExecutors : IO Unit := do
  for (label, fieldType, value) in mismatchCases do
    let wrappers : List (String × TypeRef × ResolverValue PUnit × Result ResponseValue) :=
      [
        ("nullable", fieldType, value, .ok (.null, 1)),
        ("non-null", .nonNull fieldType, value, .error 1),
        ("nullable list/item", .list fieldType, .list [value], .ok (.list [.null], 1)),
        (
          "non-null list, nullable item",
          .nonNull (.list fieldType),
          .list [value],
          .ok (.list [.null], 1)
        ),
        (
          "nullable list, non-null item",
          .list (.nonNull fieldType),
          .list [value],
          .ok (.null, 1)
        ),
        (
          "non-null list/item",
          .nonNull (.list (.nonNull fieldType)),
          .list [value],
          .error 1
        )
      ]
    for (wrapper, typ, raw, expected) in wrappers do
      let labelPrefix := label ++ ": " ++ wrapper ++ ": "
      let schema := schemaFor typ
      let env := resolvers (some raw)
      check (labelPrefix ++ "named fragments")
        (GraphQL.NamedFragment.Execution.completeValue schema env [] [] 20 typ
          [{ fieldName := "f", arguments := [], selectionSet := [] }] raw) expected
      check (labelPrefix ++ "canceling siblings")
        (GraphQL.Algorithms.ExecutionCancelingSiblings.completeValue schema env [] 20 typ
          [{ fieldName := "f", arguments := [], selectionSet := [] }] raw) expected
      check (labelPrefix ++ "annotated")
        ((GraphQL.AnnotatedExecution.completeAnnotatedResponseValue schema env [] 20 typ
            [{ fieldName := "f", arguments := [], selectionSet := [] }] raw).map
          (fun (response, errors) => (response.toResponseValue, errors))) expected
      check (labelPrefix ++ "condition tree")
        (GraphQL.ConditionTree.completeValue schema env [] typ
          [{ fieldName := "f", arguments := [], selectionSet := [] }] raw) expected
      check (labelPrefix ++ "ungrouped cached")
        (GraphQL.Algorithms.ExecutionUngrouped.outputResult
          GraphQL.Algorithms.ExecutionUngrouped.FieldCacheValue.output
          (GraphQL.Algorithms.ExecutionUngrouped.completeValue schema env [] 20 typ [] raw
            none))
        expected
      check (labelPrefix ++ "ungrouped uncached")
        (GraphQL.Algorithms.ExecutionUngroupedUncached.completeValue schema env [] 20 typ
          [] raw none)
        expected
      let incremental :=
        (GraphQL.IncrementalDelivery.Execution.completeValue schema env [] 20 typ []
          raw).run
          0
      check (labelPrefix ++ "incremental") incremental.1.result expected
      let slot :=
        (GraphQL.Algorithms.ExecutionBreadth.buildValueSlot schema [] typ raw []).2
      check (labelPrefix ++ "breadth")
        (GraphQL.Algorithms.ExecutionBreadth.completeSlot typ slot ∅).1 expected

#eval run
#eval runOtherExecutors

end GraphQL.Tests.CompletionErrors
