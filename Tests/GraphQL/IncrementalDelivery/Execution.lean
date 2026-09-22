import GraphQL.IncrementalDelivery

/-! Standalone definition-level regression checks; no Proofs imports.
Shared schema, resolver, and operation fixtures for incremental execution.
-/

namespace GraphQL.IncrementalDelivery.Tests

open GraphQL.IncrementalDelivery.Execution

#guard_msgs (drop info) in
#check_failure SharedGroupValue
#guard_msgs (drop info) in
#check_failure selectGroupOwner
#guard_msgs (drop info) in
#check_failure normalizeGroupValues

def schema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query",
            fields :=
              [
                { name := "a", outputType := .named "String" },
                { name := "b", outputType := .named "String" },
                { name := "c", outputType := .named "String" },
                { name := "fail", outputType := .named "String" },
                { name := "required", outputType := .nonNull (.named "String") },
                { name := "user", outputType := .named "User" },
                { name := "users", outputType := .list (.named "User") },
                { name := "values", outputType := .list (.named "String") },
                {
                  name := "nonNullValues",
                  outputType := .nonNull (.list (.named "String"))
                },
                { name := "empty", outputType := .list (.named "String") },
                { name := "strict", outputType := .list (.nonNull (.named "String")) },
                { name := "matrix", outputType := .list (.list (.named "String")) }
              ]
          },
        .object
          {
            name := "User",
            fields :=
              [
                { name := "name", outputType := .named "String" },
                { name := "age", outputType := .named "String" },
                { name := "required", outputType := .nonNull (.named "String") },
                { name := "values", outputType := .list (.named "String") }
              ]
          }
      ]
  }

def resolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ field _ source =>
        match field, source with
        | "fail", _ | "required", _ => none
        | "user", _ => some (.object "User" 1)
        | "users", _ => some (.list [.object "User" 1, .object "User" 2])
        | "empty", _ => some (.list [])
        | "values", _ | "nonNullValues", _ =>
            some (.list [.scalar "x", .null, .scalar "z"])
        | "strict", _ => some (.list [.scalar "x", .null, .scalar "z"])
        | "matrix", _ =>
            some (.list [.list [.scalar "x", .scalar "y"], .list [.scalar "z"]])
        | "name", .object _ ref => some (.scalar ("name" ++ toString ref))
        | "age", .object _ ref => some (.scalar (toString ref))
        | _, _ => some (.scalar field)
    resolve_argumentsEquivalent := by intros; rfl
  }

def field (name : Name) (children : List Selection := [])
    (directives : List DirectiveApplication := []) (alias : Option Name := none)
    : Selection :=
  .field (alias.getD name) name [] directives children

def defer (children : List Selection) (label : Option String := none)
    (condition : InputValue := .boolean true)
    : Selection :=
  .inlineFragment none [.defer condition (label.map InputValue.string)] children

def start (scheduler : WorkScheduler) (selections : List Selection)
    (variables : VariableValues := [])
    (definitions : List VariableDefinition := [])
    : ExecutionResult :=
  executeQuery scheduler schema resolvers variables
    { selectionSet := selections, variableDefinitions := definitions } (.object "Query" 0)

def same [Repr α] (actual expected : α) : Bool := reprStr actual == reprStr expected

/-- An intentionally unusable source detects that ordinary queries need no source law. -/
def unavailable : WorkScheduler :=
  ⟨fun _ =>
    {
      initialGroups := [],
      initialStreams := [],
      workEventStream := { admissible := fun _ => False, finished := fun _ => False }
    }⟩

/-! Ordinary queries return directly, without consulting or observing a work source. -/

#guard
  match start unavailable [field "a"] with
  | .single response => same response { data := .object [("a", .scalar "a")] }
  | _ => false

/-! Initialization is explicit; even an unavailable source is not consumed at query time.
Such a factory is useful here but fails the independent scheduler conformance predicate.
-/

#guard
  match start unavailable [field "a", defer [field "b"]] with
  | .incremental initial stream =>
      same initial.data (.object [("a", .scalar "a")])
      && initial.hasNext
      && stream.source.history.isEmpty
  | _ => false

/-- Disabled, empty, and skipped defer blocks retain the ordinary response branch. -/
def ordinaryResponse (selections : List Selection) : Option Response :=
  match start unavailable selections with
  | .single response => some response
  | .incremental .. => none

#guard
  same (ordinaryResponse [defer [field "a"] none (.boolean false)])
    (some { data := .object [("a", .scalar "a")] : Response })
#guard
  same (ordinaryResponse [field "a", defer []])
    (some { data := .object [("a", .scalar "a")] : Response })
#guard
  same
    (ordinaryResponse
      [field "a", .inlineFragment none [.defer, .skip (.boolean true)] [field "b"]])
    (some { data := .object [("a", .scalar "a")] : Response })

end GraphQL.IncrementalDelivery.Tests
