import GraphQL
import Proofs.GraphQL.Execution.Typename
import Proofs.GraphQL.Validation.Typename
import Tests.GraphQL.Execution

open GraphQL GraphQL.Execution

namespace GraphQL.Tests.Typename

/-! Implicit lookup, resolver bypass, aliases, abstract returns, and all public executors. -/

local instance : BEq ResponseValue where
  beq := GraphQL.Tests.Execution.responseEqBool

local instance : BEq Response where
  beq left right := left.data == right.data && left.errors == right.errors

local instance : BEq TypeRef where
  beq left right := decide (left = right)

def fieldSignature (field : FieldDefinition) : Name × TypeRef × Nat :=
  (field.name, field.outputType, field.arguments.length)

def schema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [
                { name := "node", outputType := .named "Node" },
                { name := "search", outputType := .named "Search" },
                { name := "nodes", outputType := .list (.named "Node") },
                { name := "label", outputType := .named "String" }
              ]
          },
        .interface
          { name := "Node", fields := [{ name := "id", outputType := .named "ID" }] },
        .object
          {
            name := "Person",
            fields := [{ name := "id", outputType := .named "ID" }],
            interfaces := ["Node"]
          },
        .object
          {
            name := "Dog",
            fields := [{ name := "id", outputType := .named "ID" }],
            interfaces := ["Node"]
          },
        .union { name := "Search", members := ["Person", "Dog"] },
        .inputObject { name := "Filter", inputFields := [] },
        .enum { name := "Choice", values := ["A"] },
        .customScalar { name := "JSON" }
      ]
  }

def resolvers : Resolvers :=
  {
    resolve :=
      fun parent field _ _ =>
        match parent, field with
        | "Query", "node" => some (.object "Person" ())
        | "Query", "search" => some (.object "Dog" ())
        | "Query", "nodes" => some (.list [.object "Person" (), .object "Dog" ()])
        | _, "label" => some (.scalar "ordinary")
        | _, _ => none
    resolve_argumentsEquivalent := by intros; rfl
  }

def rejected : Resolvers :=
  {
    resolve := fun _ _ _ _ => none
    resolve_argumentsEquivalent := by intros; rfl
  }

def operation : Operation :=
  {
    selectionSet :=
      [
        .field "kind" "__typename" [] [] [],
        .field "kind" "__typename" [] [] [],
        .field "omitted" "__typename" [] [.skip (.boolean true)] [],
        .field "excluded" "__typename" [] [.include (.boolean false)] [],
        .field "included" "__typename" [] [.include (.boolean true)] [],
        .field "node" "node" [] [] [.field "kind" "__typename" [] [] []],
        .field "search" "search" [] [] [.field "kind" "__typename" [] [] []],
        .field "nodes" "nodes" [] [] [.field "kind" "__typename" [] [] []],
        .field "__typename" "label" [] [] []
      ]
  }

def expected : Response :=
  {
    data :=
      .object
        [
          ("kind", .scalar "Query"),
          ("included", .scalar "Query"),
          ("node", .object [("kind", .scalar "Person")]),
          ("search", .object [("kind", .scalar "Dog")]),
          (
            "nodes",
            .list
              [.object [("kind", .scalar "Person")], .object [("kind", .scalar "Dog")]]
          ),
          ("__typename", .scalar "ordinary")
        ]
  }

theorem object_selection_valid
    : Validation.selectionValid schema [] "Person"
        (.field "type" "__typename" [] [] []) :=
  Validation.typename_selection_valid schema [] _ _ []
    ⟨
      .object
        {
          name := "Person"
          fields := [{ name := "id", outputType := .named "ID" }]
          interfaces := ["Node"]
        },
      rfl,
      trivial
    ⟩ (by simp [Validation.directivesValid])

theorem interface_selection_valid
    : Validation.selectionValid schema [] "Node" (.field "type" "__typename" [] [] []) :=
  Validation.typename_selection_valid schema [] _ _ []
    ⟨
      .interface
        { name := "Node", fields := [{ name := "id", outputType := .named "ID" }] },
      rfl,
      trivial
    ⟩ (by simp [Validation.directivesValid])

theorem union_composite : schema.isCompositeType "Search" :=
  ⟨.union { name := "Search", members := ["Person", "Dog"] }, rfl, trivial⟩

theorem union_selection_valid
    : Validation.selectionValid schema [] "Search"
        (.field "type" "__typename" [] [] []) :=
  Validation.typename_selection_valid schema [] _ _ [] union_composite
    (by simp [Validation.directivesValid])

theorem arguments_rejected
    : ¬ Validation.selectionValid schema [] "Search"
          (.field "type" "__typename" [{ name := "x", value := .int 1 }] [] []) := by
  intro hvalid
  have hnil := Validation.typename_selection_arguments_eq_nil schema [] _ _ _ _ _
    union_composite hvalid
  contradiction

theorem children_rejected
    : ¬ Validation.selectionValid schema [] "Search"
          (.field "type" "__typename" [] [] [.field "id" "id" [] [] []]) := by
  intro hvalid
  have hnil := Validation.typename_selection_children_eq_nil schema [] _ _ _ _ _
    union_composite hvalid
  contradiction

def check [BEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  if actual != expected then
    throw (IO.userError s!"{label}: {reprStr actual}; expected {reprStr expected}")

def run : IO Unit := do
  for name in ["Query", "Node", "Person", "Dog", "Search"] do
    check (name ++ " implicit field")
      ((schema.lookupField name "__typename").map fieldSignature)
      (some (fieldSignature Schema.typenameFieldDefinition))
    check (name ++ " declared field absent")
      (schema.lookupDeclaredField name "__typename").isSome false
  for name in ["String", "Int", "Choice", "JSON", "Filter", "Missing"] do
    check (name ++ " has no typename field")
      ((schema.lookupField name "__typename").map fieldSignature).isSome false
  check "ordinary field lookup"
    ((schema.lookupField "Query" "label").map fieldSignature)
    ((schema.lookupDeclaredField "Query" "label").map fieldSignature)
  check "union ordinary field rejected" (schema.lookupField "Search" "id").isSome false
  let conflict : Schema :=
    {
      queryType := "Query"
      types :=
        [.object
          {
            name := "Query",
            fields :=
              [{
                name := "__typename",
                outputType := .named "Int",
                arguments := [{ name := "x", inputType := .named "Int" }]
              }]
          }]
    }
  check "implicit definition wins"
    ((conflict.lookupField "Query" "__typename").map fieldSignature)
    (some (fieldSignature Schema.typenameFieldDefinition))
  check "declared lookup retains raw declaration"
    ((conflict.lookupDeclaredField "Query" "__typename").map FieldDefinition.outputType)
    (some (TypeRef.named "Int"))
  let source : ResolverValue := .object "Query" ()
  let query := executeQuery schema resolvers [] operation source
  check "main execution" query expected
  check "canceling siblings"
    (Algorithms.ExecutionCancelingSiblings.executeQuery schema resolvers [] operation
      source) expected
  check "cached ungrouped"
    (Algorithms.ExecutionUngrouped.executeQuery schema resolvers [] operation source)
    expected
  check "uncached ungrouped"
    (Algorithms.ExecutionUngroupedUncached.executeQuery schema resolvers [] operation
      source) expected
  check "annotated execution"
    ((AnnotatedExecution.executeQueryAnnotated schema resolvers [] operation
        source).toResponse) expected
  check "condition-tree execution"
    (ConditionTree.executeQuery schema resolvers [] operation source) expected
  check "breadth execution"
    (Algorithms.ExecutionBreadth.executeQueryWithSpecResolvers schema resolvers []
      operation source) expected
  let rootOnly : Operation := { selectionSet := [.field "t" "__typename" [] [] []] }
  let rootExpected : Response := { data := .object [("t", .scalar "Query")] }
  check "host resolver bypass"
    (executeQuery schema rejected [] rootOnly source) rootExpected
  let batchRejected : Algorithms.ExecutionBreadth.ResolverMap :=
    {
      resolve := fun _ _ _ _ => []
      resolve_argumentsEquivalent := by intros; rfl
    }
  check "batch host resolver bypass"
    (Algorithms.ExecutionBreadth.executeQuery schema batchRejected [] rootOnly source)
    rootExpected
  check "runtime name beats static parent"
    ((resolveFieldValue rejected "Node" "__typename" [] (.object "Person" ())).map
      (fun value =>
        match value with
        | .scalar name => some name
        | _ => none))
    (some (some "Person"))
  for value in [ResolverValue.null, .scalar "bad", .list []] do
    check "non-object typename source"
      (resolveFieldValue rejected "Query" "__typename" [] value).isSome false
  let namedOperation : NamedFragment.Operation :=
    {
      selectionSet :=
        [
          .field "t" "__typename" [] [] [],
          .field "node" "node" [] [] [.fragmentSpread "Type" []]
        ]
      fragmentDefinitions :=
        [{
          name := "Type"
          typeCondition := "Node"
          selectionSet := [.field "t" "__typename" [] [] []]
        }]
    }
  check "named fragment runtime typename"
    (NamedFragment.Execution.executeQuery schema resolvers [] namedOperation source)
    ({
        data :=
          .object [("t", .scalar "Query"), ("node", .object [("t", .scalar "Person")])]
      }
      : Response)
  let incrementalOperation : IncrementalDelivery.Operation :=
    {
      selectionSet :=
        [
          .field "t" "__typename" [] [] [],
          .field "search" "search" [] [] [.field "t" "__typename" [] [] []]
        ]
    }
  let queue : IncrementalDelivery.Execution.WorkQueue :=
    {
      initialGroups := [],
      initialStreams := [],
      workEventStream := IncrementalDelivery.EventSource.ofList []
    }
  match IncrementalDelivery.Execution.executeQuery (fun _ => queue) schema resolvers []
          incrementalOperation source with
  | .single response =>
      check "incremental executor runtime typename" response
        ({
            data :=
              .object [("t", .scalar "Query"), ("search", .object [("t", .scalar "Dog")])]
          }
          : Response)
  | .incremental _ _ => throw (IO.userError "unexpected incremental work")
  check "normalizer retains implicit field"
    ((NormalForm.normalizeOperation schema rootOnly).selectionSet.map
      Selection.responseName?)
    [some "t"]
  check "implicit field has completion fuel without declared fields"
    (Algorithms.ExecutionBreadth.schemaCompleteValueFuelBound
      { queryType := "Query", types := [.object { name := "Query", fields := [] }] }) 1

#eval run

#print axioms GraphQL.Execution.executeField_typename
#print axioms GraphQL.Execution.executeField_typename_eq

end GraphQL.Tests.Typename
