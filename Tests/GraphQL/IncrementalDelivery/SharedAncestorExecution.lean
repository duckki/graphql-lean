import Tests.GraphQL.IncrementalDelivery.Execution

/-! Public-executor snapshots for validating shared-construction runtime refinements.
Snapshots retain ordered descriptors, full ancestry, source addresses, and pure outcomes.
This module imports definitions only; the public executor keeps the general constructor. -/

namespace GraphQL.IncrementalDelivery.Tests.SharedAncestorExecution

open GraphQL.IncrementalDelivery.Execution

#guard_msgs (drop info) in
#check_failure GraphQL.IncrementalDelivery.Execution.getNewDeferMapShared
#guard_msgs (drop info) in
#check_failure GraphQL.IncrementalDelivery.Execution.sharedDeferAncestors

private inductive Entry where
  | task (address : List Nat) (groups : List DeferredFragment) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue)))
  | stream (address : List Nat) (node : DeliveryNode)
    (items : List (Result ResponseValue))
deriving Repr

mutual
  private def entries (work : Work) (address : List Nat := []) : List Entry :=
    match work with
    | .empty => []
    | .combine left right =>
        entries left (address ++ [0]) ++ entries right (address ++ [1])
    | .executionGroup groups path result children =>
        .task address groups path result :: entries children (address ++ [0])
    | .stream node items =>
        .stream address node (items.map Prod.fst) :: itemEntries items address 0

  private def itemEntries (items : List (Result ResponseValue × Work))
      (address : List Nat) (index : Nat)
      : List Entry :=
    match items with
    | [] => []
    | (_, work) :: rest =>
        entries work (address ++ [index]) ++ itemEntries rest address (index + 1)
end

private def run (selections : List Selection) (state : Nat := 0)
    (variables : VariableValues := [])
    : Completion (List (Name × ResponseValue)) × Nat :=
  (executeRootSelectionSetCore schema resolvers variables 30 "Query" (.object "Query" 0)
    selections).run
    state

private def inherited :=
  [defer
    [defer
      [field "users"
        [defer [field "name", defer [field "age"] (some "age")] (some "name")]]
      (some "inner")]
    (some "outer")]

private def sharedOwners :=
  [
    defer [field "user" [defer [field "name"]]],
    defer [field "user" [defer [field "age"]]]
  ]

private def streamed :=
  [defer
    [field "users" [defer [field "name", defer [field "age"]]]
      [.stream (.boolean true) (some (.string "users")) (.int 1)]]]

private def failures :=
  [defer [defer [field "user" [defer [field "required"], defer [field "name"]]]]]

private def node (key : Nat) (path : ResponsePath := [])
    (label : Option DirectiveLabel := none)
    : DeliveryNode :=
  { ref := key, path, label }

private def fragment (node : DeliveryNode) (ancestors : List DeliveryNode := [])
    : DeferredFragment :=
  { node, ancestors }

private def value (address : List Nat) (groups : List DeferredFragment)
    (path : ResponsePath) (data : List (Name × ResponseValue))
    : Entry :=
  .task address groups path (.ok (data, 0))

private def agrees (selections : List Selection) (expected : List Entry) (next : Nat)
    (state : Nat := 0) (variables : VariableValues := [])
    : Bool :=
  let (completed, finish) := run selections state variables
  same (completed.result, entries completed.work, finish)
    ((.ok ([], 0) : Result (List (Name × ResponseValue))), expected, next)

/- Inherited descriptors survive sibling list-item allocations with distinct child paths. -/
#guard
  let outer := node 0 [] (some "outer")
  let inner := node 1 [] (some "inner")
  let left := [.field "users", .index 0]
  let right := [.field "users", .index 1]
  let leftName := node 2 left (some "name")
  let rightName := node 4 right (some "name")
  agrees inherited
    [
      value [1, 0] [fragment inner [outer]] []
        [("users", .list [.object [], .object []])],
      value [1, 0, 0, 0, 0, 1, 0] [fragment leftName [inner, outer]] left
        [("name", .scalar "name1")],
      value [1, 0, 0, 0, 0, 1, 1, 0]
        [fragment (node 3 left (some "age")) [leftName, inner, outer]] left
        [("age", .scalar "1")],
      value [1, 0, 0, 0, 1, 0, 1, 0] [fragment rightName [inner, outer]] right
        [("name", .scalar "name2")],
      value [1, 0, 0, 0, 1, 0, 1, 1, 0]
        [fragment (node 5 right (some "age")) [rightName, inner, outer]] right
        [("age", .scalar "2")]
    ]
    6

/- One shared task retains separate complete ancestry for its two descendant branches. -/
#guard
  let path := [.field "user"]
  agrees sharedOwners
    [
      value [1, 0] [fragment (node 0), fragment (node 1)] [] [("user", .object [])],
      value [1, 0, 0, 0, 1, 0] [fragment (node 2 path) [node 0]] path
        [("name", .scalar "name1")],
      value [1, 0, 0, 0, 1, 1, 0] [fragment (node 3 path) [node 1]] path
        [("age", .scalar "1")]
    ]
    4

/- Initial items inherit defer context; noninitial stream items start their own boundary. -/
#guard
  let left := [.field "users", .index 0]
  let right := [.field "users", .index 1]
  agrees streamed
    [
      value [1, 0] [fragment (node 0)] [] [("users", .list [.object []])],
      value [1, 0, 0, 0, 0, 0, 1, 0] [fragment (node 1 left) [node 0]] left
        [("name", .scalar "name1")],
      value [1, 0, 0, 0, 0, 0, 1, 1, 0]
        [fragment (node 2 left) [node 1 left, node 0]] left [("age", .scalar "1")],
      .stream [1, 0, 0, 0, 1] (node 3 [.field "users"] (some "users"))
        [.ok (.object [], 0)],
      value [1, 0, 0, 0, 1, 0, 1, 0] [fragment (node 4 right)] right
        [("name", .scalar "name2")],
      value [1, 0, 0, 0, 1, 0, 1, 1, 0] [fragment (node 5 right) [node 4 right]] right
        [("age", .scalar "2")]
    ]
    6

/- Failed and successful siblings keep the same full inherited ancestry and source order. -/
#guard
  let path := [.field "user"]
  agrees failures
    [
      value [1, 0] [fragment (node 1) [node 0]] [] [("user", .object [])],
      .task [1, 0, 0, 0, 1, 0] [fragment (node 2 path) [node 1, node 0]] path (.error 1),
      value [1, 0, 0, 0, 1, 1, 0] [fragment (node 3 path) [node 1, node 0]] path
        [("name", .scalar "name1")]
    ]
    4

private def chain : Nat → List Selection
  | 0 => [field "a"]
  | depth + 1 => [defer (chain depth)]

/- Latent empty ancestors remain in the full chain, including with a nonzero fresh supply. -/
#guard
  [1, 2, 8, 32].all
    (fun depth =>
      agrees (chain depth)
        [value [1, 0]
          [fragment (node (20 + depth - 1))
            ((List.range (depth - 1)).reverse.map (fun key => node (20 + key)))]
          [] [("a", .scalar "a")]]
        (20 + depth) 20)

private def conditional :=
  [defer
    [.inlineFragment none [.include (.variable "enabled")]
      [defer [field "user" [defer [field "name"]]]]]]

#guard agrees conditional [] 1 0 [("enabled", .boolean false)]

#guard
  let path := [.field "user"]
  agrees conditional
    [
      value [1, 0] [fragment (node 1) [node 0]] [] [("user", .object [])],
      value [1, 0, 0, 0, 1, 0] [fragment (node 2 path) [node 1, node 0]] path
        [("name", .scalar "name1")]
    ]
    3 0 [("enabled", .boolean true)]

end GraphQL.IncrementalDelivery.Tests.SharedAncestorExecution
