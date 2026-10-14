import Proofs.GraphQL.IncrementalDelivery.Semantics.SharedAncestorCollection
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Exact shared-construction regressions. Raw inconsistent contexts demonstrate why
the generated fold certificate matters; they do not refute the generated theorem. -/

namespace GraphQL.IncrementalDelivery.Tests.SharedAncestorConstruction

open GraphQL.IncrementalDelivery.Execution
open Semantics.SharedAncestorConstruction

private def chain : List DeferUsage :=
  [{ ref := 0 }, { ref := 1, ancestors := [0] }, { ref := 2, ancestors := [1, 0] }]

example : getNewDeferMapShared chain [] [] = getNewDeferMap chain [] [] := rfl

example : sharedDeferAncestors [] [] = [] := rfl

private def first : DeferredFragment := { node := { ref := 0, path := [.index 0] } }

private def parent : DeferredFragment :=
  {
    node := { ref := 1, path := [.index 0], label := some "parent" },
    ancestors := [first.node]
  }

example
    : fromParent [first, parent] (some { ref := 1, ancestors := [0] })
      = [parent.node, first.node] :=
  rfl

/-- An absent immediate parent must not erase a present older ancestor. -/
example : sharedDeferAncestors [first] [9, 0] = [first.node] := rfl

example
    : build [{ ref := 2, ancestors := [9, 0] }] [] [first]
      = getNewDeferMap [{ ref := 2, ancestors := [9, 0] }] [] [first] :=
  rfl

/-- Fully reversed raw input still uses the exact missing-parent fallback. -/
example : build chain.reverse [] [] = getNewDeferMap chain.reverse [] [] := rfl

private def lateAncestor : List DeferUsage :=
  [{ ref := 1, ancestors := [0] }, { ref := 0 }, { ref := 2, ancestors := [1, 0] }]

/-- A found parent's earlier missing suffix need not match the child's current lookups. -/
example : build lateAncestor [] [] ≠ getNewDeferMap lateAncestor [] [] := by
  intro equal
  have impossible := congrArg
    (fun context =>
      (lookupDeferredFragment? context 2).map
        (fun fragment => fragment.ancestors.map DeliveryNode.ref)) equal
  change some [1] = some [1, 0] at impossible
  cases impossible

private def shadow : DeferredFragment := { node := { ref := 0, path := [.index 1] } }

/-- A first-match append cannot shadow the descriptor captured by a stored suffix. -/
example
    : fromParent [first, parent, shadow] (some { ref := 1, ancestors := [0] })
      = resolve [first, parent, shadow] [1, 0] :=
  rfl

/-- Replacing the lookup context can invalidate metadata despite identical ancestor keys. -/
example
    : fromParent [shadow, parent] (some { ref := 1, ancestors := [0] })
      ≠ resolve [shadow, parent] [1, 0] := by
  intro equal
  have impossible := congrArg (List.map DeliveryNode.path) equal
  change ([[.index 0], [.index 0]] : List ResponsePath)
    = [[.index 0], [.index 1]] at impossible
  cases impossible

private def collected : FieldCollection × Nat :=
  (collectFields schema [] "Query" (.object "Query" 0)
    [defer [field "a", defer [field "b", defer [field "c"]]]]).run
    10

example
    : getNewDeferMapShared collected.1.newDeferUsages [] []
      = getNewDeferMap collected.1.newDeferUsages [] [] :=
  rootConstructionExact_holds Nat schema [] "Query" (.object "Query" 0) _ 10 []

/-- Descendant fields retain inherited defer context at object boundaries. -/
private def childFields : List FieldDetails :=
  [{
    fieldName := "user"
    arguments := []
    deferUsage := some { ref := 1, ancestors := [0] }
    selectionSet := [defer [field "name", defer [field "age"]]]
  }]

private def children : List DeferUsage :=
  ((collectSubfields schema [] "User" (.object "User" 1) childFields).run
    2).1.newDeferUsages

example
    : build children [.index 0, .field "user"] [first, parent]
      = getNewDeferMap children [.index 0, .field "user"] [first, parent] :=
  rfl

/-- Sibling object paths share inherited descriptors, not newly allocated child nodes. -/
example
    : build children [.index 1, .field "user"] [first, parent]
      = getNewDeferMap children [.index 1, .field "user"] [first, parent] :=
  rfl

example
    : (lookupDeferredFragment? (build children [.index 0] [first, parent]) 2).map
        (fun fragment => fragment.node.path)
      = some [.index 0] :=
  rfl

example
    : (lookupDeferredFragment? (build children [.index 1] [first, parent]) 2).map
        (fun fragment => fragment.node.path)
      = some [.index 1] :=
  rfl

private def siblingChildren : List DeferUsage :=
  ((collectSubfields schema [] "User" (.object "User" 2) childFields).run
    ((collectSubfields schema [] "User" (.object "User" 1) childFields).run
      2).2).1.newDeferUsages

/-- Consecutive object collections allocate distinct children under inherited owners. -/
example
    : (build siblingChildren [.index 1] [first, parent]).map
        (fun fragment => fragment.node.ref)
      = [0, 1, 4, 5] :=
  rfl

example
    : build siblingChildren [.index 1] [first, parent]
      = getNewDeferMap siblingChildren [.index 1] [first, parent] :=
  rfl

example : ParentExtensionExact := parentExtensionExact_holds
example : RootConstructionExact := rootConstructionExact_holds

#print axioms coherent_getNewDeferMap
#print axioms parentExtensionExact_holds
#print axioms rootConstructionExact_holds
#print axioms subfields_build_eq

end GraphQL.IncrementalDelivery.Tests.SharedAncestorConstruction
