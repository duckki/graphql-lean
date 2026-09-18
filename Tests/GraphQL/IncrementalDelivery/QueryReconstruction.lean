import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryReconstruction

/-! Actual merging preserves causal parent creation and rejects unavailable parents. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryReconstruction
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- The final public witness retains precisely the public complete-success boundary. -/
example (schema : Schema) (operation : Operation)
    : mergedExecutionEquivalentToBasic schema operation :=
  mergedExecutionEquivalentToBasic_holds schema operation

/-- A streamed parent and its deferred child may arrive in one response; the parent's
item publication precedes the child's object patch inside that response.
-/
def nested : QueryResult :=
  .incremental
    {
      data := .object [("items", .list [])],
      pending := [{ id := "0", path := [.field "items"] }],
      hasNext := true
    }
    [{
      pending := [{ id := "1", path := [.field "items", .index 0] }],
      incremental := [.list "0" [.object []], .object "1" [("x", .scalar "one")]],
      completed := [{ id := "0" }, { id := "1" }],
      hasNext := false
    }]

/-- Actual ID lookup and merging reconstruct the nested item, by reduction. -/
example
    : mergeQueryResult nested
      = some { data := .object [("items", .list [.object [("x", .scalar "one")]])] } := by
  rfl

/-- Successful reconstruction is stronger than ID lifecycle validity: reordering a
child ahead of its not-yet-present parent cannot merge, by reduction.
-/
example
    : applyAtoms
        [
          .object [.field "items", .index 0] [("x", .scalar "one")],
          .item [.field "items"] (.object [])
        ]
        (.object [("items", .list [])])
      = none := by
  rfl

/-- Equal-valued stream items occupy distinct successive positions and both survive. -/
example
    : applyAtoms
        [.item [.field "items"] (.scalar "same"), .item [.field "items"] (.scalar "same")]
        (.object [("items", .list [.scalar "initial"])])
      = some
          (.object
            [("items", .list [.scalar "initial", .scalar "same", .scalar "same"])]) := by
  rfl

/-- Adjacent nonempty streamed payloads may coalesce without changing actual merging. -/
example (path : ResponsePath) (data : ResponseValue) (items : List ResponseValue)
    (nonempty : items ≠ [])
    : applyAtoms (items.map (PositionAtom.item path)) data
      = ResponseMerging.modifyAtPath path
          (fun value =>
            match value with
            | .list existing => some (.list (existing ++ items))
            | _ => none) data :=
  applyAtoms_items path items nonempty data

end GraphQL.IncrementalDelivery.Tests.QueryReconstruction
