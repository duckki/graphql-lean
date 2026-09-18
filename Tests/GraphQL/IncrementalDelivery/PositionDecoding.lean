import GraphQL.IncrementalDelivery.Correctness

/-! Deterministic causal decoding is public, without proof imports or scheduler choices. -/

namespace GraphQL.IncrementalDelivery.Tests.PositionDecoding
open GraphQL.IncrementalDelivery.Execution

#guard_msgs (drop info) in
#check_failure DeliveryTrace.PositionPatch
#guard_msgs (drop info) in
#check_failure DeliveryTrace.PositionPatches
#guard_msgs (drop info) in
#check_failure DeliveryTrace.PositionUpdates

/-- A reusable absolute list path for the wire fixtures. -/
def path : ResponsePath := [.field "items"]

/-- A root-object notice and a later stream notice may refer to separate owners. -/
def root : IncrementalPendingNotice := { id := "root", path := [] }

/-- The stream ID resolves a list path, not an initial item index. -/
def stream : IncrementalPendingNotice := { id := "stream", path }

/-- An owner ID without an observed list cursor does not invent index zero. -/
example : DeliveryTrace.decodePatch false [stream] [] (.list "stream" [.null]) = none :=
  rfl

/-- A cursor without an announced owner does not license a payload. -/
example
    : DeliveryTrace.decodePatch false [] [(path, 0)] (.list "stream" [.null]) = none :=
  rfl

/-- Same-update notices are available before decoding the update's payloads. -/
example
    : DeliveryTrace.decodeUpdates false [] [(path, 3)]
        [{
          pending := [stream],
          incremental := [.list "stream" [.scalar "next"]],
          hasNext := true
        }]
      = some ([[path ++ [.index 3]]], [(path, 4), (path, 3)]) :=
  rfl

/-- A later response cannot retroactively announce an earlier payload's owner. -/
example
    : DeliveryTrace.decodeUpdates false [] [(path, 0)]
        [
          { incremental := [.list "stream" [.null]], hasNext := true },
          { pending := [stream], hasNext := false }
        ]
      = none :=
  rfl

/-- Object payloads can seed list cursors before the stream ID is announced. -/
def deferredList : QueryResult :=
  .incremental { data := .object [], pending := [root], hasNext := true }
    [
      {
        incremental := [.object "root" [("items", .list [.scalar "first"])]],
        completed := [{ id := "root" }],
        hasNext := true
      },
      {
        pending := [stream],
        incremental := [.list "stream" [.scalar "same", .scalar "same"]],
        completed := [{ id := "stream" }],
        hasNext := false
      }
    ]

/-- Initial, object, and stream slices retain their boundaries and exact append indices. -/
example
    : deferredList.decodeSlices false
      = some [[], [path ++ [.index 0]], [path ++ [.index 1], path ++ [.index 2]]] :=
  rfl

/-- Container mode additionally includes the initial root and the introduced list root. -/
example
    : deferredList.decodeSlices true
      = some
          [[[]], [path, path ++ [.index 0]], [path ++ [.index 1], path ++ [.index 2]]] :=
  rfl

/-- Within one update, an object can seed a list before a subsequent stream payload. -/
example
    : DeliveryTrace.decodePatches false [root, stream] []
        [.object "root" [("items", .list [])], .list "stream" [.null]]
      = some ([[], [path ++ [.index 0]]], [(path, 1), (path, 0)]) :=
  rfl

/-- Reversing those payloads fails: later data cannot seed an earlier stream cursor. -/
example
    : DeliveryTrace.decodePatches false [root, stream] []
        [.list "stream" [.null], .object "root" [("items", .list [])]]
      = none :=
  rfl

/-- Control-only responses create no payload slices and leave cursor state unchanged. -/
example (containers : Bool) (notices : List IncrementalPendingNotice)
    (cursors : ResponsePositions.Cursors)
    : DeliveryTrace.decodeUpdates containers notices cursors [{ hasNext := false }]
      = some ([], cursors) :=
  rfl

/-- Raw wire paths can decode even when their announced parent cannot be merged. -/
def unattached : QueryResult :=
  .incremental
    {
      data := .null
      pending := [{ id := "d", path := [.field "missing"] }]
      hasNext := true
    }
    [{
      incremental := [.object "d" [("x", .null)]],
      completed := [{ id := "d" }],
      hasNext := false
    }]

/-- Decoding does not assume parent attachment or inspect response data shapes. -/
example : unattached.DeliversSlices false [[[]], [[.field "missing", .field "x"]]] :=
  rfl

/-- The same raw trace has a valid lifecycle but fails the independent data merger. -/
example : unattached.deliveryComplete = true ∧ mergeQueryResult unattached = none :=
  ⟨rfl, rfl⟩

/-- An interrupted observation can still have decoded slices despite incomplete delivery. -/
example
    : (QueryResult.incremental
        { data := .null, pending := [], hasNext := true } []).decodeSlices
        false
      = some [[[]]] :=
  rfl

end GraphQL.IncrementalDelivery.Tests.PositionDecoding
