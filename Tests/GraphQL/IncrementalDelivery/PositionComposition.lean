import Proofs.GraphQL.IncrementalDelivery.Correctness.PositionComposition
import Tests.GraphQL.IncrementalDelivery.PositionDecoding

/-! Decoder composition retains cursor state, causal notices, and failure behavior. -/

namespace GraphQL.IncrementalDelivery.Tests.PositionComposition
open GraphQL.IncrementalDelivery.Execution
open PositionDecoding

/-- The suffix can append only after the prefix introduces its list cursor; witness:
the general patch append law and concrete prefix/suffix decoding.
-/
example
    : DeliveryTrace.decodePatches false [root, stream] []
        ([.object "root" [("items", .list [])]] ++ [.list "stream" [.null]])
      = some ([[], [path ++ [.index 0]]], [(path, 1), (path, 0)]) := by
  apply DeliveryTrace.decodePatches_append_iff.mpr
  exact ⟨[[]], [(path, 0)], [[path ++ [.index 0]]], rfl, rfl, rfl⟩

/-- Prefix notices remain visible to the suffix; witness: the update append law with
an announcement-only prefix and a streamed payload suffix.
-/
example
    : DeliveryTrace.decodeUpdates false [] [(path, 2)]
        ([{ pending := [stream], hasNext := true }]
          ++ [{ incremental := [.list "stream" [.null]], hasNext := false }])
      = some ([[path ++ [.index 2]]], [(path, 3), (path, 2)]) := by
  apply DeliveryTrace.decodeUpdates_append_iff.mpr
  exact ⟨[], [(path, 2)], [[path ++ [.index 2]]], rfl, rfl, rfl⟩

/-- No suffix can repair a failed prefix; witness: the Option append equation.
-/
example (containers notices cursors left right)
    (failed : DeliveryTrace.decodeUpdates containers notices cursors left = none)
    : DeliveryTrace.decodeUpdates containers notices cursors (left ++ right) = none := by
  rw [DeliveryTrace.decodeUpdates_append, failed]
  rfl

/-- Successful whole-history decoding always exposes a successfully decoded prefix;
witness: append inversion, without a lifecycle or scheduler premise.
-/
example (containers notices cursors left right slices final)
    (decoded
      : DeliveryTrace.decodeUpdates containers notices cursors (left ++ right)
        = some (slices, final))
    : ∃ head middle,
        DeliveryTrace.decodeUpdates containers notices cursors left
        = some (head, middle) := by
  obtain ⟨head, middle, _, first, _, _⟩ := DeliveryTrace.decodeUpdates_append_iff.mp decoded
  exact ⟨head, middle, first⟩

end GraphQL.IncrementalDelivery.Tests.PositionComposition
