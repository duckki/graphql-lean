import Proofs.GraphQL.IncrementalDelivery.Correctness.NoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.Correctness.PatchPositions

/-! Exact source-path decoding under stable mapper IDs and observed list cursors. -/

namespace GraphQL.IncrementalDelivery.Tests.NoticeMetadata
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open MapperIdentity

def owner : DeliveryNode := { key := 7, path := [.field "viewer"], label := some .null }

def notice : IncrementalPendingNotice :=
  { id := "0", path := owner.path, label := owner.label }

def payload : GroupValue :=
  { path := [.field "viewer", .field "profile"], data := [("age", .scalar "42")] }

/-- The mapper can reference an ancestor owner while retaining the full source path;
witness: the decoder theorem and the exact two-segment subPath computation.
-/
example
    : DeliveryTrace.decodePatch true [notice] []
        ((getIncrementalEntry (m := StateM IDState) owner payload ensureID).run {}).1
      = some ([[.field "viewer", .field "profile", .field "age"]], []) := by
  apply getIncrementalEntry_positions owner payload {} (ensureID owner {}).2
    (fun _ => owner.path) [notice] [] true
  · exact .refl _
  · exact ensureID_allocated owner {} .empty
  · intro entry member
    have equal : entry = notice := by simpa using member
    subst entry
    exact ⟨7, (ensureID_spec owner {}).2, rfl⟩
  · rfl
  · exact ⟨[.field "profile"], rfl⟩
  · decide

/-- Stream offsets come from the current observed cursor, not from the numeric ID or
the directive's initialCount. Here the next delivered item starts at index seven.
-/
example
    : DeliveryTrace.decodePatch false [notice] [(owner.path, 7)]
        (.list "0" [.scalar "next"])
      = some ([[.field "viewer", .index 7]], [(owner.path, 8), (owner.path, 7)]) := by
  apply streamEntry_positions owner "0" [.scalar "next"] 0 (fun _ => owner.path)
    (ensureID owner {}).2 [notice] [(owner.path, 7)] 7 false
  · exact ensureID_allocated owner {} .empty
  · exact (ensureID_spec owner {}).2
  · intro entry member
    have equal : entry = notice := by simpa using member
    subst entry
    exact ⟨7, (ensureID_spec owner {}).2, rfl⟩
  · rfl
  · decide
  · decide

/-- The path bridge applies to every observation with generated-work metadata, not only
complete outcomes; its state contains only allocations from the supplied inputs.
-/
example {paths bound response work complete result}
    (observed : WorkObservation response work complete result)
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    : ∃ ids, Allocated ids ∧ NoticePaths paths ids (queryNotices result) :=
  observed.noticePaths coherent

end GraphQL.IncrementalDelivery.Tests.NoticeMetadata
