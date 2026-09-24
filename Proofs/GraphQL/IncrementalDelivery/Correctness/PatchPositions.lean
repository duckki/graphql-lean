import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperMetadata
import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamPositions

/-! Actual wire entries decode to their source attachment paths using stable notice IDs.
Stream offsets still require the independent cursor-history invariant.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- An announced ID has an actual matching notice; witness: membership excludes failed
lookup. No future notices are used.
-/
theorem notice_exists {notices : List IncrementalPendingNotice} {id : String}
    (announced : id ∈ notices.map IncrementalPendingNotice.id)
    : ∃ notice, notices.find? (fun notice => notice.id == id) = some notice := by
  cases found : notices.find? (fun notice => notice.id == id) with
  | none =>
      obtain ⟨notice, member, same⟩ := List.mem_map.mp announced
      have absent := List.find?_eq_none.mp found notice member
      exact False.elim (absent (by simp [same]))
  | some notice => exact ⟨notice, rfl⟩

/-- An object entry's real mapper ID resolves its original absolute field positions.
Witness: stable allocation, current notice metadata, and the source-owner path prefix.
The final ID state may include later allocations in the same response batch.
-/
theorem getIncrementalEntry_positions (node : DeliveryNode) (value : GroupValue)
    (ids final : IDState) (paths : Nat → ResponsePath)
    (notices : List IncrementalPendingNotice) (cursors : ResponsePositions.Cursors)
    (containers : Bool)
    (preserved : Preserves (ensureID node ids).2 final) (allocated : Allocated final)
    (metadata : NoticePaths paths final notices) (path : paths node.key = node.path)
    (ownerPrefix : Semantics.Below node.path value.path)
    (announced : (ensureID node ids).1 ∈ notices.map IncrementalPendingNotice.id)
    : DeliveryTrace.decodePatch containers notices cursors
        ((getIncrementalEntry (m := StateM IDState) node value ensureID).run ids).1
      = some
          (
            ResponsePositions.fields containers value.path value.data,
            ResponsePositions.fieldCursors value.path value.data ++ cursors
          ) := by
  obtain ⟨notice, found⟩ := notice_exists announced
  have known := preserved _ _ (ensureID_spec node ids).2
  have noticePath := metadata.lookup allocated known path found
  obtain ⟨suffix, equal⟩ := ownerPrefix
  have absolute : notice.path ++ value.path.drop node.path.length = value.path := by
    rw [noticePath, equal]
    simp
  have decoded := DeliveryTrace.decodePatch_object (containers := containers)
    (cursors := cursors) (data := value.data) (errors := value.errors)
    (subPath := value.path.drop node.path.length) found
  simpa only [getIncrementalEntry, StateT.run, StateT.bind, StateT.pure, bind, pure,
    absolute]
    using decoded

/-- A stream entry decodes at its source list's current cursor. Witness: stable-ID
metadata identifies the list path; the supplied cursor premise determines its next index.
This lemma does not assume or prove the scheduler-to-cursor invariant.
-/
theorem streamEntry_positions (node : DeliveryNode) (id : String)
    (values : List ResponseValue) (errors : Nat) (paths : Nat → ResponsePath)
    (ids : IDState) (notices : List IncrementalPendingNotice)
    (cursors : ResponsePositions.Cursors) (index : Nat) (containers : Bool)
    (allocated : Allocated ids) (known : Known ids node.key id)
    (metadata : NoticePaths paths ids notices) (path : paths node.key = node.path)
    (announced : id ∈ notices.map IncrementalPendingNotice.id)
    (cursor : ResponsePositions.cursorAt cursors node.path = some index)
    : DeliveryTrace.decodePatch containers notices cursors (.list id values errors)
      = some
          (
            ResponsePositions.items containers node.path index values,
            (node.path, index + values.length)
              :: ResponsePositions.itemCursors node.path index values
            ++ cursors
          ) := by
  obtain ⟨notice, found⟩ := notice_exists announced
  have noticePath := metadata.lookup allocated known path found
  have decoded := DeliveryTrace.decodePatch_list (containers := containers)
    (cursors := cursors) (data := values) (errors := errors)
    found (by simpa only [noticePath] using cursor)
  simpa only [noticePath] using decoded

end GraphQL.IncrementalDelivery.Correctness
