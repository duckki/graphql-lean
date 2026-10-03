import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRootCoverage

/-! Immediate stream registration gives fresh, internally unique notice refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The executable selection fold excludes every previously registered ref
-----------------------------------------------------------------------------------------

/-- The actual registration fold selects distinct refs absent from the old registry.
Witness: each append passes both the old-registry lookup and the selected-ref guard.
This holds for arbitrary raw states and duplicate incoming descriptors.
-/
theorem State.addStreams_selection_fresh (queue : State) (streams : List Stream)
    : let fresh :=
        streams.foldl
          (fun selected stream =>
            if (queue.stream? stream.node.ref).isSome
                || selected.any (fun known => known.node.ref == stream.node.ref) then
              selected
            else
              selected ++ [stream]) []
      (fresh.map (fun stream => stream.node.ref)).Nodup
      ∧ ∀ stream ∈ fresh,
          stream.node.ref ∉ queue.streams.map (fun old => old.node.ref) := by
  let step (selected : List Stream) (stream : Stream) :=
    if (queue.stream? stream.node.ref).isSome
        || selected.any (fun known => known.node.ref == stream.node.ref) then selected
    else selected ++ [stream]
  have loop (more selected : List Stream)
      (unique : (selected.map (fun stream => stream.node.ref)).Nodup)
      (absent : ∀ stream ∈ selected,
        stream.node.ref ∉ queue.streams.map (fun old => old.node.ref))
      : ((more.foldl step selected).map (fun stream => stream.node.ref)).Nodup
        ∧ ∀ stream ∈ more.foldl step selected,
            stream.node.ref ∉ queue.streams.map (fun old => old.node.ref) := by
    induction more generalizing selected with
    | nil => exact ⟨unique, absent⟩
    | cons stream rest ih =>
        rw [List.foldl_cons]
        unfold step
        split
        · exact ih _ unique absent
        · rename_i fresh
          have guards : (queue.stream? stream.node.ref).isSome = false
              ∧ (selected.any (fun known => known.node.ref == stream.node.ref)) = false := by
            simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true] using fresh
          have distinct : stream.node.ref ∉ selected.map (fun known => known.node.ref) := by
            intro member
            obtain ⟨old, included, same⟩ := List.mem_map.mp member
            have hit : selected.any (fun known => known.node.ref == stream.node.ref) = true :=
              List.any_eq_true.mpr ⟨old, included, by simp [same]⟩
            simp [guards.2] at hit
          have unregistered : stream.node.ref
              ∉ queue.streams.map (fun old => old.node.ref) := by
            intro member
            obtain ⟨old, included, same⟩ := List.mem_map.mp member
            have found : ∃ known, queue.stream? stream.node.ref = some known :=
              State.stream?_exists_of_registered
                (node := old.node) (List.mem_map.mpr ⟨old, included, rfl⟩) |>
                fun ⟨known, found⟩ => ⟨known, same ▸ found⟩
            obtain ⟨known, found⟩ := found
            simp [found] at guards
          refine ih _ ?_ ?_
          · rw [List.map_append]
            exact List.nodup_append.mpr ⟨unique, by simp, by
              intro old member next present same
              simp only [List.map_cons, List.map_nil, List.mem_singleton] at present
              exact distinct ((same.trans present) ▸ member)⟩
          · intro next member
            rcases List.mem_append.mp member with old | new
            · exact absent next old
            · exact List.mem_singleton.mp new ▸ unregistered
  exact loop streams [] (by simp) (by simp)

/-- Immediate stream notices have unique refs, none previously registered.
Witness: root registration returns the exact fresh selection; task attachment returns
no immediate notice. Existing registry uniqueness is not assumed.
-/
theorem State.addStreams_notices_fresh (queue : State) (streams : List Stream)
    (parent : Option Occurrence := none)
    : ((queue.addStreams streams parent).2.map Execution.DeliveryNode.ref).Nodup
      ∧ ∀ node ∈ (queue.addStreams streams parent).2,
          node.ref ∉ queue.streams.map (fun stream => stream.node.ref) := by
  have selected := queue.addStreams_selection_fresh streams
  unfold State.addStreams
  cases parent with
  | none =>
      refine ⟨?_, ?_⟩
      · simpa only [List.map_map, Function.comp_def] using selected.1
      · intro node member
        obtain ⟨stream, included, same⟩ := List.mem_map.mp member
        exact same ▸ selected.2 stream included
  | some occurrence =>
      dsimp only
      split <;> exact ⟨by simp, by intro node impossible; cases impossible⟩

/-- Full integration preserves immediate stream-notice freshness and ref uniqueness.
Witness: group/task registration leaves the stream registry unchanged before selection.
-/
theorem State.maybeIntegrateWork_streamNotices_fresh (queue : State) (work : Work)
    (parent : Option Occurrence := none)
    : ((queue.maybeIntegrateWork work parent).2.newStreams.map
        Execution.DeliveryNode.ref).Nodup
      ∧ ∀ node ∈ (queue.maybeIntegrateWork work parent).2.newStreams,
          node.ref ∉ queue.streams.map (fun stream => stream.node.ref) := by
  have fresh := State.addStreams_notices_fresh
    (work.tasks.foldl State.addTask (queue.addGroups work.groups).1) work.streams parent
  rw [fold_projection State.streams State.addTask State.addTask_streams,
    State.addGroups_streams] at fresh
  exact fresh

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
