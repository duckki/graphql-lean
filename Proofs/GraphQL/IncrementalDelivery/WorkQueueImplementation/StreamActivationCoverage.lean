import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAnnouncements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistry

/-! Every released registered stream is activated; activation never loses an existing root. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registry membership suffices for the executable start operation
-----------------------------------------------------------------------------------------

/-- A registered descriptor has a successful key lookup, even in a nonunique raw registry.
Witness: a failed list search would reject the supplied descriptor's own matching key.
-/
theorem State.stream?_exists_of_registered {queue : State} {node : Execution.DeliveryNode}
    (registered : node ∈ queue.streams.map Stream.node)
    : ∃ stream, queue.stream? node.key = some stream := by
  obtain ⟨stream, member, same⟩ := List.mem_map.mp registered
  cases found : queue.stream? node.key with
  | some chosen => exact ⟨chosen, rfl⟩
  | none =>
      have rejected := List.find?_eq_none.mp found stream member
      simp [same] at rejected

/-- Starting one stream retains the descriptor registry.
Witness: the only possible update appends an active-root key.
-/
theorem State.startStream_streams (queue : State) (key : Nat)
    : (queue.startStream key).streams = queue.streams := by
  unfold State.startStream
  split <;> rfl

/-- Starting a group retains the stream registry.
Witness: starting its tasks changes only task-node bookkeeping.
-/
theorem State.startGroup_streams (queue : State) (key : Nat)
    : (queue.startGroup key).streams = queue.streams := by
  have task : ∀ current occurrence,
      (State.startTask current occurrence).streams = current.streams := by
    intro current occurrence
    unfold State.startTask
    split
    · rfl
    · split <;> rfl
  unfold State.startGroup
  split
  · rfl
  · split
    · rfl
    · exact fold_projection State.streams State.startTask task _ _

/-- Starting a stream cannot remove an already active stream.
Witness: the concrete operation either keeps roots or appends one key.
-/
theorem State.startStream_rootStreams_mono (queue : State) (key : Nat)
    : queue.rootStreams.Subset (queue.startStream key).rootStreams := by
  unfold State.startStream
  split
  · exact List.Subset.refl _
  · exact List.subset_append_left _ _

/-- A registered stream is active after its start operation, including duplicate starts.
Witness: successful lookup excludes the missing-descriptor guard; an old root is retained
or the requested key is appended.
-/
theorem State.startStream_active {queue : State} {key : Nat}
    (registered : ∃ stream, queue.stream? key = some stream)
    : key ∈ (queue.startStream key).rootStreams := by
  obtain ⟨stream, found⟩ := registered
  simp only [State.startStream, found, Option.isNone_some, Bool.false_or]
  split
  · rename_i active
    exact List.contains_iff_mem.mp active
  · exact List.mem_append_right _ List.mem_cons_self

-----------------------------------------------------------------------------------------
-- Group activation and the stream-start fold cover every released stream
-----------------------------------------------------------------------------------------

/-- Activation keeps all old active streams and starts every registered released descriptor.
Witness: group starts leave both stream fields unchanged; the stream fold retains old keys
and starts each supplied registered key. No source or work-generation premise is needed.
-/
theorem State.startNewWork_streamRoots_cover (queue : State) (released : NewWork)
    (registered : released.newStreams.Subset (queue.streams.map Stream.node))
    : (queue.rootStreams ++ released.newStreams.map Execution.DeliveryNode.key).Subset
        (queue.startNewWork released).rootStreams := by
  have loop (keys : Keys) (current : State)
      (known : ∀ key ∈ keys, ∃ stream, current.stream? key = some stream)
      : (current.rootStreams ++ keys).Subset
          (keys.foldl State.startStream current).rootStreams := by
    induction keys generalizing current with
    | nil =>
        intro key member
        exact (List.mem_append.mp member).elim id (fun impossible => nomatch impossible)
    | cons key rest ih =>
        have later :=
          ih (current.startStream key)
            (by
              intro next member
              simpa only [State.stream?, State.startStream_streams]
                using known next (List.mem_cons_of_mem _ member))
        intro target member
        apply later
        rcases List.mem_append.mp member with old | pending
        · exact List.mem_append_left _ (current.startStream_rootStreams_mono key old)
        · rcases List.mem_cons.mp pending with same | next
          · exact List.mem_append_left _ (same.symm ▸ State.startStream_active
              (known key List.mem_cons_self))
          · exact List.mem_append_right _ next
  unfold State.startNewWork
  let groups := released.newGroups.map Execution.DeliveryNode.key
  let current := groups.foldl State.startGroup
    { queue with rootGroups := queue.rootGroups ++ groups }
  have streams : current.streams = queue.streams :=
    fold_projection State.streams State.startGroup State.startGroup_streams _ _
  have roots : current.rootStreams = queue.rootStreams :=
    fold_projection State.rootStreams State.startGroup State.startGroup_rootStreams _ _
  have included := loop (released.newStreams.map Execution.DeliveryNode.key) current (by
    intro key member
    obtain ⟨node, releasedNode, same⟩ := List.mem_map.mp member
    have present := registered releasedNode
    rw [← streams] at present
    exact same ▸ State.stream?_exists_of_registered present)
  simpa only [roots] using included

/-- Every group-flush stream notice names a descriptor retained in the resulting registry.
Witness: the release list is built from successful lookups, and flushing preserves streams.
-/
theorem State.finishGroupSuccess_streams_registered (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).2.2.newStreams.Subset
        ((queue.finishGroupSuccess group).1.streams.map Stream.node) := by
  rw [State.finishGroupSuccess_streams]
  exact (show queue.StreamsSatisfy (fun node => node ∈ queue.streams.map Stream.node) from
    fun _ member => List.mem_map_of_mem member).finishGroupSuccess_notices group

/-- A flush followed by activation covers its exact stream notices and all earlier roots.
Witness: every returned stream is registered and its release list equals its notice list.
-/
theorem State.finishGroupSuccess_streamRoots_cover (queue : State) (group : GroupNode)
    : (queue.rootStreams
        ++ (queue.finishGroupSuccess group).2.1.flatMap rawStreamNoticeKeys).Subset
        ((queue.finishGroupSuccess group).1.startNewWork
          (queue.finishGroupSuccess group).2.2).rootStreams := by
  have covered := (queue.finishGroupSuccess group).1.startNewWork_streamRoots_cover
    (queue.finishGroupSuccess group).2.2 (queue.finishGroupSuccess_streams_registered group)
  simpa only [State.finishGroupSuccess_rootStreams,
    State.finishGroupSuccess_streamNotices]
    using covered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
