import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.DrainFailureCut

/-! The successful task's single-pass contributor fold supplies the exact starting
evidence for mixed-drain cuts and cannot discard a buffer whose contributors do not publish.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode GroupNode)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode WorkQueueEvent)

private abbrev Kernel := ReferenceWorkQueue.State
private abbrev Accumulator := Kernel × List WorkQueueEvent × ReferenceWorkQueue.NewWork

-----------------------------------------------------------------------------------------
-- Counter changes preserve the generated proof-side frame
-----------------------------------------------------------------------------------------

/-- A looked-up contributor's counter decrement changes neither its tasks nor ownership. -/
theorem SnapshotTaskEvidence.putPending {queue : Kernel} {work key node}
    (frame : SnapshotTaskEvidence queue work) (found : queue.groupNode? key = some node)
    (pending : Nat)
    : SnapshotTaskEvidence (queue.putGroupNode { node with pending }) work := by
  have member := List.mem_of_find?_eq_some found
  exact { frame with
    keys := frame.keys.putGroupNode _,
    live := frame.live.putGroupNode _ (frame.live node member),
    buffered := frame.buffered.putGroupNodeSameTasks frame.keys node member _ rfl rfl,
    sound := frame.sound.putGroupNode _ (frame.sound node member) }

-----------------------------------------------------------------------------------------
-- The actual contributor fold constructs the drain's registration and retirement evidence
-----------------------------------------------------------------------------------------

/-- The success fold preserves registration and the removal forest, projects surviving
edges to its exact starting queue, and accounts for all its actual closure output. These
are constructed together on one fold, not assumed at the mixed-drain boundary.
-/
theorem successGroupFold_releaseEvidence {queue : Kernel} {work parents}
    (frame : SnapshotTaskEvidence queue work) (forest : queue.RemovalForest parents)
    (groups : List DeliveryNode)
    : let folded := groups.foldl ReferenceWorkQueue.successGroupStep (queue, [], {})
      SnapshotTaskEvidence folded.1 work
      ∧ folded.1.RemovalForest parents
      ∧ folded.1.GroupEdgesFrom queue
      ∧ ReferenceWorkQueue.GroupClosureAccounting queue (folded.1, folded.2.1) := by
  have loop (more : List DeliveryNode) (acc : Accumulator)
      (frame : SnapshotTaskEvidence acc.1 work) (forest : acc.1.RemovalForest parents)
      (edges : acc.1.GroupEdgesFrom queue)
      (closures : ReferenceWorkQueue.GroupClosureAccounting queue (acc.1, acc.2.1))
      : let folded := more.foldl ReferenceWorkQueue.successGroupStep acc
        SnapshotTaskEvidence folded.1 work
          ∧ folded.1.RemovalForest parents
          ∧ folded.1.GroupEdgesFrom queue
          ∧ ReferenceWorkQueue.GroupClosureAccounting queue (folded.1, folded.2.1) := by
    induction more generalizing acc with
    | nil => exact ⟨frame, forest, edges, closures⟩
    | cons group rest ih =>
        obtain ⟨current, events, released⟩ := acc
        dsimp only [List.foldl_cons, ReferenceWorkQueue.successGroupStep]
        split
        · exact ih _ frame forest edges closures
        · rename_i node found
          let updated := { node with pending := node.pending - 1 }
          have updatedFrame := frame.putPending found updated.pending
          have updatedForest := forest.putCounters frame.keys found updated.pending node.failure
          have updatedEdges := (ReferenceWorkQueue.State.putPending_groupEdgesFrom frame.keys
            found updated.pending).trans edges
          have updatedClosures := closures.post (fun _ retired => retired.putGroupNode updated)
          split
          · have member : updated ∈ (current.putGroupNode updated).groupNodes := by
              apply List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found, ?_⟩
              simp [updated]
            exact ih _ (updatedFrame.finishGroupSuccess updated)
              (updatedForest.finishGroupSuccess updated)
              (((current.putGroupNode updated).finishGroupSuccess_descendants updated).1.trans updatedEdges)
              (updatedClosures.append
                (ReferenceWorkQueue.State.finishGroupSuccess_closureAccounting
                  updatedFrame.live updated member))
          · exact ih _ updatedFrame updatedForest updatedEdges updatedClosures
  exact loop groups _ frame forest (.refl queue)
    (.silent (fun _ retired => retired))

-----------------------------------------------------------------------------------------
-- An unpublished buffered occurrence and each live owner survive the complete success fold
-----------------------------------------------------------------------------------------

private theorem successGroupFold_publicationRoots_retains (groups : List DeliveryNode)
    (acc : Accumulator)
    : (publicationRoots acc.2.1).Subset
        (publicationRoots
          (groups.foldl ReferenceWorkQueue.successGroupStep acc).2.1) := by
  induction groups generalizing acc with
  | nil => exact List.Subset.refl _
  | cons group rest ih =>
      obtain ⟨current, events, released⟩ := acc
      dsimp only [List.foldl_cons, ReferenceWorkQueue.successGroupStep]
      split
      · exact ih (current, events, released)
      · rename_i node found
        split
        · intro key published
          apply ih _
          rw [publicationRoots, List.filterMap_append]
          exact List.mem_append_left _ published
        · exact ih (current.putGroupNode { node with pending := node.pending - 1 }, events, released)

private theorem flushKey (queue : Kernel) (node : GroupNode)
    : node.group.node.ref ∈ publicationRoots (queue.finishGroupSuccess node).2.1 := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output]
  split <;> simp [publicationRoots]

/-- Without a successful contributing key in the fold's actual output, a stored task and
every initially live contributor remain. Sound memberships exclude selecting the buffer;
its links prevent successful child-shell pruning, including latent failed contributors.
-/
theorem successGroupFold_pendingBuffer_retained {queue : Kernel} {work occurrence node}
    (frame : SnapshotTaskEvidence queue work) (groups : List DeliveryNode)
    (found : queue.taskNode? occurrence = some node) (stored : node.value.isSome = true)
    (unpublished
      : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
          key
          ∉ publicationRoots
              (groups.foldl ReferenceWorkQueue.successGroupStep (queue, [], {})).2.1)
    : let folded := groups.foldl ReferenceWorkQueue.successGroupStep (queue, [], {})
      folded.1.taskNode? occurrence = some node
      ∧ ∀ key ∈ node.task.groups.map DeliveryNode.ref,
          key ∈ queue.groupNodes.map (fun group => group.group.node.ref)
          → key ∈ folded.1.groupNodes.map (fun group => group.group.node.ref) := by
  have loop (more : List DeliveryNode) (acc : Accumulator)
      (frame : SnapshotTaskEvidence acc.1 work) (found : acc.1.taskNode? occurrence = some node)
      (unpublished
        : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
            key ∉ publicationRoots (more.foldl ReferenceWorkQueue.successGroupStep acc).2.1)
      : let folded := more.foldl ReferenceWorkQueue.successGroupStep acc
        folded.1.taskNode? occurrence = some node
          ∧ ∀ key ∈ node.task.groups.map DeliveryNode.ref,
              key ∈ acc.1.groupNodes.map (fun group => group.group.node.ref)
              → key ∈ folded.1.groupNodes.map (fun group => group.group.node.ref) := by
    induction more generalizing acc with
    | nil => exact ⟨found, fun _ _ present => present⟩
    | cons group rest ih =>
        obtain ⟨current, events, released⟩ := acc
        dsimp only [List.foldl_cons, ReferenceWorkQueue.successGroupStep] at unpublished ⊢
        split at unpublished
        · rename_i absent
          exact ih _ frame found unpublished
        · rename_i closing live
          let updated := { closing with pending := closing.pending - 1 }
          have updatedFrame := frame.putPending live updated.pending
          split at unpublished
          · rename_i ready
            simp only [ready, ↓reduceIte]
            let flushed := (current.putGroupNode updated).finishGroupSuccess updated
            let next : Accumulator :=
              (flushed.1, events ++ flushed.2.1,
                ⟨released.newGroups ++ flushed.2.2.newGroups,
                  released.newStreams ++ flushed.2.2.newStreams⟩)
            have noncontributor : updated.group.node.ref ∉ node.task.groups.map DeliveryNode.ref := by
              intro contributes
              apply unpublished _ contributes
              apply successGroupFold_publicationRoots_retains rest next
              rw [publicationRoots, List.filterMap_append]
              exact List.mem_append_right _ (flushKey _ updated)
            have member : updated ∈ (current.putGroupNode updated).groupNodes := by
              apply List.mem_map.mpr ⟨closing, List.mem_of_find?_eq_some live, ?_⟩
              simp [updated]
            obtain ⟨retained, owners⟩ := successfulFlush_noncontributorBuffer updatedFrame
              updated member found stored noncontributor
            obtain ⟨later, finalOwners⟩ := ih next (updatedFrame.finishGroupSuccess updated)
              retained unpublished
            refine ⟨later, ?_⟩
            intro key contributes present
            apply finalOwners key contributes
            apply owners key contributes
            rwa [ReferenceWorkQueue.State.putGroupNode_refs]
          · rename_i notReady
            simp only [notReady]
            obtain ⟨retained, owners⟩ := ih (current.putGroupNode updated, events, released)
              updatedFrame found unpublished
            refine ⟨retained, ?_⟩
            intro key contributes present
            apply owners key contributes
            rwa [ReferenceWorkQueue.State.putGroupNode_refs]
  exact loop groups _ frame found unpublished

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
