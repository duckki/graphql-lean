import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeReannouncement

/-! Actual owner passes and drains cannot reannounce an ancestor-protected group. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every single-pass owner step preserves protection and excludes an old protected ref
-----------------------------------------------------------------------------------------

/-- One owner step keeps the frame and cannot append a notice for a protected ref.
Witness: a counter update preserves live metadata. A successful branch has a supported
active owner, so its release frontier excludes the ref; permanent retirement preserves
that protection for every later step, even before pending releases are activated.
-/
theorem LiveRootFrame.successGroupStep_noProtectedNotice
    {acc : State × List WorkQueueEvent × NewWork} {work parents ref}
    (frame : LiveRootFrame acc.1 work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (protectedRef : acc.1.AncestorsRetired work ref)
    (absent : ref ∉ acc.2.1.flatMap rawGroupNoticeRefs) (group : Execution.DeliveryNode)
    : LiveRootFrame (successGroupStep acc group).1 work parents
      ∧ (successGroupStep acc group).1.AncestorsRetired work ref
      ∧ ref ∉ (successGroupStep acc group).2.1.flatMap rawGroupNoticeRefs := by
  obtain ⟨queue, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨frame, protectedRef, absent⟩
  · rename_i node found
    let updated := { node with pending := node.pending - 1 }
    let next := queue.putGroupNode updated
    have member := List.mem_of_find?_eq_some found
    have roots : next.RootAncestorsRetired work := frame.roots.mono (fun _ active => active)
      (fun _ retired => retired.putGroupNode updated)
    have present : next.RootGroupsPresent := by
      intro ref active
      rw [State.putGroupNode_refs]
      exact frame.present ref active
    have nextFrame : LiveRootFrame next work parents :=
      ⟨frame.refs.putGroupNode updated,
        frame.records.putGroupNode updated (frame.records node member),
        frame.links.putGroupNode updated (frame.links node member),
        frame.registered.putGroupNode updated (frame.registered node member),
        frame.tasks, roots,
        frame.support.putGroupNode updated (frame.support.contents node member), present⟩
    have nextProtected : next.AncestorsRetired work ref := protectedRef.mono
      (fun _ retired => retired.putGroupNode updated)
    split
    · rename_i finishes
      have active : updated.group.node.ref ∈ next.rootGroups := by
        have flags := Bool.and_eq_true_iff.mp finishes
        have refEq := State.groupNode?_ref found
        simpa only [updated, refEq, List.contains_iff_mem]
          using (Bool.and_eq_true_iff.mp flags.1).1
      have updatedMember : updated ∈ next.groupNodes := by
        exact List.mem_map.mpr ⟨node, member, by simp [updated]⟩
      have lookup := nextFrame.refs.groupNode?_of_mem updatedMember
      refine ⟨nextFrame.finishGroupSuccess_unactivated generated canonical lookup active,
        nextProtected.mono (fun _ retired => retired.finishGroupSuccess updated), ?_⟩
      rw [List.flatMap_append, List.mem_append, not_or]
      exact ⟨absent, nextFrame.finishGroupSuccess_noProtectedNotice generated canonical
        lookup active nextProtected⟩
    · exact ⟨nextFrame, nextProtected, absent⟩

/-- An entire owner fold emits no notice for any group protected at its entry.
Witness: iterate the exact single-pass step, preserving both permanent ancestry and
the accumulating output exclusion. No owner ordering or distinct-value premise is used.
-/
theorem LiveRootFrame.successGroupFold_noProtectedNotice {queue work parents ref}
    (frame : LiveRootFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (protectedRef : queue.AncestorsRetired work ref)
    (owners : List Execution.DeliveryNode)
    : let folded := owners.foldl successGroupStep (queue, [], {})
      LiveRootFrame folded.1 work parents
      ∧ folded.1.AncestorsRetired work ref
      ∧ ref ∉ folded.2.1.flatMap rawGroupNoticeRefs := by
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (current : LiveRootFrame acc.1 work parents)
      (protectedRef : acc.1.AncestorsRetired work ref)
      (absent : ref ∉ acc.2.1.flatMap rawGroupNoticeRefs)
      : let folded := more.foldl successGroupStep acc
        LiveRootFrame folded.1 work parents
        ∧ folded.1.AncestorsRetired work ref
        ∧ ref ∉ folded.2.1.flatMap rawGroupNoticeRefs := by
    induction more generalizing acc with
    | nil => exact ⟨current, protectedRef, absent⟩
    | cons owner rest ih =>
        obtain ⟨next, preserved, excluded⟩ := current.successGroupStep_noProtectedNotice
          generated canonical protectedRef absent owner
        exact ih (successGroupStep acc owner) next preserved excluded
  exact loop owners (queue, [], {}) frame protectedRef (by simp)

-----------------------------------------------------------------------------------------
-- Recursive release uses the same exclusion after earlier success or failure cleanup
-----------------------------------------------------------------------------------------

/-- A recursive drain cannot announce a group whose ancestors were already protected.
Witness: each actual selected successful flush excludes that ref and preserves its
protection; failure cleanup emits no notices and cannot undo retirement. The result holds
at every bounded drain prefix, including prefixes after cached-error closures.
-/
theorem LiveRootFrame.drainReadyGroups_go_noProtectedNotice
    {queue work parents ref} (frame : LiveRootFrame queue work parents)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (protectedRef : queue.AncestorsRetired work ref) (fuel : Nat)
    : ref ∉ (State.drainReadyGroups.go fuel queue).2.flatMap rawGroupNoticeRefs := by
  induction fuel generalizing queue with
  | zero => simp [State.drainReadyGroups.go]
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · simp
      · rename_i node selected
        obtain ⟨selectedRef, active, choice⟩ := List.exists_of_findSome?_eq_some selected
        cases found : queue.groupNode? selectedRef with
        | none => simp [found] at choice
        | some candidate =>
            simp only [found] at choice
            change (if candidate.failure.isSome || candidate.pending == 0 then
              some candidate else none) = some node at choice
            split at choice
            · cases Option.some.inj choice
              have same := State.groupNode?_ref found
              cases cached : node.failure with
              | none =>
                  rw [List.flatMap_append, List.mem_append, not_or]
                  exact ⟨frame.finishGroupSuccess_noProtectedNotice generated canonical
                    (same ▸ found) (same ▸ active) protectedRef,
                    ih (frame.finishGroupSuccess generated canonical
                      (same ▸ found) (same ▸ active))
                      (protectedRef.mono (fun _ retired =>
                        (retired.finishGroupSuccess node).startNewWork _))⟩
              | some errors =>
                  exact ih (frame.removeGroup node.group.node.ref)
                    (protectedRef.mono (fun _ retired => retired.removeGroup node.group.node.ref))
            · contradiction

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
