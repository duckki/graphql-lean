import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFrontierUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeSourceFreshness

/-! Each group-success carrier has a duplicate-free list of announced group refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Release-list uniqueness is exactly uniqueness of the successful carrier's notices
-----------------------------------------------------------------------------------------

/-- Every event emitted by a successful flush has unique group-notice refs.
Witness: its optional value event has no notices; the control copies its unique pruned frontier.
-/
theorem State.finishGroupSuccess_groupNoticesUnique {queue : State} {parents}
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    {group : GroupNode} (present : group ∈ queue.groupNodes)
    : ∀ event ∈ (queue.finishGroupSuccess group).2.1,
        (rawGroupNoticeRefs event).Nodup := by
  have unique := queue.finishGroupSuccess_newGroups_unique links children present
  obtain ⟨values, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications group
  intro event emitted
  rw [output] at emitted
  rcases List.mem_append.mp emitted with value | control
  · split at value
    · cases value
    · obtain rfl := List.mem_singleton.mp value
      exact List.nodup_nil
  · obtain rfl := List.mem_singleton.mp control
    exact unique

-----------------------------------------------------------------------------------------
-- Owner iteration retains the structural metadata needed by every later flush
-----------------------------------------------------------------------------------------

/-- Each owner step preserves canonical unique child links and unique carried notice lists.
Witness: counter updates change no links, and a successful branch flushes a live record
whose actual pruned frontier is unique. Accumulated releases need not yet be activated.
-/
theorem successGroupStep_groupNoticesUnique
    {acc : State × List WorkQueueEvent × NewWork} {parents}
    (links : acc.1.ChildLinksCanonical parents) (children : acc.1.ChildGroupsUnique)
    (notices : ∀ event ∈ acc.2.1, (rawGroupNoticeRefs event).Nodup)
    (owner : Execution.DeliveryNode)
    : (successGroupStep acc owner).1.ChildLinksCanonical parents
      ∧ (successGroupStep acc owner).1.ChildGroupsUnique
      ∧ ∀ event ∈ (successGroupStep acc owner).2.1, (rawGroupNoticeRefs event).Nodup := by
  obtain ⟨queue, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨links, children, notices⟩
  · rename_i node found
    let updated := { node with pending := node.pending - 1 }
    let next := queue.putGroupNode updated
    have present := List.mem_of_find?_eq_some found
    have nextLinks : next.ChildLinksCanonical parents :=
      links.putGroupNode updated (links node present)
    have nextChildren : next.ChildGroupsUnique :=
      children.putGroupNode updated (children node present)
    split
    · have member : updated ∈ next.groupNodes :=
        List.mem_map.mpr ⟨node, present, by simp [updated]⟩
      refine ⟨nextLinks.finishGroupSuccess updated, nextChildren.finishGroupSuccess updated, ?_⟩
      intro event emitted
      rcases List.mem_append.mp emitted with old | new
      · exact notices event old
      · exact next.finishGroupSuccess_groupNoticesUnique nextLinks nextChildren member event new
    · exact ⟨nextLinks, nextChildren, notices⟩

/-- Every carrier in the full single-pass owner fold has unique group-notice refs.
Witness: induction through the literal owner step preserves its structural metadata.
-/
theorem State.successGroupFold_groupNoticesUnique {queue : State} {parents}
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    (owners : List Execution.DeliveryNode)
    : let folded := owners.foldl successGroupStep (queue, [], {})
      folded.1.ChildLinksCanonical parents
      ∧ folded.1.ChildGroupsUnique
      ∧ ∀ event ∈ folded.2.1, (rawGroupNoticeRefs event).Nodup := by
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (links : acc.1.ChildLinksCanonical parents) (children : acc.1.ChildGroupsUnique)
      (notices : ∀ event ∈ acc.2.1, (rawGroupNoticeRefs event).Nodup)
      : (more.foldl successGroupStep acc).1.ChildLinksCanonical parents
        ∧ (more.foldl successGroupStep acc).1.ChildGroupsUnique
        ∧ ∀ event ∈ (more.foldl successGroupStep acc).2.1,
            (rawGroupNoticeRefs event).Nodup := by
    induction more generalizing acc with
    | nil => exact ⟨links, children, notices⟩
    | cons owner rest ih =>
        obtain ⟨nextLinks, nextChildren, nextNotices⟩ :=
          successGroupStep_groupNoticesUnique links children notices owner
        exact ih _ nextLinks nextChildren nextNotices
  exact loop owners (queue, [], {}) links children (by simp)

-----------------------------------------------------------------------------------------
-- Recursive draining adds only fresh-frontier success controls or notice-free failures
-----------------------------------------------------------------------------------------

/-- Every group-notice list emitted by a bounded drain is duplicate-free.
Witness: invert its real ready-node lookup; each successful flush starts from a live
record and preserves the structural facts through activation, while failure only removes.
-/
theorem State.drainReadyGroups_go_groupNoticesUnique {queue : State} {parents}
    (links : queue.ChildLinksCanonical parents) (children : queue.ChildGroupsUnique)
    (fuel : Nat)
    : ∀ event ∈ (State.drainReadyGroups.go fuel queue).2,
        (rawGroupNoticeRefs event).Nodup := by
  induction fuel generalizing queue with
  | zero => simp [State.drainReadyGroups.go]
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · simp
      · rename_i node selected
        obtain ⟨ref, _, choice⟩ := List.exists_of_findSome?_eq_some selected
        cases found : queue.groupNode? ref with
        | none => simp [found] at choice
        | some candidate =>
            simp only [found] at choice
            change (if candidate.failure.isSome || candidate.pending == 0 then
              some candidate else none) = some node at choice
            split at choice
            · cases Option.some.inj choice
              cases cached : node.failure with
              | none =>
                  intro event emitted
                  rcases List.mem_append.mp emitted with first | later
                  · exact queue.finishGroupSuccess_groupNoticesUnique links children
                      (List.mem_of_find?_eq_some found) event first
                  · exact ih ((links.finishGroupSuccess node).startNewWork _)
                      ((children.finishGroupSuccess node).startNewWork _) event later
              | some errors =>
                  intro event emitted
                  rcases List.mem_cons.mp emitted with rfl | later
                  · exact List.nodup_nil
                  · exact ih (links.removeGroup _) (children.removeGroup _) event later
            · contradiction

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
