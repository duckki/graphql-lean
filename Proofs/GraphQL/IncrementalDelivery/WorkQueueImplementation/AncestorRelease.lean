import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplay

/-! Retired ancestry survives successful and cached-failure release-time draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Activation carries old and newly released ancestor certificates
-----------------------------------------------------------------------------------------

/-- Activating work preserves retired ancestors for old and newly announced roots.
Witness: the root list is the old roots followed by the released groups; activation
changes neither permanent registration nor the live group map.
-/
theorem State.RootAncestorsRetired.startNewWork {queue : State} {work}
    (prior : queue.RootAncestorsRetired work) (released : NewWork)
    (protectedGroups
      : ∀ group ∈ released.newGroups, queue.AncestorsRetired work group.ref)
    : (queue.startNewWork released).RootAncestorsRetired work := by
  intro ref active
  rw [(queue.startNewWork_groupCore released).2.2] at active
  rcases List.mem_append.mp active with old | new
  · exact (prior ref old).mono (fun ref retired => retired.startNewWork released)
  · obtain ⟨node, member, same⟩ := List.mem_map.mp new
    exact same ▸ (protectedGroups node member).mono
      (fun ref retired => retired.startNewWork released)

-----------------------------------------------------------------------------------------
-- Recursive draining needs cache provenance, not health of every active root
-----------------------------------------------------------------------------------------

/-- Draining preserves protected roots and ancestor-closed healthy retirement together.
Witness: successful release protects promoted children before activation; a supported
cached failure removes only invalidated nodes, retaining every healthy retirement
certificate. The executable drain may encounter transient failed active roots.
These are internal state invariants, not extra source or conformance premises.
-/
theorem State.drainReadyGroups_retirement {queue : State} {work parents failed}
    (roots : queue.RootAncestorsRetired work)
    (retirement : queue.HealthyRetiredAncestors work failed)
    (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (supported : queue.CachedFailuresSupported work failed)
    : queue.drainReadyGroups.1.RootAncestorsRetired work
      ∧ queue.drainReadyGroups.1.HealthyRetiredAncestors work failed := by
  let invariant (current : State) :=
    current.RootAncestorsRetired work
    ∧ current.HealthyRetiredAncestors work failed
    ∧ current.GroupNodesMatchWork work
    ∧ current.ChildLinksCanonical parents
    ∧ current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered
    ∧ current.CachedFailuresSupported work failed
  have final := State.drainReadyGroups_preserves invariant (by
    intro current node valid member active _ _
    obtain ⟨oldRoots, closure, matched, linked, recorded, covered, caches⟩ := valid
    have closed := State.finishGroupSuccess_retirement (failed := failed)
      generated matched linked canonical recorded member (oldRoots _ active)
    have coveredNext := current.finishGroupSuccess_registration recorded covered node
    have activated := State.startNewWork_registration coveredNext.1 coveredNext.2.1
      (current.finishGroupSuccess node).2.2
    have survivingRoots := oldRoots.mono (current.finishGroupSuccess_rootsSubset node)
      (fun ref retired => retired.finishGroupSuccess node)
    exact ⟨
      survivingRoots.startNewWork _ closed.2.2.1,
      (closed.2.2.2 closure).startNewWork _,
      (matched.finishGroupSuccess node).startNewWork _,
      (linked.finishGroupSuccess node).startNewWork _,
      activated.1,
      activated.2,
      (caches.finishGroupSuccess node).startNewWork _
    ⟩) (by
    intro current node errors valid member _ cached
    obtain ⟨oldRoots, closure, matched, linked, recorded, covered, caches⟩ := valid
    have invalid := caches.invalidated member (by simp [cached])
    exact ⟨
      oldRoots.mono (current.removeGroup_rootsSubset node.group.node.ref)
        (fun ref retired => retired.removeGroup node.group.node.ref),
      closure.removeGroup linked matched canonical _ invalid.toRecordInvalidated,
      matched.removeGroup _,
      linked.removeGroup _,
      fun other member => recorded other (List.mem_filter.mp member).1,
      covered,
      caches.removeGroup _
    ⟩) ⟨roots, retirement, matching, links, registered, tasks, supported⟩
  exact ⟨final.1, final.2.1⟩

-----------------------------------------------------------------------------------------
-- Retired ancestry closes the object-task availability obligation locally
-----------------------------------------------------------------------------------------

/-- An accepted fresh object settlement has available child contributors under retirement
closure. Witness: the started task is permanently registered, source freshness excludes
earlier settlement, and healthy owner/count projections give the live-producer argument.
Retirement closure remains an internal invariant to derive through full replay.
-/
theorem State.OwnerAccounting.taskSuccess_available {queue : State}
    {work parents before occurrence result}
    (accounting : queue.OwnerAccounting work parents before)
    (generated : ExecutedWork work)
    (closure : queue.HealthyRetiredAncestors work (GraphEvent.failureSettlements before))
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (accepted : queue.acceptsGraphEvent (.taskSuccess occurrence result) = true)
    : queue.ChildGroupsAvailable work (GraphEvent.failureSettlements before)
        result.work := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.acceptsGraphEvent, found] at accepted
  | some node =>
      have registered := accounting.pending.started node (List.mem_of_find?_eq_some found)
      have same : node.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun candidate : TaskNode =>
          candidate.task.occurrence == occurrence) found)
      apply closure.childGroupsAvailable accounting.healthyRegisteredTasks
        (accounting.pending.healthyPendingTracks accounting.healthy)
        accounting.pending.matching generated registered
      · rw [same]
        exact fun member => fresh.2.2.1 occurrence List.mem_cons_self
          (GraphEvent.groupSettlements_subsetIdentities before member)
      · simpa only [same] using matching

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
