import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailurePathTransport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StartupFailureCut

/-! Queued startup failure paths survive publication filtering at the full handler boundary. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.Execution (DeliveryNode WorkQueueEvent)
private abbrev Kernel := ReferenceWorkQueue.State

/-- A queued startup failure path excludes all earlier and later successful carriers. -/
theorem startupFailureBoundary_path {before current : Kernel}
    {event parents earlier target} (roots : ReferenceWorkQueue.NewWork)
    (forest : current.RemovalForest parents)
    (edges : current.GroupEdgesFrom (registrationSnapshot before event))
    (closures
      : ReferenceWorkQueue.GroupClosureAccounting
          (registrationSnapshot before event) (current, earlier))
    (fuel : Nat) {failure : ReferenceWorkQueue.GroupFailureEvent}
    (queued : failure ∈ (current.startNewWork roots).2)
    (path : current.LiveDescendant failure.group.ref target)
    : (failurePruningView before event
        (earlier
          ++ (ReferenceWorkQueue.State.drainReadyGroups.go [] fuel
                (current.startNewWork roots).1).2.1)).LiveDescendant
        failure.group.ref target := by
  apply failurePruningView_pathFrom edges path
  intro key fromRoot toTarget published
  rw [publicationRoots, List.filterMap_append, List.mem_append] at published
  rcases published with old | later
  · obtain ⟨carrier, groups, streams, emitted, same⟩ := mem_publicationRoots.mp old
    have retired := (closures.closed key
      (List.mem_flatMap.mpr ⟨_, emitted, same ▸ List.mem_cons_self⟩)).lookup_none
    obtain ⟨node, found⟩ := toTarget.found
    rw [retired] at found
    contradiction
  · have live := drainReadyGroups_go_publicationRoots_live fuel
      (current.startNewWork roots).1 later
    obtain ⟨node, member, same⟩ := List.mem_map.mp live
    have absent := ReferenceWorkQueue.State.startNewWork_failedDescendant_absent
      forest roots [] queued fromRoot
    exact List.find?_eq_none.mp absent node member (by simp [same])

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
