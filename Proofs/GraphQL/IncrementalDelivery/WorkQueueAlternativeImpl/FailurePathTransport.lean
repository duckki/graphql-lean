import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PendingFailureCut
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainRootCoverage

/-! Failure-boundary paths survive the cleanup view's upfront successful-key exclusion.
Use the actual preceding retirement and remaining drain, not final-state absence alone.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.Execution (DeliveryNode WorkQueueEvent)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Transport only the live path's vertices through publication filtering
-----------------------------------------------------------------------------------------

/-- A later path projects into the exact cleanup view when its vertices have not published.
Edge provenance supplies their earlier lookups and identical children; task membership
changes do not affect the path. The avoidance premise covers this path interval, not all
ancestors of the target: already published ancestors above a failed root are allowed.
-/
theorem failurePruningView_pathFrom {before current : Kernel} {event events root target}
    (edges : current.GroupEdgesFrom (registrationSnapshot before event))
    (path : current.LiveDescendant root target)
    (avoids
      : ∀ key,
          current.LiveDescendant root key
          → current.LiveDescendant key target
          → key ∉ publicationRoots events)
    : (failurePruningView before event events).LiveDescendant root target := by
  induction path with
  | self found =>
      obtain ⟨old, earlier, _⟩ := edges _ _ found
      exact .self (failurePruningView_lookup earlier (avoids _ (.self found) (.self found)))
  | @child key node child target found linked below ih =>
      obtain ⟨old, earlier, children⟩ := edges key node found
      apply ReferenceWorkQueue.State.LiveDescendant.child
        (failurePruningView_lookup earlier (avoids key (.self found) (.child found linked below)))
      · exact children ▸ linked
      · exact ih (fun vertex first second => avoids vertex (.child found linked first) second)

-----------------------------------------------------------------------------------------
-- An actual failed subtree cannot contain any subsequent successful carrier
-----------------------------------------------------------------------------------------

/-- Every failure-subtree vertex is absent before the remaining actual mixed drain.
Since later success carriers come from that boundary's live keys, none can be a vertex
of the just-removed subtree. This holds for any remaining drain budget.
-/
theorem failurePath_unpublishedLater {current : Kernel} {parents root key}
    (forest : current.RemovalForest parents) (path : current.LiveDescendant root key)
    (fuel : Nat)
    : key
      ∉ publicationRoots
          (ReferenceWorkQueue.State.drainReadyGroups.go fuel
            (current.removeGroup root)).2 := by
  intro published
  have live := drainReadyGroups_go_publicationRoots_live fuel (current.removeGroup root) published
  obtain ⟨node, member, same⟩ := List.mem_map.mp live
  have absent := (ReferenceWorkQueue.State.removeGroup_liveDescendant_absent forest path).1
  exact (List.find?_eq_none.mp absent node member) (by simp [same])

/-- An actual failure-boundary path survives upfront exclusion of all successful carriers.
Earlier carriers have already retired from this same boundary; the failed subtree cannot
publish during its actual remaining drain. Thus neither past nor future successful vertices
are silently assumed disjoint from the path. Parent success above this root is permitted.
-/
theorem failureBoundary_path {before current : Kernel} {event parents earlier target}
    (failed : DeliveryNode) (errors fuel : Nat)
    (forest : current.RemovalForest parents)
    (edges : current.GroupEdgesFrom (registrationSnapshot before event))
    (retired : ∀ key ∈ publicationRoots earlier, current.groupNode? key = none)
    (path : current.LiveDescendant failed.ref target)
    : (failurePruningView before event
        (earlier
          ++ [.groupFailure failed errors]
          ++ (ReferenceWorkQueue.State.drainReadyGroups.go fuel
                (current.removeGroup failed.ref)).2)).LiveDescendant
        failed.ref target := by
  apply failurePruningView_pathFrom edges path
  intro key fromRoot toTarget published
  have split : key ∈ publicationRoots earlier
      ∨ key ∈ publicationRoots
        (ReferenceWorkQueue.State.drainReadyGroups.go fuel (current.removeGroup failed.ref)).2 := by
    simpa only [publicationRoots, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.nil_append, List.append_nil, List.mem_append]
      using published
  rcases split with old | later
  · obtain ⟨node, found⟩ := toTarget.found
    rw [retired key old] at found
    contradiction
  · exact failurePath_unpublishedLater forest fromRoot fuel later

-----------------------------------------------------------------------------------------
-- The actual bounded drain derives its own preceding retirement and topology evidence
-----------------------------------------------------------------------------------------

/-- A real failure at any drain prefix has its path in the full publication-filtered view.
The initial closure certificate may contain preceding contributor successes. Its retirement
is transported through the actual prefix, whose own closure accounting supplies every
additional retirement. The forest and edge evidence likewise follow the exact drain prefix;
no caller supplies a disjointness, path-avoidance, or preceding-key absence premise.
-/
theorem drainFailureBoundary_path {before initial : Kernel}
    {event parents preceding target}
    (forest : initial.RemovalForest parents)
    (edges : initial.GroupEdgesFrom (registrationSnapshot before event))
    (live : initial.LiveGroupsRegistered) (tasks : initial.TaskGroupsRegistered)
    (closures
      : ReferenceWorkQueue.GroupClosureAccounting
          (registrationSnapshot before event) (initial, preceding))
    (steps fuel : Nat) (failed : DeliveryNode) (errors : Nat)
    (path
      : (ReferenceWorkQueue.State.drainReadyGroups.go steps initial).1.LiveDescendant
          failed.ref target)
    : let current := (ReferenceWorkQueue.State.drainReadyGroups.go steps initial).1
      let earlier :=
        preceding ++ (ReferenceWorkQueue.State.drainReadyGroups.go steps initial).2
      (failurePruningView before event
        (earlier
          ++ [.groupFailure failed errors]
          ++ (ReferenceWorkQueue.State.drainReadyGroups.go fuel
                (current.removeGroup failed.ref)).2)).LiveDescendant
        failed.ref target := by
  dsimp only
  have prefixClosures := ReferenceWorkQueue.State.drainReadyGroups_go_closureAccounting live tasks steps
  have allClosures := closures.append prefixClosures
  have prefixForest := ReferenceWorkQueue.State.drainReadyGroups_go_preserves
    (fun queue => queue.RemovalForest parents)
    (fun _ node current _ _ _ _ => (current.finishGroupSuccess node).startNewWork _)
    (fun _ node errors current _ _ _ => current.removeGroup node.group.node.ref)
    forest steps
  apply failureBoundary_path failed errors fuel prefixForest
    ((ReferenceWorkQueue.State.drainReadyGroups_go_groupEdgesFrom steps initial).trans edges)
    _ path
  intro key published
  obtain ⟨owner, groups, streams, emitted, sameKey⟩ := mem_publicationRoots.mp published
  exact (allClosures.closed key
    (List.mem_flatMap.mpr ⟨_, emitted, sameKey ▸ List.mem_cons_self⟩)).lookup_none

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
