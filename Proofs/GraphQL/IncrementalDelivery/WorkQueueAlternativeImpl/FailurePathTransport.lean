import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PendingFailureCut
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDescendants

/-! Failure-boundary paths survive the cleanup view's upfront successful-key exclusion.
Use the actual preceding retirement and remaining drain, not final-state absence alone.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)

/-- Retained rejection replay preserves the generated removal forest. -/
theorem State.RemovalForest.taskFailure {queue : State} {parents}
    (forest : queue.RemovalForest parents) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.RemovalForest parents := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using forest
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      apply failureGroupFold_preserves (fun current => current.RemovalForest parents)
        (fun _ ref prior => prior.removeGroup ref)
      exact ⟨forest.uniqueChildren, forest.canonical, forest.increasing⟩

/-- A replayed identical rejection preserves another exact buffer while its owner survives. -/
theorem State.taskFailure_lookup_survivingOwner_unchanged {queue : State}
    {occurrence node} (found : queue.taskNode? occurrence = some node)
    (failed : Occurrence) (errors : Nat)
    (unchanged : occurrence ≠ failed ∨ node.rejection = some errors)
    {contributor : Execution.DeliveryNode} (contributes : contributor ∈ node.task.groups)
    {owner : GroupNode} (live : owner ∈ (queue.taskFailure failed errors).1.groupNodes)
    (same : owner.group.node.ref = contributor.ref)
    : (queue.taskFailure failed errors).1.taskNode? occurrence = some node := by
  by_cases different : occurrence ≠ failed
  · exact State.taskFailure_lookup_survivingOwner found failed errors different contributes live same
  · have equal : occurrence = failed := Classical.not_not.mp different
    subst failed
    have rejected := unchanged.resolve_left (by simp)
    rw [queue.taskFailure_eq occurrence errors node found] at live ⊢
    have identical : { node with rejection := some errors } = node := by
      cases node
      simp_all
    have stored := State.putTaskNode_lookup_same found
      { node with rejection := some errors } (State.taskNode?_some found).2
    rw [identical] at stored live ⊢
    exact failureGroupFold_lookup_survivingOwner errors _ _ stored contributes live same

end GraphQL.IncrementalDelivery.ReferenceWorkQueue

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

/-- Every failed completion emitted in a rejection pass had an active root at entry. -/
theorem taskFailure_failureRoot_active (queue : Kernel)
    (occurrence : WorkQueueSemantics.Occurrence) (errors : Nat) {group count}
    (emitted : .groupFailure group count ∈ (queue.taskFailure occurrence errors).2)
    : group.ref ∈ queue.rootGroups := by
  have loop (groups : List DeliveryNode) (acc : Kernel × List WorkQueueEvent)
      (roots : acc.1.rootGroups.Subset queue.rootGroups)
      (prior : ∀ group count, .groupFailure group count ∈ acc.2 → group.ref ∈ queue.rootGroups)
      : ∀ group count,
          .groupFailure group count ∈ (groups.foldl (ReferenceWorkQueue.failureGroupStep errors) acc).2
          → group.ref ∈ queue.rootGroups := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons owner rest ih =>
        refine ih (ReferenceWorkQueue.failureGroupStep errors acc owner) ?_ ?_
        · unfold ReferenceWorkQueue.failureGroupStep
          dsimp only
          split
          · exact roots
          · split
            · intro ref active
              exact roots (List.mem_filter.mp active).1
            · exact roots
        · unfold ReferenceWorkQueue.failureGroupStep
          dsimp only
          split
          · exact prior
          · rename_i node found
            split
            · rename_i active
              intro group count member
              rcases List.mem_append.mp member with earlier | recent
              · exact prior group count earlier
              · have same := List.mem_singleton.mp recent
                have equal : group = node.group.node := (WorkQueueEvent.groupFailure.inj same).1
                rw [equal, ReferenceWorkQueue.State.groupNode?_ref found]
                exact roots (List.contains_iff_mem.mp active)
            · exact prior
  cases found : queue.taskNode? occurrence with
  | none => simp [ReferenceWorkQueue.State.taskFailure, found] at emitted
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found] at emitted
      exact loop task.task.groups _ (List.Subset.refl _)
        (by intro _ _ member; cases member) group count emitted

/-- A reported rejection subtree is absent after the full owner pass. -/
theorem taskFailure_failedDescendant_absent {current : Kernel}
    {parents occurrence errors root key} (forest : current.RemovalForest parents)
    (unique : current.GroupRefsUnique)
    (reported : root ∈ failureRoots (current.taskFailure occurrence errors).2)
    (path : current.LiveDescendant root key)
    : (current.taskFailure occurrence errors).1.groupNode? key = none := by
  obtain ⟨event, emitted, selected⟩ := List.mem_filterMap.mp reported
  obtain ⟨group, rfl⟩ := current.taskFailure_event_failure occurrence errors event emitted
  have same : group.ref = root := Option.some.inj selected
  obtain ⟨task, found, member, _⟩ :=
    current.taskFailure_groupFailure_current occurrence errors emitted
  obtain ⟨owner, contributes, equal⟩ := List.mem_map.mp member
  have active := taskFailure_failureRoot_active current occurrence errors emitted
  exact (ReferenceWorkQueue.State.taskFailure_liveDescendant_absent forest unique found
    contributes (equal ▸ active) (equal ▸ same.symm ▸ path)).1

/-- A path below an actual rejection-pass report survives full-handler publication filtering. -/
theorem taskFailureBoundary_path {before current : Kernel}
    {event parents earlier target root} (occurrence : WorkQueueSemantics.Occurrence)
    (errors fuel : Nat) (forest : current.RemovalForest parents)
    (unique : current.GroupRefsUnique)
    (edges : current.GroupEdgesFrom (registrationSnapshot before event))
    (retired : ∀ key ∈ publicationRoots earlier, current.groupNode? key = none)
    (reported : root ∈ failureRoots (current.taskFailure occurrence errors).2)
    (path : current.LiveDescendant root target)
    : (failurePruningView before event
        (earlier
          ++ (current.taskFailure occurrence errors).2
          ++ (ReferenceWorkQueue.State.drainReadyGroups.go fuel
                (current.taskFailure occurrence errors).1).2)).LiveDescendant
        root target := by
  apply failurePruningView_pathFrom edges path
  intro key fromRoot toTarget published
  simp only [publicationRoots, List.filterMap_append, List.mem_append] at published
  rcases published with (old | during) | later
  · obtain ⟨node, found⟩ := toTarget.found
    rw [retired key old] at found
    contradiction
  · obtain ⟨carrier, groups, streams, impossible, _⟩ := mem_publicationRoots.mp during
    exact current.taskFailure_noGroupSuccess occurrence errors carrier groups streams impossible
  · have live := drainReadyGroups_go_publicationRoots_live fuel
      (current.taskFailure occurrence errors).1 later
    obtain ⟨node, member, same⟩ := List.mem_map.mp live
    have absent := taskFailure_failedDescendant_absent forest unique reported fromRoot
    exact (List.find?_eq_none.mp absent node member) (by simp [same])

/-- The complete rejection pass retains a live key or gives its actual emitted failure path. -/
theorem taskFailure_ownerCut {before current : Kernel} {event parents earlier key}
    (occurrence : WorkQueueSemantics.Occurrence) (errors fuel : Nat)
    (forest : current.RemovalForest parents) (unique : current.GroupRefsUnique)
    (edges : current.GroupEdgesFrom (registrationSnapshot before event))
    (closures
      : ReferenceWorkQueue.GroupClosureAccounting
          (registrationSnapshot before event) (current, earlier))
    (present : key ∈ current.groupNodes.map (fun group => group.group.node.ref))
    : key
        ∈ (current.taskFailure occurrence errors).1.groupNodes.map
            (fun group => group.group.node.ref)
      ∨ ∃ root ∈ failureRoots (current.taskFailure occurrence errors).2,
          (failurePruningView before event
            (earlier
              ++ (current.taskFailure occurrence errors).2
              ++ (ReferenceWorkQueue.State.drainReadyGroups.go fuel
                    (current.taskFailure occurrence errors).1).2)).LiveDescendant
            root key := by
  classical
  by_cases kept : key ∈ (current.taskFailure occurrence errors).1.groupNodes.map
      (fun group => group.group.node.ref)
  · exact .inl kept
  · right
    have path : ∃ root ∈ failureRoots (current.taskFailure occurrence errors).2,
        current.LiveDescendant root key := by
      apply Classical.byContradiction
      intro absent
      obtain ⟨node, member, same⟩ := List.mem_map.mp present
      have found := unique.groupNode?_of_mem member
      rw [same] at found
      obtain ⟨retained, lookup⟩ := taskFailure_outside_survives unique forest occurrence errors
        ⟨node, found⟩ (fun root reported below => absent ⟨root, reported, below⟩)
      exact kept (List.mem_map.mpr ⟨retained, List.mem_of_find?_eq_some lookup,
        ReferenceWorkQueue.State.groupNode?_ref lookup⟩)
    obtain ⟨root, reported, below⟩ := path
    refine ⟨root, reported, taskFailureBoundary_path occurrence errors fuel forest unique
      edges ?_ reported below⟩
    intro ref published
    obtain ⟨carrier, groups, streams, emitted, same⟩ := mem_publicationRoots.mp published
    exact (closures.closed ref
      (List.mem_flatMap.mpr ⟨_, emitted, same ▸ List.mem_cons_self⟩)).lookup_none

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
    (fun _ _ occurrence errors current _ _ _ => current.taskFailure occurrence errors)
    forest steps
  apply failureBoundary_path failed errors fuel prefixForest
    ((ReferenceWorkQueue.State.drainReadyGroups_go_groupEdgesFrom steps initial).trans edges)
    _ path
  intro key published
  obtain ⟨owner, groups, streams, emitted, sameKey⟩ := mem_publicationRoots.mp published
  exact (allClosures.closed key
    (List.mem_flatMap.mpr ⟨_, emitted, sameKey ▸ List.mem_cons_self⟩)).lookup_none

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
