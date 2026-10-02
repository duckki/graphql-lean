import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainRootCoverage

/-! The single-pass contributor fold retains coverage while child releases await activation. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A closing group transfers coverage to its release without activating it prematurely
-----------------------------------------------------------------------------------------

/-- Successful closure preserves coverage by active or retained release roots.
Witness: descendants of the closing group move to its promoted frontier; unrelated paths
retain their old root. Previously retained releases remain available without changing the
implementation's activation order or requiring them to be announced already.
-/
theorem State.finishGroupSuccess_retained_root_coverage {queue : State} {parents target}
    (forest : queue.RemovalForest parents) {group : GroupNode}
    (found : queue.groupNode? group.group.node.key = some group) (retained : Keys)
    (covered : ∃ root ∈ queue.rootGroups ++ retained, queue.LiveDescendant root target)
    (survives : ∃ node, (queue.finishGroupSuccess group).1.groupNode? target = some node)
    : let result := queue.finishGroupSuccess group
      ∃ root ∈
        result.1.rootGroups
        ++ retained
        ++ result.2.2.newGroups.map Execution.DeliveryNode.key,
        result.1.LiveDescendant root target := by
  intro result
  classical
  obtain ⟨root, member, path⟩ := covered
  by_cases affected : queue.LiveDescendant group.group.node.key target
  · obtain ⟨next, released, below⟩ :=
      State.finishGroupSuccess_surviving_descendant forest found affected survives
    exact ⟨next.key, List.mem_append_right _ (List.mem_map_of_mem released), below⟩
  · have outside : ¬queue.LiveDescendant group.group.node.key root :=
      fun reaches => affected (reaches.trans path)
    have different : root ≠ group.group.node.key := fun same => affected (same ▸ path)
    obtain ⟨old, oldFound⟩ := path.found
    have oldMember : root ∈ queue.groupNodes.map (fun node => node.group.node.key) :=
      List.mem_map.mpr ⟨old, List.mem_of_find?_eq_some oldFound, State.groupNode?_key oldFound⟩
    have retainedRoot := State.finishGroupSuccess_preserves_outside oldMember found outside
    have rootSurvives : ∃ node, result.1.groupNode? root = some node := by
      cases lookup : result.1.groupNode? root with
      | none =>
          obtain ⟨node, live, key⟩ := List.mem_map.mp retainedRoot
          have missing := List.find?_eq_none.mp lookup node live
          simp [key] at missing
      | some node => exact ⟨node, rfl⟩
    refine ⟨root, List.mem_append_left _ ?_,
      path.finishGroupSuccess forest found affected rootSurvives⟩
    rcases List.mem_append.mp member with active | waiting
    · apply List.mem_append_left
      rw [State.finishGroupSuccess_rootGroups]
      exact List.mem_filter.mpr ⟨active, by simp [different]⟩
    · exact List.mem_append_right _ waiting

-----------------------------------------------------------------------------------------
-- Thread delayed releases through the exact single-pass contributor loop
-----------------------------------------------------------------------------------------

/-- A contributor fold retains its forest and coverage by roots or delayed releases.
Witness: decrementing counts preserves paths; closure transfers affected paths to the
accumulated release list. No activation is inserted into the single-pass algorithm.
-/
private theorem successGroupFold_retained_coverage {queue : State} {parents target}
    (unique : queue.GroupKeysUnique) (forest : queue.RemovalForest parents)
    (groups : List Execution.DeliveryNode)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    : let folded := groups.foldl successGroupStep (queue, [], {})
      folded.1.GroupKeysUnique
      ∧ folded.1.RemovalForest parents
      ∧ ((∃ node, folded.1.groupNode? target = some node)
          → ∃ root ∈
              folded.1.rootGroups ++ folded.2.2.newGroups.map Execution.DeliveryNode.key,
              folded.1.LiveDescendant root target) := by
  let property (acc : State × List WorkQueueEvent × NewWork) :=
    acc.1.GroupKeysUnique ∧ acc.1.RemovalForest parents
    ∧ ((∃ node, acc.1.groupNode? target = some node)
      → ∃ root ∈ acc.1.rootGroups ++ acc.2.2.newGroups.map Execution.DeliveryNode.key,
          acc.1.LiveDescendant root target)
  have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (prior : property acc) : property (successGroupStep acc group) := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact prior
    · rename_i node found
      let changed : GroupNode := { node with pending := node.pending - 1 }
      let updated := current.putGroupNode changed
      have updatedKeys : updated.GroupKeysUnique := prior.1.putGroupNode changed
      have updatedForest : updated.RemovalForest parents :=
        prior.2.1.putCounters prior.1 found _ node.failure
      have updatedEdges : updated.GroupEdgesFrom current :=
        State.putPending_groupEdgesFrom prior.1 found _
      have updatedCoverage : ∀ child, updated.groupNode? target = some child
          → ∃ root ∈ updated.rootGroups ++ released.newGroups.map Execution.DeliveryNode.key,
              updated.LiveDescendant root target := by
        intro child lookup
        obtain ⟨old, oldFound, _⟩ := updatedEdges _ _ lookup
        obtain ⟨root, member, path⟩ := prior.2.2 ⟨old, oldFound⟩
        exact ⟨root, member, path.putCounters prior.1 found _ node.failure⟩
      split
      · refine ⟨updatedKeys.finishGroupSuccess changed,
          updatedForest.finishGroupSuccess changed, ?_⟩
        rintro ⟨child, lookup⟩
        obtain ⟨old, oldFound, _⟩ := (updated.finishGroupSuccess_descendants changed).1 _ _ lookup
        have changedFound : updated.groupNode? changed.group.node.key = some changed :=
          updatedKeys.groupNode?_of_mem (List.mem_map.mpr
            ⟨node, List.mem_of_find?_eq_some found, by simp [changed]⟩)
        have next := State.finishGroupSuccess_retained_root_coverage updatedForest changedFound
          (released.newGroups.map Execution.DeliveryNode.key) (updatedCoverage old oldFound)
          ⟨child, lookup⟩
        simpa only [List.map_append, List.append_assoc] using next
      · exact ⟨updatedKeys, updatedForest, fun ⟨child, found⟩ => updatedCoverage child found⟩
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (prior : property acc) : property (more.foldl successGroupStep acc) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons group rest ih => exact ih _ (step acc group prior)
  exact loop groups (queue, [], {})
    ⟨unique, forest, fun _ => by simpa using covered⟩

/-- A contributor fold cannot strand any initially covered group that remains live.
Witness: accumulated release coverage is activated only after the original single-pass
fold. Contributor order, duplicate contributors, and successive closures are unrestricted.
-/
theorem State.successGroupFold_activated_root_coverage {queue : State} {parents target}
    (unique : queue.GroupKeysUnique) (forest : queue.RemovalForest parents)
    (groups : List Execution.DeliveryNode)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    : let folded := groups.foldl successGroupStep (queue, [], {})
      let next := folded.1.startNewWork folded.2.2
      (∃ node, next.groupNode? target = some node)
      → ∃ root ∈ next.rootGroups, next.LiveDescendant root target := by
  have final := successGroupFold_retained_coverage unique forest groups covered
  intro folded next survives
  have beforeStart : ∃ node, folded.1.groupNode? target = some node := by
    simpa only [next, State.groupNode?, (State.startNewWork_groupCore _ _).1]
      using survives
  obtain ⟨root, member, path⟩ := final.2.2 beforeStart
  exact ⟨
    root,
    by rwa [(State.startNewWork_groupCore _ _).2.2],
    path.of_groupNodes_eq (State.startNewWork_groupCore _ _).1
  ⟩

/-- Final draining cannot strand a target covered before the contributor fold.
Witness: delayed-release coverage after the fold, followed by the mixed-drain coverage
theorem. Backward lookup provenance recovers survival at the pre-drain boundary.
-/
theorem State.successGroupFold_drained_root_coverage {queue : State} {parents target}
    (unique : queue.GroupKeysUnique) (forest : queue.RemovalForest parents)
    (groups : List Execution.DeliveryNode)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    : let folded := groups.foldl successGroupStep (queue, [], {})
      let active := folded.1.startNewWork folded.2.2
      let final := active.drainReadyGroups.1
      (∃ node, final.groupNode? target = some node)
      → ∃ root ∈ final.rootGroups, final.LiveDescendant root target := by
  intro folded active final survives
  have frame := successGroupFold_retained_coverage unique forest groups covered
  have keys := frame.1.startNewWork folded.2.2
  have currentForest := frame.2.1.startNewWork folded.2.2
  obtain ⟨node, found⟩ := survives
  obtain ⟨prior, priorFound, _⟩ := (active.drainReadyGroups_descendants keys).1 _ _ found
  have coverage := State.successGroupFold_activated_root_coverage unique forest groups covered
    ⟨prior, priorFound⟩
  exact State.drainReadyGroups_root_coverage keys currentForest target coverage ⟨node, found⟩

/-- Actual successful task handling preserves coverage established at child integration.
Witness: unfold the accepted healthy branch and apply coverage through the unchanged
single-pass contributor fold, delayed activation, and recursive drain.
-/
theorem State.taskSuccess_integrated_root_coverage {queue : State}
    {parents target occurrence node} (unique : queue.GroupKeysUnique)
    (found : queue.taskNode? occurrence = some node)
    (healthy : queue.taskHasHealthyOwner node.task = true) (result : TaskResult)
    : let stored := queue.putTaskNode { node with value := some result.value }
      let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
      integrated.RemovalForest parents
      → (∃ root ∈ integrated.rootGroups, integrated.LiveDescendant root target)
      → (∃ child, (queue.taskSuccess occurrence result).1.groupNode? target = some child)
      → ∃ root ∈ (queue.taskSuccess occurrence result).1.rootGroups,
          (queue.taskSuccess occurrence result).1.LiveDescendant root target := by
  intro stored integrated forest covered survives
  have storedKeys : stored.GroupKeysUnique := unique
  have resultCoverage := State.successGroupFold_drained_root_coverage
    (storedKeys.maybeIntegrateWork result.work (some occurrence)) forest node.task.groups covered
  rw [queue.taskSuccess_eq occurrence result node found] at survives ⊢
  simp only [healthy, Bool.not_true, Bool.false_eq_true, ite_false] at survives ⊢
  exact resultCoverage survives

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
