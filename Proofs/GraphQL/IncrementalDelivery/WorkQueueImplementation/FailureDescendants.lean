import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalUpdates

/-! Descendant coverage through the task-failure handler's sequential owner removals. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Removing one subtree preserves every path to a surviving descendant
-----------------------------------------------------------------------------------------

/-- Live descendant paths compose without consulting abstract work metadata.
Witness: prepend the first path's stored edges to the second path.
-/
theorem State.LiveDescendant.trans {queue : State} {first middle last}
    (left : queue.LiveDescendant first middle)
    (right : queue.LiveDescendant middle last)
    : queue.LiveDescendant first last := by
  induction left with
  | self found => exact right
  | child found linked below ih => exact .child found linked (ih right)

/-- Filtering whole group records by key either keeps the same lookup or removes it.
Witness: combine the filter and lookup predicates; both inspect the same key.
-/
theorem State.groupNode?_filterKeys (queue : State) (keep : Nat → Bool) (key : Nat)
    : (queue.groupNodes.filter (fun node => keep node.group.node.key)).find?
        (fun node => node.group.node.key == key)
      = if keep key then queue.groupNode? key else none := by
  simp only [State.groupNode?, List.find?_filter]
  by_cases kept : keep key = true
  · simp only [kept, ↓reduceIte]
    congr 1
    funext node
    by_cases same : node.group.node.key = key <;> simp [same, kept]
  · simp only [kept]
    apply List.find?_eq_none.mpr
    intro node member
    by_cases same : node.group.node.key = key <;> simp [same, kept]

/-- Group removal cannot create a group lookup that was previously absent.
Witness: its group-node map is a key filter of the old map.
-/
theorem State.removeGroup_groupNodeAbsent {queue : State} {key : Nat}
    (absent : queue.groupNode? key = none) (root : Nat)
    : (queue.removeGroup root).groupNode? key = none := by
  change (queue.groupNodes.filter
    (fun node => !(State.removeGroup.collect (queue.groupNodes.length + 1)
      queue [root] []).contains node.group.node.key)).find?
      (fun node => node.group.node.key == key) = none
  rw [State.groupNode?_filterKeys queue (fun key =>
    !(State.removeGroup.collect (queue.groupNodes.length + 1) queue [root] []).contains key)]
  split <;> simp [absent]

/-- Every group outside a removed live subtree retains its exact old lookup.
Witness: the collector contains exactly that subtree's live descendants.
-/
theorem State.removeGroup_groupNodeRetained
    {queue : State} {parents root key}
    (forest : queue.RemovalForest parents)
    (outside : ¬queue.LiveDescendant root key)
    : (queue.removeGroup root).groupNode? key = queue.groupNode? key := by
  have absent : key ∉ State.removeGroup.collect (queue.groupNodes.length + 1)
      queue [root] [] := fun member => outside
        ((State.removeGroup_collect_mem_iff forest).mp member)
  change (queue.groupNodes.filter
    (fun node => !(State.removeGroup.collect (queue.groupNodes.length + 1)
      queue [root] []).contains node.group.node.key)).find?
      (fun node => node.group.node.key == key)
    = queue.groupNode? key
  rw [State.groupNode?_filterKeys queue (fun key =>
    !(State.removeGroup.collect (queue.groupNodes.length + 1) queue [root] []).contains key)]
  simp [absent]

/-- Removal preserves the finite forest on retained group records.
Witness: every retained child list and live edge already belonged to the old forest.
-/
theorem State.RemovalForest.removeGroup
    {queue : State} {parents} (forest : queue.RemovalForest parents) (root : Nat)
    : (queue.removeGroup root).RemovalForest parents := by
  refine ⟨forest.uniqueChildren.removeGroup root, forest.canonical.removeGroup root, ?_⟩
  intro parent child parentMember childMember linked
  exact forest.increasing (List.mem_filter.mp parentMember).1
    (List.mem_filter.mp childMember).1 linked

/-- A path to a surviving descendant remains intact after removing another subtree.
Witness: removal of any path vertex would also remove its descendant by transitivity
and traversal coverage. Every vertex lookup and child list is therefore retained.
-/
theorem State.LiveDescendant.removeGroup
    {queue : State} {parents root target removed}
    (forest : queue.RemovalForest parents)
    (path : queue.LiveDescendant root target)
    (outside : ¬queue.LiveDescendant removed target)
    : (queue.removeGroup removed).LiveDescendant root target := by
  induction path with
  | self found =>
      exact .self ((State.removeGroup_groupNodeRetained forest outside).trans found)
  | @child key node child target found linked below ih =>
      have rootOutside : ¬queue.LiveDescendant removed key := by
        intro reaches
        exact outside (reaches.trans (.child found linked below))
      exact .child
        ((State.removeGroup_groupNodeRetained forest rootOutside).trans found) linked
        (ih outside)

/-- Each original path either loses its target or survives a subtree removal intact.
Witness: split on membership in the removed live subtree; coverage or path retention
then supplies the corresponding result.
-/
theorem State.LiveDescendant.removeGroup_or_absent
    {queue : State} {parents root target removed}
    (forest : queue.RemovalForest parents)
    (path : queue.LiveDescendant root target)
    : ((queue.removeGroup removed).groupNode? target = none
        ∧ target ∉ (queue.removeGroup removed).rootGroups)
      ∨ (queue.removeGroup removed).LiveDescendant root target := by
  by_cases affected : queue.LiveDescendant removed target
  · exact Or.inl (State.removeGroup_liveDescendant_absent forest affected)
  · exact Or.inr (path.removeGroup forest affected)

-----------------------------------------------------------------------------------------
-- Accepted failures cover descendants of announced contributing owners
-----------------------------------------------------------------------------------------

/-- An accepted task failure removes descendants of each announced contributing group.
Witness: an earlier removal clears the target or retains its path and active owner.
Caching another owner's failure changes no child links. Unannounced owners are retained,
and a settlement with no healthy owner is ignored; neither case implies removal.
-/
theorem State.taskFailure_liveDescendant_absent
    {queue : State} {parents occurrence errors taskNode owner target}
    (forest : queue.RemovalForest parents)
    (unique : queue.GroupKeysUnique)
    (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    (contributes : owner ∈ taskNode.task.groups)
    (active : owner.key ∈ queue.rootGroups)
    (path : queue.LiveDescendant owner.key target)
    : (queue.taskFailure occurrence errors).1.groupNode? target = none
      ∧ target ∉ (queue.taskFailure occurrence errors).1.rootGroups := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent :=
    let (current, events) := acc
    match current.groupNode? group.key with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.key then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else (current.putGroupNode
          { node with
            pending := node.pending - 1
            failure := some (node.failure.getD 0 + errors) }, events)
  let cleared (current : State) :=
    current.groupNode? target = none ∧ target ∉ current.rootGroups
  have stepState (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      : (step acc group).1 = acc.1
        ∨ (step acc group).1 = acc.1.removeGroup group.key
        ∨ ∃ node, acc.1.groupNode? group.key = some node
            ∧ (step acc group).1 = acc.1.putGroupNode
                { node with
                  pending := node.pending - 1
                  failure := some (node.failure.getD 0 + errors) } := by
    obtain ⟨current, events⟩ := acc
    cases nodeFound : current.groupNode? group.key with
    | none => exact Or.inl (by simp [step, nodeFound])
    | some node =>
        have nodeKey := State.groupNode?_key nodeFound
        by_cases announced : group.key ∈ current.rootGroups
        · exact Or.inr (Or.inl (by
            simp [step, nodeFound, announced, State.finishGroupFailure, nodeKey]))
        · exact Or.inr (Or.inr ⟨node, rfl, by
            simp [step, nodeFound, announced]⟩)
  have stepUnique (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (currentUnique : acc.1.GroupKeysUnique)
      : (step acc group).1.GroupKeysUnique := by
    rcases stepState acc group with same | removed | ⟨node, _, cached⟩
    · exact same ▸ currentUnique
    · rw [removed]
      exact currentUnique.removeGroup group.key
    · rw [cached]
      exact currentUnique.putGroupNode _
  have stepForest (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (currentForest : acc.1.RemovalForest parents)
      (currentUnique : acc.1.GroupKeysUnique)
      : (step acc group).1.RemovalForest parents := by
    rcases stepState acc group with same | removed | ⟨node, nodeFound, cached⟩
    · exact same ▸ currentForest
    · rw [removed]
      exact currentForest.removeGroup group.key
    · rw [cached]
      exact currentForest.putCounters currentUnique nodeFound _ _
  have stepCleared (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (absent : cleared acc.1) : cleared (step acc group).1 := by
    rcases stepState acc group with same | removed | ⟨node, _, cached⟩
    · simpa only [same] using absent
    · rw [removed]
      exact ⟨State.removeGroup_groupNodeAbsent absent.1 group.key,
        fun member => absent.2 (acc.1.removeGroup_rootsSubset group.key member)⟩
    · rw [cached]
      exact ⟨State.putCounters_groupNodeAbsent absent.1 _ _, absent.2⟩
  have stepPath (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (currentForest : acc.1.RemovalForest parents)
      (currentUnique : acc.1.GroupKeysUnique)
      {root} (currentPath : acc.1.LiveDescendant root target)
      (currentActive : root ∈ acc.1.rootGroups)
      : cleared (step acc group).1
        ∨ (step acc group).1.LiveDescendant root target
          ∧ root ∈ (step acc group).1.rootGroups := by
    rcases stepState acc group with same | removed | ⟨node, nodeFound, cached⟩
    · exact Or.inr (same ▸ ⟨currentPath, currentActive⟩)
    · rw [removed]
      by_cases affected : acc.1.LiveDescendant group.key target
      · exact Or.inl (State.removeGroup_liveDescendant_absent currentForest affected)
      · refine Or.inr ⟨currentPath.removeGroup currentForest affected, ?_⟩
        have rootOutside : ¬acc.1.LiveDescendant group.key root :=
          fun reaches => affected (reaches.trans currentPath)
        have notCollected : root ∉ State.removeGroup.collect
            (acc.1.groupNodes.length + 1) acc.1 [group.key] [] :=
          fun member => rootOutside ((State.removeGroup_collect_mem_iff currentForest).mp member)
        exact List.mem_filter.mpr ⟨currentActive, by simpa using notCollected⟩
    · rw [cached]
      exact Or.inr ⟨currentPath.putCounters currentUnique nodeFound _ _, currentActive⟩
  have stepCovers (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (currentForest : acc.1.RemovalForest parents)
      (currentPath : acc.1.LiveDescendant group.key target)
      (currentActive : group.key ∈ acc.1.rootGroups)
      : cleared (step acc group).1 := by
    obtain ⟨node, nodeFound⟩ := currentPath.found
    have nodeKey := State.groupNode?_key nodeFound
    have removed := State.removeGroup_liveDescendant_absent currentForest currentPath
    obtain ⟨current, events⟩ := acc
    simpa [step, nodeFound, currentActive, cleared, State.finishGroupFailure, nodeKey]
      using removed
  have foldCleared (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (absent : cleared acc.1) : cleared (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact absent
    | cons group rest ih => exact ih (step acc group) (stepCleared acc group absent)
  have foldCovers (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (currentForest : acc.1.RemovalForest parents)
      (currentUnique : acc.1.GroupKeysUnique)
      (member : owner ∈ more) (currentPath : acc.1.LiveDescendant owner.key target)
      (currentActive : owner.key ∈ acc.1.rootGroups)
      : cleared (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => cases member
    | cons group rest ih =>
        rcases List.mem_cons.mp member with same | later
        · subst owner
          exact foldCleared rest (step acc group)
            (stepCovers acc group currentForest currentPath currentActive)
        · rcases stepPath acc group currentForest currentUnique currentPath currentActive
            with absent | ⟨survives, stillActive⟩
          · exact foldCleared rest (step acc group) absent
          · exact ih (step acc group) (stepForest acc group currentForest currentUnique)
              (stepUnique acc group currentUnique) later survives stillActive
  let current := queue.removeTask occurrence
  unfold State.taskFailure
  simp only [found, accepted, Bool.not_true, Bool.false_eq_true, ite_false]
  exact foldCovers taskNode.task.groups (current, []) (forest.removeTask occurrence)
    (unique.removeTask occurrence) contributes (path.removeTask occurrence) active

/-- An accepted failure covers announced-owner descendants after generated replay.
Witness: generated metadata and concrete bookkeeping derive the removal forest; the
sequential-removal theorem then consumes the looked-up task and its stored owner path.
Acceptance and announcement are local branch facts, not extra event-source assumptions.
-/
theorem ExecutedWork.runNormalized_taskFailure_covers
    {work : Execution.Work} (generated : ExecutedWork work)
    (batches : List (List GraphEvent)) (valid : ValidGraphEvents work batches.flatten)
    {occurrence errors taskNode owner target}
    (found
      : ((State.initialize (Work.fromExecution work)).runNormalized batches).1.taskNode?
          occurrence
        = some taskNode)
    (accepted
      : ((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.taskHasHealthyOwner
          taskNode.task
        = true)
    (contributes : owner ∈ taskNode.task.groups)
    (active
      : owner.key
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.rootGroups)
    (path
      : ((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.LiveDescendant
          owner.key target)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      (queue.taskFailure occurrence errors).1.groupNode? target = none
      ∧ target ∉ (queue.taskFailure occurrence errors).1.rootGroups := by
  obtain ⟨parents, forest⟩ := generated.runNormalized_removalForest batches valid
  exact State.taskFailure_liveDescendant_absent forest
    (createWorkQueue_runNormalized_groupKeysUnique _ _) found accepted contributes active path

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
