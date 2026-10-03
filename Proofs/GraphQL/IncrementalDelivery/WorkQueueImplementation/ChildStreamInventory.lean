import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistrationFreshness

/-! Stored child-stream links are distinct and backed by permanent registration. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Local link accounting, independent of source validity or generated work
-----------------------------------------------------------------------------------------

/-- Each stored task has distinct child-stream refs, all in the descriptor registry.
This is a derived implementation invariant, not a host-source or scheduler premise.
-/
def State.ChildStreamInventory (queue : State) : Prop :=
  ∀ node ∈ queue.taskNodes,
    node.childStreams.Nodup
    ∧ node.childStreams.Subset (queue.streams.map (fun stream => stream.node.ref))

/-- Extending the registry and retaining or emptying links preserves their inventory.
Witness: every surviving list uses its original uniqueness and registration evidence.
-/
theorem State.ChildStreamInventory.of_frame {before after : State}
    (inventory : before.ChildStreamInventory)
    (registered : before.streams.Subset after.streams)
    (retained
      : ∀ node ∈ after.taskNodes,
          node.childStreams = []
          ∨ ∃ old ∈ before.taskNodes, node.childStreams = old.childStreams)
    : after.ChildStreamInventory := by
  intro node member
  rcases retained node member with empty | ⟨old, included, same⟩
  · rw [empty]
    exact ⟨by simp, by intro ref impossible; cases impossible⟩
  · rw [same]
    exact ⟨(inventory old included).1,
      (inventory old included).2.trans (List.map_subset _ registered)⟩

/-- Replacing a task node preserves the inventory when its replacement links are certified.
Witness: each mapped entry is either the supplied replacement or an unchanged old node.
-/
theorem State.ChildStreamInventory.putTaskNode {queue : State}
    (inventory : queue.ChildStreamInventory) (updated : TaskNode)
    (unique : updated.childStreams.Nodup)
    (registered
      : updated.childStreams.Subset (queue.streams.map (fun stream => stream.node.ref)))
    : (queue.putTaskNode updated).ChildStreamInventory := by
  intro node member
  obtain ⟨old, included, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact ⟨unique, registered⟩
  · subst node; exact inventory old included

/-- Group registration leaves stored links and the stream registry unchanged.
Witness: the exact task-map and descriptor-map projection equations.
-/
theorem State.ChildStreamInventory.addGroups {queue : State}
    (inventory : queue.ChildStreamInventory) (groups : List Group)
    : (queue.addGroups groups).1.ChildStreamInventory := by
  intro node member
  rw [State.addGroups_taskNodes] at member
  rw [State.addGroups_streams]
  exact inventory node member

/-- Registering a task keeps old links or creates an empty link list.
Witness: the old-or-new task-node characterization and unchanged stream registry.
-/
theorem State.ChildStreamInventory.addTask {queue : State}
    (inventory : queue.ChildStreamInventory) (task : Task)
    : (queue.addTask task).ChildStreamInventory := by
  apply inventory.of_frame
  · rw [State.addTask_streams]; exact List.Subset.refl _
  · intro node member
    rcases queue.addTask_startedOldOrNew task member with old | new
    · exact .inr ⟨node, old, rfl⟩
    · exact .inl (new ▸ rfl)

/-- Stream attachment extends one task's links with fresh, registered, distinct refs.
Witness: the actual selection fold excludes every old registered ref, including old links;
the registry is extended before the updated task node is installed.
-/
theorem State.ChildStreamInventory.addStreams {queue : State}
    (inventory : queue.ChildStreamInventory) (streams : List Stream)
    (parent : Option Occurrence)
    : (queue.addStreams streams parent).1.ChildStreamInventory := by
  let fresh : List Stream := streams.foldl (fun selected stream =>
    if (queue.stream? stream.node.ref).isSome
        || selected.any (fun known => known.node.ref == stream.node.ref) then selected
    else selected ++ [stream]) []
  let current : State := { queue with streams := queue.streams ++ fresh }
  have prior : current.ChildStreamInventory := inventory.of_frame
    (List.subset_append_left _ _) (fun node member => .inr ⟨node, member, rfl⟩)
  have selected := queue.addStreams_selection_fresh streams
  cases parent with
  | none => exact prior
  | some occurrence =>
      simp only [State.addStreams]
      split
      · exact prior
      · rename_i node found
        have stored : node ∈ queue.taskNodes := (State.taskNode?_some found).1
        have old := inventory node stored
        apply prior.putTaskNode
        · refine List.nodup_append.mpr ⟨old.1, selected.1, ?_⟩
          intro ref linked other member same
          obtain ⟨stream, included, equal⟩ := List.mem_map.mp member
          exact selected.2 stream included ((same.trans equal.symm) ▸ old.2 linked)
        · intro ref member
          change ref ∈ (queue.streams ++ fresh).map (fun stream => stream.node.ref)
          rw [List.map_append]
          rcases List.mem_append.mp member with existing | added
          · exact List.mem_append_left _ (old.2 existing)
          · exact List.mem_append_right _ added

private theorem fold_preserves {α β : Type} (property : α → Prop) (step : α → β → α)
    (preserved : ∀ current item, property current → property (step current item))
    (items : List β) (current : α) (prior : property current)
    : property (items.foldl step current) := by
  induction items generalizing current with
  | nil => exact prior
  | cons item rest ih => exact ih _ (preserved current item prior)

/-- Full integration preserves distinct registered child links.
Witness: compose group/task preservation with the fresh attachment theorem.
-/
theorem State.ChildStreamInventory.maybeIntegrateWork {queue : State}
    (inventory : queue.ChildStreamInventory) (work : Work)
    (parent : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parent).1.ChildStreamInventory := by
  have tasks := fold_preserves State.ChildStreamInventory State.addTask
    (fun _ task prior => prior.addTask task) work.tasks _ (inventory.addGroups work.groups)
  exact tasks.addStreams work.streams parent

/-- Empty-group pruning changes neither stored task links nor stream descriptors.
Witness: both exact field-preservation equations for the bounded traversal.
-/
theorem State.ChildStreamInventory.pruneEmptyGroups {queue : State}
    (inventory : queue.ChildStreamInventory) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.ChildStreamInventory := by
  intro node member
  rw [State.pruneEmptyGroups_taskNodes] at member
  rw [State.pruneEmptyGroups_streams]
  exact inventory node member

/-- Starting a task keeps existing nodes or appends a node with no child links.
Witness: inspect the lookup guards; no stream descriptor is changed.
-/
theorem State.ChildStreamInventory.startTask {queue : State}
    (inventory : queue.ChildStreamInventory) (occurrence : Occurrence)
    : (queue.startTask occurrence).ChildStreamInventory := by
  unfold State.startTask
  split
  · exact inventory
  · split
    · exact inventory
    · apply inventory.of_frame
      · exact List.Subset.refl _
      · intro node member
        rcases List.mem_append.mp member with old | new
        · exact .inr ⟨node, old, rfl⟩
        · exact .inl (List.mem_singleton.mp new ▸ rfl)

/-- Starting a group preserves stored stream links while starting its tasks.
Witness: failed/missing groups do nothing; healthy starts use task-start preservation.
-/
theorem State.ChildStreamInventory.startGroup {queue : State}
    (inventory : queue.ChildStreamInventory) (ref : NodeRef)
    : (queue.startGroup ref).ChildStreamInventory := by
  unfold State.startGroup
  split
  · exact inventory
  · split
    · exact inventory
    · exact fold_preserves State.ChildStreamInventory State.startTask
        (fun _ occurrence prior => prior.startTask occurrence) _ _ inventory

/-- Activating new work preserves distinct registered child links.
Witness: group starts preserve the invariant, and stream starts only update active roots.
-/
theorem State.ChildStreamInventory.startNewWork {queue : State}
    (inventory : queue.ChildStreamInventory) (work : NewWork)
    : (queue.startNewWork work).ChildStreamInventory := by
  have groups := fold_preserves State.ChildStreamInventory State.startGroup
    (fun _ ref prior => prior.startGroup ref) (work.newGroups.map Execution.DeliveryNode.ref)
    { queue with rootGroups := queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.ref }
    inventory
  apply fold_preserves State.ChildStreamInventory State.startStream _ _ _ groups
  intro current ref prior
  unfold State.startStream
  split <;> exact prior

/-- Initial queue construction has distinct registered task-produced stream links.
Witness: the empty task map, integration, pruning, and activation preserve the invariant.
-/
theorem createWorkQueue_childStreamInventory (work : Work)
    : (State.initialize work).ChildStreamInventory := by
  have empty : ({} : State).ChildStreamInventory := by intro node impossible; cases impossible
  exact ((empty.maybeIntegrateWork work).pruneEmptyGroups _).startNewWork _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
