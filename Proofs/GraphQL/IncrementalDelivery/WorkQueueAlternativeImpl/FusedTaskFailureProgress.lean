import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedUnsettledTaskDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureResources

/-! Task ownership through the actual failed-owner fold. An unfinished task needs no
computation node: its complete memberships force disposal when its last owner is removed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (NodeRefs Occurrence)

private theorem failureFold_targets (errors : Nat) (groups : List Execution.DeliveryNode)
    (acc : State × List Execution.WorkQueueEvent × List CleanupTarget)
    : acc.2.2.Subset (groups.foldl (fusedFailureGroupStep errors) acc).2.2 := by
  induction groups generalizing acc with
  | nil => exact List.Subset.refl _
  | cons group rest ih =>
      apply List.Subset.trans (l₂ := (fusedFailureGroupStep errors acc group).2.2) ?_ (ih _)
      unfold fusedFailureGroupStep
      split
      · exact List.Subset.refl _
      · split
        · exact (FusedRemovalSafety_holds acc.1 _ acc.2.2).1
        · exact List.Subset.refl _

theorem failureFold_unsettledTask {work : Work} {parents : Nat → NodeRefs}
    (errors : Nat) (groups : List Execution.DeliveryNode)
    (acc : State × List Execution.WorkQueueEvent × List CleanupTarget)
    (frame : acc.1.queue.TaskOwnerFrame work) (forest : acc.1.queue.RemovalForest parents)
    (task : ReferenceWorkQueue.Task)
    (catalogue : acc.1.queue.task? task.occurrence = some task)
    (links
      : acc.1.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref))
    (owned
      : ∃ owner ∈ task.groups, ∃ group, acc.1.queue.groupNode? owner.ref = some group)
    (unique : acc.2.2.Nodup)
    : let next := groups.foldl (fusedFailureGroupStep errors) acc
      (next.1.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref)
        ∧ ∃ owner ∈ task.groups, ∃ group, next.1.queue.groupNode? owner.ref = some group)
      ∨ .task task.occurrence ∈ next.2.2 := by
  induction groups generalizing acc with
  | nil => exact .inl ⟨links, owned⟩
  | cons group rest ih =>
      let next := fusedFailureGroupStep errors acc group
      have projected := fusedFailureGroupStep_projection errors acc frame forest group
      have nextUnique := fusedFailureGroupStep_targets errors acc group unique
      have nextCatalogue : next.1.queue.task? task.occurrence = some task := by
        rw [show next.1.queue = (ReferenceWorkQueue.failureGroupStep errors (acc.1.queue, acc.2.1) group).1
          from congrArg Prod.fst projected.1]
        unfold ReferenceWorkQueue.failureGroupStep
        dsimp only
        split
        · exact catalogue
        · split <;> exact catalogue
      have step : (next.1.queue.TaskLinkedOn task.occurrence (task.groups.map Execution.DeliveryNode.ref)
          ∧ ∃ owner ∈ task.groups, ∃ group, next.1.queue.groupNode? owner.ref = some group)
          ∨ .task task.occurrence ∈ next.2.2 := by
        unfold next fusedFailureGroupStep
        cases found : acc.1.queue.groupNode? group.ref with
        | none => exact .inl ⟨links, owned⟩
        | some node =>
            simp only
            split
            · rcases FusedRemovalTaskProgress_holds acc.1 node.group.node.ref task acc.2.2
                  unique catalogue links owned with kept | aborted
              · exact .inl kept
              · have listed : CleanupTarget.task task.occurrence ∈
                    ((acc.1.removeGroup node.group.node.ref acc.2.2).2.flatMap
                      CleanupTarget.effects).filterMap HostEffect.cleanupStart? :=
                  List.mem_filterMap.mpr ⟨HostEffect.abortTask task.occurrence, aborted, rfl⟩
                rw [cleanupEffects_starts] at listed
                exact .inr listed
            · refine .inl ⟨links.putGroupNodeSameTasks frame.keys node
                (List.mem_of_find?_eq_some found) _ rfl rfl, ?_⟩
              obtain ⟨owner, member, old, lookup⟩ := owned
              refine ⟨owner, member, ?_⟩
              cases live : (acc.1.queue.putGroupNode _).groupNode? owner.ref with
              | some current => exact ⟨current, rfl⟩
              | none =>
                  have present : owner.ref ∈ acc.1.queue.groupNodes.map (fun node => node.group.node.ref) :=
                    List.mem_map.mpr ⟨old, List.mem_of_find?_eq_some lookup,
                      ReferenceWorkQueue.State.groupNode?_ref lookup⟩
                  rw [← ReferenceWorkQueue.State.putGroupNode_refs] at present
                  exact False.elim ((ReferenceWorkQueue.State.groupNode?_eq_none_iff _ _).mp live present)
      rw [List.foldl_cons]
      rcases step with kept | requested
      · exact ih next projected.2.1 projected.2.2 nextCatalogue kept.1 kept.2 nextUnique
      · exact .inr (failureFold_targets errors rest next requested)

/-- The other unfinished task retains a real owner or receives an abort from this handler.
The input task itself is already settled and is deliberately excluded.
-/
theorem State.taskFailure_unsettledTask {state : State} {work : Work}
    {parents : Nat → NodeRefs} (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents) (failed : Occurrence) (errors : Nat)
    (task : ReferenceWorkQueue.Task) (different : task.occurrence ≠ failed)
    (catalogue : state.queue.task? task.occurrence = some task)
    (links
      : state.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref))
    (owned
      : ∃ owner ∈ task.groups, ∃ group, state.queue.groupNode? owner.ref = some group)
    : RecordTargetRepresented (state.taskFailure failed errors).1.queue
        (.task task.occurrence)
      ∨ .abortTask task.occurrence ∈ (state.taskFailure failed errors).2.2 := by
  have represent {queue : ReferenceWorkQueue.State}
      (links : queue.TaskLinkedOn task.occurrence (task.groups.map Execution.DeliveryNode.ref))
      (owned : ∃ owner ∈ task.groups, ∃ group, queue.groupNode? owner.ref = some group)
      : RecordTargetRepresented queue (.task task.occurrence) := by
    obtain ⟨owner, member, group, found⟩ := owned
    exact .task found (links group (List.mem_of_find?_eq_some found)
      (List.mem_map.mpr ⟨owner, member, (ReferenceWorkQueue.State.groupNode?_ref found).symm⟩))
  have removedLinks := links.removeOtherTask failed different
  have removedOwned : ∃ owner ∈ task.groups, ∃ group,
      (state.queue.removeTask failed).groupNode? owner.ref = some group := by
    obtain ⟨owner, member, group, found⟩ := owned
    cases live : (state.queue.removeTask failed).groupNode? owner.ref with
    | some current => exact ⟨owner, member, current, live⟩
    | none =>
        have present : owner.ref ∈ state.queue.groupNodes.map (fun node => node.group.node.ref) :=
          List.mem_map.mpr ⟨group, List.mem_of_find?_eq_some found,
            ReferenceWorkQueue.State.groupNode?_ref found⟩
        have same : (state.queue.removeTask failed).groupNodes.map (fun node => node.group.node.ref)
            = state.queue.groupNodes.map (fun node => node.group.node.ref) := by
          simp only [ReferenceWorkQueue.State.removeTask, List.map_map]; rfl
        rw [← same] at present
        exact False.elim
          ((ReferenceWorkQueue.State.groupNode?_eq_none_iff _ _).mp live present)
  unfold State.taskFailure
  split
  · exact .inl (represent links owned)
  · dsimp only
    split
    · exact .inl (represent removedLinks removedOwned)
    · rcases failureFold_unsettledTask errors _
          ({ state with queue := state.queue.removeTask failed }, [], [])
          (frame.removeTask failed) (forest.removeTask failed) task catalogue
          removedLinks removedOwned List.nodup_nil with kept | requested
      · exact .inl (represent kept.1 kept.2)
      · exact .inr (List.mem_flatMap.mpr ⟨.task task.occurrence, requested, List.mem_cons_self⟩)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
