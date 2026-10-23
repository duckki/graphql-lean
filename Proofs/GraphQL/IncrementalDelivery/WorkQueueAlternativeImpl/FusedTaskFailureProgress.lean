import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedUnsettledTaskDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureResources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureTaskRetention

/-! Task ownership through the actual failed-owner fold. An unfinished task needs no
computation node: its complete memberships force disposal when its last owner is removed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (NodeRefs Occurrence)

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
    (unrejected
      : state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    : RecordTargetRepresented
        (state.handleGraphEvent (.taskFailure failed errors)).1.queue
        (.task task.occurrence)
      ∨ .abortTask task.occurrence
        ∈ (state.handleGraphEvent (.taskFailure failed errors)).2.2.1 := by
  have represent {queue : ReferenceWorkQueue.State}
      (links : queue.TaskLinkedOn task.occurrence (task.groups.map Execution.DeliveryNode.ref))
      (owned : ∃ owner ∈ task.groups, ∃ group, queue.groupNode? owner.ref = some group)
      (prior : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
      : RecordTargetRepresented queue (.task task.occurrence) := by
    obtain ⟨owner, member, group, found⟩ := owned
    exact .task found (links group (List.mem_of_find?_eq_some found)
      (List.mem_map.mpr ⟨owner, member, (ReferenceWorkQueue.State.groupNode?_ref found).symm⟩))
        prior.unrejected_lookup
  have finalUnrejected : (state.handleGraphEvent (.taskFailure failed
    errors)).1.queue.TaskRejectionsSatisfy
      (fun rejected _ => rejected ≠ task.occurrence) := by
    change (state.taskFailure failed errors).1.queue.TaskRejectionsSatisfy _
    have same : (state.taskFailure failed errors).1.queue =
        (state.queue.taskFailure failed errors).1 :=
      congrArg Prod.fst (state.taskFailure_projection frame forest failed errors)
    rw [same]
    exact unrejected.taskFailure failed errors (Ne.symm different)
  cases found : state.queue.taskNode? failed with
  | none =>
      simpa only [State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, State.taskFailure, found, List.flatMap_nil]
        using (Or.inl (represent links owned unrejected)
                : RecordTargetRepresented state.queue (.task task.occurrence)
                  ∨ .abortTask task.occurrence ∈ ([] : List HostEffect))
  | some node =>
      let stored : State :=
        { state with queue := state.queue.putTaskNode { node with rejection := some errors } }
      have storedFrame : stored.queue.TaskOwnerFrame work :=
        frame.putExistingTaskNode node (List.mem_of_find?_eq_some found)
          { node with rejection := some errors } rfl
      have storedForest : stored.queue.RemovalForest parents :=
        ⟨forest.uniqueChildren, forest.canonical, forest.increasing⟩
      have storedUnrejected : stored.queue.TaskRejectionsSatisfy
          (fun rejected _ => rejected ≠ task.occurrence) := by
        apply unrejected.putTaskNode
        intro count rejected
        exact (ReferenceWorkQueue.State.taskNode?_some found).2 ▸ Ne.symm different
      have outcome := failureFold_unsettledTask errors node.task.groups (stored, [], [])
        storedFrame storedForest task catalogue links owned List.nodup_nil storedUnrejected
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, State.taskFailure, found] at finalUnrejected ⊢
      rcases outcome with kept | requested
      · exact .inl (represent kept.1 kept.2 finalUnrejected)
      · exact .inr (List.mem_flatMap.mpr
          ⟨.task task.occurrence, requested, List.mem_cons_self⟩)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
