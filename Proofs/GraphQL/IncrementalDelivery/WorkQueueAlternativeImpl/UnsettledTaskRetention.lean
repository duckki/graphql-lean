import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IncomingTaskRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskRetention

/-! Retain the owners of uncompleted tasks through successful publication. Unlike
buffered-source retention, this requires no task node or stored value: a real membership
prevents empty-shell pruning, and pending accounting prevents premature publication.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (GroupNode)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode ExecutionGroupValue)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- A successful publication of other tasks preserves every live owner
-----------------------------------------------------------------------------------------

/-- Success cannot erase a linked task's owner if that task is outside the closing group.
This is the computation-independent counterpart of buffered-owner retention, using the
same executable flush and pruning fold. No cancellation or endpoint premise is supplied.
-/
theorem finishGroupSuccess_linkedOwner_present {queue : Kernel} {occurrence keys key}
    (links : queue.TaskLinkedOn occurrence keys) (group : GroupNode)
    (live : group ∈ queue.groupNodes) (unlisted : occurrence ∉ group.tasks)
    (contributes : key ∈ keys)
    (present : key ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    : key
      ∈ (queue.finishGroupSuccess group).1.groupNodes.map
          (fun node => node.group.node.ref) := by
  have different : key ≠ group.group.node.ref := by
    intro same
    exact unlisted (links group live (same ▸ contributes))
  have loop (tasks : List Occurrence) (included : tasks.Subset group.tasks)
      (acc : Kernel × List ExecutionGroupValue × NodeRefs) (linked : acc.1.TaskLinkedOn occurrence keys)
      : (tasks.foldl ReferenceWorkQueue.flushGroupTask acc).1.TaskLinkedOn occurrence keys
        ∧ (tasks.foldl ReferenceWorkQueue.flushGroupTask acc).1.groupNodes.map (fun node => node.group.node.ref)
          = acc.1.groupNodes.map (fun node => node.group.node.ref) := by
    induction tasks generalizing acc with
    | nil => exact ⟨linked, rfl⟩
    | cons chosen rest ih =>
        rw [List.foldl_cons]
        have nextLinks : (ReferenceWorkQueue.flushGroupTask acc chosen).1.TaskLinkedOn occurrence keys := by
          unfold ReferenceWorkQueue.flushGroupTask
          split
          · exact linked
          · exact linked.removeOtherTask chosen
              (fun same => unlisted (same.symm ▸ included List.mem_cons_self))
        have nextKeys : (ReferenceWorkQueue.flushGroupTask acc chosen).1.groupNodes.map
            (fun node => node.group.node.ref) = acc.1.groupNodes.map (fun node => node.group.node.ref) := by
          unfold ReferenceWorkQueue.flushGroupTask
          split
          · rfl
          · simp only [ReferenceWorkQueue.State.removeTask, List.map_map]; rfl
        obtain ⟨kept, same⟩ := ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (ReferenceWorkQueue.flushGroupTask acc chosen) nextLinks
        exact ⟨kept, same.trans nextKeys⟩
  let flushed := (group.tasks.foldl ReferenceWorkQueue.flushGroupTask (queue, [], [])).1
  obtain ⟨flushedLinks, flushedKeys⟩ := loop group.tasks (List.Subset.refl _) (queue, [], []) links
  let current : Kernel := { flushed with
    groupNodes := flushed.groupNodes.filter (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentLinks : current.TaskLinkedOn occurrence keys := by
    intro node member contributes
    exact flushedLinks node (List.mem_filter.mp member).1 contributes
  have currentOwner : key ∈ current.groupNodes.map (fun node => node.group.node.ref) := by
    rw [← flushedKeys] at present
    obtain ⟨owner, member, same⟩ := List.mem_map.mp present
    exact List.mem_map.mpr ⟨owner,
      List.mem_filter.mpr ⟨member, by simp [same, different]⟩, same⟩
  exact pruneEmptyGroups_linkedOwner_present currentLinks contributes currentOwner _

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
