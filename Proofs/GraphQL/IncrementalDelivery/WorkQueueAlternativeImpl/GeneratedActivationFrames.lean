import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationActivationSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskReplay

/-! Source settlement derives structural evidence before delayed cached group startup. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

private theorem forest_of_groupNodes {queue before : ReferenceWorkQueue.State} {parents}
    (same : queue.groupNodes = before.groupNodes) (forest : before.RemovalForest parents)
    : queue.RemovalForest parents := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ReferenceWorkQueue.State.ChildGroupsUnique, same] using forest.uniqueChildren
  · simpa only [ReferenceWorkQueue.State.ChildLinksCanonical, same] using forest.canonical
  · intro parent child memberParent memberChild linked
    rw [same] at memberParent memberChild
    exact forest.increasing memberParent memberChild linked

/-- The exact settlement projection derives activation evidence from eager source frames.
Active-task completion is identified before any released group starts. Cached failure
removal may occur afterwards, so its endpoint is not used as a premise.
-/
theorem State.taskSuccess_activationFrame {state : State} {work settled}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (present : state.queue.RootGroupsPresent)
    (accounting : state.queue.PendingAccounting work settled) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (node : ReferenceWorkQueue.TaskNode)
    (found : state.queue.taskNode? occurrence = some node) (fresh : occurrence ∉ settled)
    (known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (childFresh : ∀ task ∈ result.work.tasks, task.occurrence ∉ occurrence :: settled)
    (startup
      : ∃ parents,
          (referenceTaskSuccessReleased state.queue occurrence result
            node).1.TaskOwnerFrame
            work
          ∧ (referenceTaskSuccessReleased state.queue occurrence result
              node).1.RemovalForest
              parents)
    : let stored : State :=
        {
          state with
            queue := state.queue.putTaskNode {node with value := some result.value}
        }
      let registered := stored.maybeIntegrateWork result.work (some occurrence)
      let released :=
        node.task.groups.foldl ReferenceWorkQueue.successGroupStep
          (registered.1.queue, [], {})
      ∃ parents,
        ActivationFrame {registered.1 with queue := released.1} registered.2 work
          parents := by
  intro stored registered released
  have projection := state.taskSuccess_settlementProjection generated present accounting occurrence
    result node found fresh known childFresh
  obtain ⟨parents, owners, forest⟩ := startup
  have registeredMatch := stored.maybeIntegrateWork_registeredTasksMatch accounting.matching
    result.work known (some occurrence)
  have catalogue := ReferenceWorkQueue.successGroupFold_tasks node.task.groups
    (registered.1.queue, [], {})
  have matching : released.1.RegisteredTasksMatch work := by
    intro task member
    rw [catalogue] at member
    exact registeredMatch task member
  have members : registered.2.activeTasks.Subset released.1.tasks := by
    intro task member
    rw [catalogue]
    change task ∈ (stored.maybeIntegrateWork result.work (some occurrence)).1.queue.tasks
    rw [State.maybeIntegrateWork_tasks stored result.work (some occurrence)]
    exact List.mem_append_right _
      (stored.maybeIntegrateWork_activeTasks result.work (some occurrence) member)
  have starts := activateRegisteredTasks_eq_startTasks matching registered.2.activeTasks members
  have phase := congrArg Prod.fst projection
  have activeEq : registered.2.activeTasks.foldl
      (fun current task => current.startTask task.occurrence) released.1 =
      (referenceTaskSuccessReleased state.queue occurrence result node).1 := by
    rw [← starts]
    exact phase
  have groups : released.1.groupNodes =
      (referenceTaskSuccessReleased state.queue occurrence result node).1.groupNodes := by
    have same := congrArg ReferenceWorkQueue.State.groupNodes phase
    rw [activateRegisteredTasks_nodes] at same
    exact same
  exact ⟨parents, by rw [activeEq]; exact owners, forest_of_groupNodes groups forest⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
