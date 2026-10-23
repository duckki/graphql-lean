import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLookupUpdates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication

/-! Integration preserves existing computation lookups independently of stored values. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics

/-- Registering another task preserves every successful task-node lookup.
Witness: group updates leave the task map unchanged; any new node is appended after it.
-/
theorem State.addTask_taskNode?_of_some {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (task : Task)
    : (queue.addTask task).taskNode? occurrence = some node := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some groupNode =>
        if groupNode.tasks.contains task.occurrence then current
        else current.putGroupNode
          { groupNode with
            tasks := groupNode.tasks ++ [task.occurrence]
            pending := groupNode.pending + 1 }
  have unchanged (groups : List Execution.DeliveryNode) (current : State)
      : (groups.foldl step current).taskNodes = current.taskNodes := by
    induction groups generalizing current with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih]
        dsimp only [step]
        split
        · rfl
        · split <;> rfl
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have same : current.taskNodes = queue.taskNodes := unchanged _ _
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
        { current with taskNodes := current.taskNodes ++ [{ task }] }
      else current).taskNode? occurrence = some node
  split
  · change queue.taskNodes.find? _ = _ at found
    simp only [State.taskNode?, List.find?_append, same, found]
    rfl
  · simpa only [State.taskNode?, same] using found

/-- Integrating child work retains every lookup except its stream-attachment producer.
Witness: group registration leaves tasks unchanged, task registration appends new nodes,
and stream attachment can replace only the explicitly supplied producer.
-/
theorem State.maybeIntegrateWork_lookup_other {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (work : Work)
    (producer : Option Occurrence := none)
    (different : producer ≠ some occurrence := by simp)
    : (queue.maybeIntegrateWork work producer).1.taskNode? occurrence = some node := by
  have grouped : (queue.addGroups work.groups).1.taskNode? occurrence = some node := by
    simpa only [State.taskNode?, State.addGroups_taskNodes] using found
  have loop (tasks : List Task) (current : State)
      (prior : current.taskNode? occurrence = some node)
      : (tasks.foldl State.addTask current).taskNode? occurrence = some node := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (State.addTask_taskNode?_of_some prior task)
  have integrated := loop work.tasks _ grouped
  unfold State.maybeIntegrateWork
  dsimp only
  cases producer with
  | none => exact integrated
  | some parent =>
      simp only [State.addStreams]
      split
      · exact integrated
      · rename_i owner lookup
        exact State.putTaskNode_lookup_other integrated _ (by
          intro same
          exact different (congrArg some ((State.taskNode?_some lookup).2.symm.trans same)))

/-- Producer attachment retains the task descriptor and value while extending stream refs.
Witness: group/task registration preserves its first lookup; the final stream operation
only replaces that producer's child-stream list. No well-formedness premise is required.
-/
theorem State.maybeIntegrateWork_lookup_producer {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (work : Work)
    : ∃ next,
        (queue.maybeIntegrateWork work (some occurrence)).1.taskNode? occurrence
          = some next
        ∧ next.task = node.task
        ∧ next.value = node.value := by
  have grouped : (queue.addGroups work.groups).1.taskNode? occurrence = some node := by
    simpa only [State.taskNode?, State.addGroups_taskNodes] using found
  have loop (tasks : List Task) (current : State)
      (prior : current.taskNode? occurrence = some node)
      : (tasks.foldl State.addTask current).taskNode? occurrence = some node := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (State.addTask_taskNode?_of_some prior task)
  have integrated := loop work.tasks _ grouped
  unfold State.maybeIntegrateWork
  dsimp only
  simp only [State.addStreams]
  split
  · rename_i impossible
    have contradiction : some node = none := integrated.symm.trans impossible
    cases contradiction
  · rename_i current lookup
    have equal : current = node := Option.some.inj (lookup.symm.trans integrated)
    subst current
    refine ⟨_, State.putTaskNode_lookup_same integrated _ (State.taskNode?_some found).2,
      rfl, rfl⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
