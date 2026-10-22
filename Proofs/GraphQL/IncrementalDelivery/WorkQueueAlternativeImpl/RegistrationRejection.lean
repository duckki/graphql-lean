import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationHostEffects
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRejections

/-! Rejected-task disposal follows the temporary registration projection, not a second
owner scan. These local facts are independent of native acquisition observations.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (Occurrence)

-----------------------------------------------------------------------------------------
-- Owner absence during one registration scope constructs the rejected projection
-----------------------------------------------------------------------------------------

/-- Missing contributors cause no owner update and classify the task as rejected. -/
theorem State.addTask_rejected_of_missing (state : State) (task : ReferenceWorkQueue.Task)
    (missing : ∀ owner ∈ task.groups, state.queue.groupNode? owner.ref = none)
    : (state.addTask task).2 = .rejected := by
  let initial : ReferenceWorkQueue.State × Bool × Bool :=
    ({ state.queue with tasks := state.queue.tasks ++ [task] }, false, false)
  have loop (owners : List Execution.DeliveryNode) (included : owners.Subset task.groups)
      : owners.foldl (classifyOwner task) initial = initial := by
    induction owners with
    | nil => rfl
    | cons owner rest ih =>
        have absent : initial.1.groupNode? owner.ref = none := missing owner (included List.mem_cons_self)
        rw [List.foldl_cons]
        simp only [classifyOwner, absent]
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member))
  change (if (task.groups.foldl (classifyOwner task) initial).2.2 then TaskRegistration.active
    else if (task.groups.foldl (classifyOwner task) initial).2.1 then
      TaskRegistration.registered else TaskRegistration.rejected) = TaskRegistration.rejected
  rw [loop task.groups (List.Subset.refl _)]
  rfl

private theorem registerTasks_includesKeys
    (tasks : List ReferenceWorkQueue.Task)
    (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
    : (acc.1.queue.groupNodes.map (fun node => node.group.node.ref)).Subset
        ((tasks.foldl registerTaskStep acc).1.queue.groupNodes.map
          (fun node => node.group.node.ref)) := by
  induction tasks generalizing acc with
  | nil => exact List.Subset.refl _
  | cons task rest ih =>
      have next : (acc.1.queue.groupNodes.map (fun node => node.group.node.ref)).Subset
          ((acc.1.addTask task).1.queue.groupNodes.map (fun node => node.group.node.ref)) := by
        have groups := congrArg ReferenceWorkQueue.State.groupNodes (acc.1.addTask_registrationCore task)
        change (acc.1.addTask task).1.queue.groupNodes = (acc.1.queue.addTask task).groupNodes at groups
        rw [groups]
        exact ReferenceWorkQueue.State.addTask_includesRefs _ _
      have forget : (registerTaskStep acc task).1 = (acc.1.addTask task).1 := by
        unfold registerTaskStep
        dsimp only
        split <;> rfl
      exact next.trans (by rw [← forget]; exact ih _)

private theorem registerTasks_keepsRejected
    (tasks : List ReferenceWorkQueue.Task)
    (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
    : acc.2.2.Subset (tasks.foldl registerTaskStep acc).2.2 := by
  induction tasks generalizing acc with
  | nil => exact List.Subset.refl _
  | cons task rest ih =>
      apply List.Subset.trans (l₂ := (registerTaskStep acc task).2.2) _ (ih _)
      unfold registerTaskStep
      dsimp only
      split
      · exact List.Subset.refl _
      · exact List.Subset.refl _
      · exact List.subset_append_left _ _

private theorem registerTasks_rejected
    (tasks : List ReferenceWorkQueue.Task)
    (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
    (task : ReferenceWorkQueue.Task) (member : task ∈ tasks)
    (missing
      : ∀ owner ∈ task.groups,
          (tasks.foldl registerTaskStep acc).1.queue.groupNode? owner.ref = none)
    : task ∈ (tasks.foldl registerTaskStep acc).2.2 := by
  induction tasks generalizing acc with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst first
        have absent : ∀ owner ∈ task.groups, acc.1.queue.groupNode? owner.ref = none := by
          intro owner listed
          apply (acc.1.queue.groupNode?_eq_none_iff owner.ref).mpr
          intro present
          have final := registerTasks_includesKeys (task :: rest) acc present
          exact ((ReferenceWorkQueue.State.groupNode?_eq_none_iff _ _).mp
            (missing owner listed)) final
        have rejected := State.addTask_rejected_of_missing acc.1 task absent
        apply registerTasks_keepsRejected rest (registerTaskStep acc task)
        simp only [registerTaskStep, rejected]
        exact List.mem_append_right _ List.mem_cons_self
      · exact ih (registerTaskStep acc first) later missing

/-- Within one scope, a returned task with no registered contributor is in the actual
rejected projection. This fact is about registration before pruning and release.
-/
theorem State.maybeIntegrateWork_rejected {state : State} (work : ReferenceWorkQueue.Work)
    (producer : Option Occurrence := none) (task : ReferenceWorkQueue.Task)
    (returned : task ∈ work.tasks)
    (missing
      : ∀ owner ∈ task.groups,
          (state.maybeIntegrateWork work producer).1.queue.groupNode? owner.ref = none)
    : task ∈ (state.maybeIntegrateWork work producer).2.rejectedTasks := by
  let initial : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task :=
    ({ state with queue := (state.queue.addGroups work.groups).1 }, [], [])
  let registered := work.tasks.foldl registerTaskStep initial
  change task ∈ registered.2.2
  apply registerTasks_rejected work.tasks initial task returned
  intro owner listed
  have known := missing owner listed
  change (registered.1.queue.addStreams work.streams producer).1.groupNode? owner.ref = none at known
  cases producer with
  | none => exact known
  | some parent =>
      simp only [ReferenceWorkQueue.State.addStreams] at known
      split at known <;> exact known

-----------------------------------------------------------------------------------------
-- The actual projection licenses inline cleanup without evaluating a rejected task
-----------------------------------------------------------------------------------------

/-- Disposal includes an unrejected computation identity, even if unstarted. -/
theorem State.disposeRejectedTasks_contains (state : State) (integrated : IntegratedWork)
    (targets : List CleanupTarget) (task : ReferenceWorkQueue.Task)
    (rejected : task ∈ integrated.rejectedTasks)
    (unrejected
      : (state.queue.taskNode? task.occurrence).any (fun node => node.rejection.isSome)
        = false)
    : .task task.occurrence ∈ state.disposeRejectedTasks integrated targets := by
  rw [State.disposeRejectedTasks, mem_uniqueCleanupTargets]
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨task, rejected, ?_⟩
  simp only [State.cancelTask, unrejected, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_append_left _ List.mem_cons_self

/-- Activation's cleanup targets retain every rejected computation of the scope. -/
theorem State.startNewWork_rejected (state : State) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget)
    (running : state.stopped = false) (task : ReferenceWorkQueue.Task)
    (rejected : task ∈ integrated.rejectedTasks)
    {settled : List Occurrence}
    (prior : state.queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (fresh : task.occurrence ∉ settled)
    : .task task.occurrence ∈ (state.startNewWork roots integrated targets).2 := by
  simp only [State.startNewWork, running, Bool.false_eq_true, ↓reduceIte]
  apply State.disposeRejectedTasks_contains _ integrated targets task rejected
  have nodes (streams : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
      : (streams.foldl (fun (current : ReferenceWorkQueue.State) (stream : Execution.DeliveryNode) => current.startStream stream.ref)
          queue).taskNodes = queue.taskNodes := by
    induction streams generalizing queue with
    | nil => rfl
    | cons stream rest ih =>
        rw [List.foldl_cons, ih]
        unfold ReferenceWorkQueue.State.startStream
        split <;> rfl
  have supported : (roots.newStreams.foldl (fun (current : ReferenceWorkQueue.State) (stream : Execution.DeliveryNode) => current.startStream stream.ref)
      { state.queue with rootGroups := state.queue.rootGroups
        ++ roots.newGroups.map Execution.DeliveryNode.ref }).TaskRejectionsSatisfy
          (fun occurrence _ => occurrence ∈ settled) := by
    intro node member errors failure
    rw [nodes] at member
    exact prior node member errors failure
  cases found
        : (roots.newStreams.foldl
            (fun (current : ReferenceWorkQueue.State) (stream : Execution.DeliveryNode) =>
              current.startStream stream.ref)
            {
              state.queue with
                rootGroups :=
                  state.queue.rootGroups ++ roots.newGroups.map Execution.DeliveryNode.ref
            }).taskNode?
            task.occurrence with
  | none => simp only [Option.any_none]
  | some node =>
      cases failed : node.rejection with
      | none => simp only [Option.any_some, failed, Option.isSome_none]
      | some errors =>
          exact False.elim (fresh ((ReferenceWorkQueue.State.taskNode?_some found).2 ▸
            supported node (List.mem_of_find?_eq_some found) errors failed))

/-- An accepted object's rejected projection emits its abort in that actual handler.
Owner settlement and the ready drain cannot hide the already accumulated target.
-/
theorem State.taskSuccess_rejected {state : State} {occurrence result node}
    (found : state.queue.taskNode? occurrence = some node)
    (running : state.stopped = false) (task : ReferenceWorkQueue.Task)
    {settled : List Occurrence}
    (prior : state.queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (fresh : task.occurrence ∉ settled)
    (rejected
      : task
        ∈ (({
                state with
                  queue :=
                    state.queue.putTaskNode { node with value := some result.value }
              }
            : State).maybeIntegrateWork
            result.work (some occurrence)).2.rejectedTasks)
    : .abortTask task.occurrence ∈ (state.taskSuccess occurrence result).2.2 := by
  let stored : State :=
    { state with queue := state.queue.putTaskNode { node with value := some result.value } }
  let registered := stored.maybeIntegrateWork result.work (some occurrence)
  let folded := node.task.groups.foldl ReferenceWorkQueue.successGroupStep (registered.1.queue, [], {})
  let starting : State := { registered.1 with queue := folded.1 }
  have guard : starting.stopped = false :=
    (State.maybeIntegrateWork_stopped stored result.work (some occurrence)).trans running
  have storedSupport : stored.queue.TaskRejectionsSatisfy
      (fun occurrence _ => occurrence ∈ settled) :=
    prior.putTaskNode _ (prior node (List.mem_of_find?_eq_some found))
  have registeredSupport := State.maybeIntegrateWork_taskRejections storedSupport
    result.work (some occurrence)
  have target := State.startNewWork_rejected starting folded.2.2 registered.2 [] guard task
    rejected (registeredSupport.successGroupFold node.task.groups) fresh
  let active := starting.startNewWork folded.2.2 registered.2 []
  have unique := State.startNewWork_targets_nodup starting folded.2.2 registered.2 [] List.nodup_nil
  have targetFinal : .task task.occurrence ∈ (active.1.drainReadyGroups active.2).2.2 :=
    (active.1.drainReadyGroups_targets active.2 unique).2.sublist.subset target
  rw [State.taskSuccess_eq state occurrence result node found]
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨.task task.occurrence, targetFinal, List.mem_cons_self⟩

/-- Registration-time owner absence, not an endpoint scan, constructs object abort. -/
theorem State.taskSuccess_ownerless_aborted {state : State} {occurrence result node}
    (found : state.queue.taskNode? occurrence = some node)
    (running : state.stopped = false) (task : ReferenceWorkQueue.Task)
    {settled : List Occurrence}
    (prior : state.queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (fresh : task.occurrence ∉ settled)
    (returned : task ∈ result.work.tasks)
    (missing
      : ∀ owner ∈ task.groups,
          (({
                state with
                  queue :=
                    state.queue.putTaskNode { node with value := some result.value }
              }
            : State).maybeIntegrateWork
            result.work (some occurrence)).1.queue.groupNode?
            owner.ref
          = none)
    : .abortTask task.occurrence ∈ (state.taskSuccess occurrence result).2.2 :=
  State.taskSuccess_rejected found running task prior fresh
    (State.maybeIntegrateWork_rejected result.work (some occurrence) task returned
      missing)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
