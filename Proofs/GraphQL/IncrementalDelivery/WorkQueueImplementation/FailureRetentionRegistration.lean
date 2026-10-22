import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipSoundness

/-! Registration and activation preserve the rejected tasks of surviving owners. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem fold_preserves {α β : Type} (property : β → Prop)
    (step : β → α → β) (items : List α)
    (preserved : ∀ state item, property state → property (step state item))
    (state : β) (valid : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact valid
  | cons item rest ih => exact ih _ (preserved state item valid)

/-- A fresh group has no earlier failed contributor; old records remain untouched. -/
theorem State.RetainedFailures.addGroup {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (group : Group)
    : (queue.addGroup group).RetainedFailures work failed := by
  unfold State.addGroup
  split
  · exact prior
  · rename_i fresh
    have absent : group.node.ref ∉ queue.registeredGroups := by
      simp only [Bool.or_eq_true, List.contains_iff_mem, not_or] at fresh
      exact fresh.1
    have freshRefs : ∀ ref, ref ∉ queue.registeredGroups ++ [group.node.ref] →
        ∀ occurrence ∈ failed, ∀ owners, TaskHasOwners work occurrence owners → ref ∉ owners :=
      fun ref unregistered => prior.fresh ref
        (fun old => unregistered (List.mem_append_left _ old))
    dsimp only
    split
    · exact ⟨prior.retained, freshRefs⟩
    · refine ⟨?_, freshRefs⟩
      intro occurrence recorded owners known node member owner
      rcases List.mem_append.mp member with old | new
      · exact prior.retained occurrence recorded owners known node old owner
      · cases List.mem_singleton.mp new
        exact False.elim (prior.fresh group.node.ref absent occurrence recorded owners known owner)

/-- Group registration and parent linking preserve failed task retention. -/
theorem State.RetainedFailures.addGroups {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (unique : queue.GroupRefsUnique)
    (groups : List Group)
    : (queue.addGroups groups).1.RetainedFailures work failed := by
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref && (queue.groupNode? group.node.ref).isNone)
  let property (current : State) := current.GroupRefsUnique ∧ current.RetainedFailures work failed
  have registered := fold_preserves property State.addGroup fresh
    (fun _ group valid => ⟨valid.1.addGroup group, valid.2.addGroup group⟩) queue ⟨unique, prior⟩
  let link (current : State) (group : Group) :=
    match group.parent with
    | none => current
    | some parent => match current.groupNode? parent with
      | none => current
      | some node =>
          let children := if node.childGroups.contains group.node.ref then node.childGroups
            else node.childGroups ++ [group.node.ref]
          current.putGroupNode { node with childGroups := children }
  have linked (current : State) (group : Group) (valid : property current)
      : property (link current group) := by
    unfold link
    split
    · exact valid
    · split
      · exact valid
      · rename_i node found
        exact ⟨valid.1.putGroupNode _, valid.2.putGroupNodeSameTasks valid.1 node
          (List.mem_of_find?_eq_some found) _ rfl rfl⟩
  exact (fold_preserves property link fresh linked _ registered).2

/-- Appending task nodes leaves every existing first-match lookup unchanged. -/
private theorem State.RetainedFailures.appendTaskNodes {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (nodes : List TaskNode)
    : ({ queue with taskNodes := queue.taskNodes ++ nodes }).RetainedFailures work
        failed := by
  refine ⟨?_, prior.fresh⟩
  intro occurrence recorded owners known group member owner
  obtain ⟨listed, task, found, rejected, contributes⟩ :=
    prior.retained occurrence recorded owners known group member owner
  refine ⟨listed, task, ?_, rejected, contributes⟩
  change (queue.taskNodes ++ nodes).find? _ = _
  simp only [State.taskNode?] at found
  rw [List.find?_append, found]
  rfl

/-- Adding a task only grows group memberships and may append an unrejected task node. -/
theorem State.RetainedFailures.addTask {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (unique : queue.GroupRefsUnique)
    (task : Task)
    : (queue.addTask task).RetainedFailures work failed := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node => if node.tasks.contains task.occurrence then current
      else current.putGroupNode
        { node with
          tasks := node.tasks ++ [task.occurrence]
          pending := node.pending + 1 }
  let property (current : State) := current.GroupRefsUnique ∧ current.RetainedFailures work failed
  have preserved (current : State) (group : Execution.DeliveryNode) (valid : property current)
      : property (step current group) := by
    unfold step
    split
    · exact valid
    · rename_i node found
      split
      · exact valid
      · exact ⟨valid.1.putGroupNode _, valid.2.putGroupNodeTasksGrow valid.1 node
          (List.mem_of_find?_eq_some found) _ rfl (List.subset_append_left _ _)⟩
  have folded := (fold_preserves property step task.groups preserved
    { queue with tasks := queue.tasks ++ [task] } ⟨unique, prior⟩).2
  dsimp only [State.addTask]
  split
  · exact folded.appendTaskNodes [{ task }]
  · exact folded

/-- Stream registration changes only child-stream metadata on a present producer. -/
theorem State.RetainedFailures.addStreams {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (streams : List Stream)
    (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.RetainedFailures work failed := by
  dsimp only [State.addStreams]
  split
  · exact prior
  · split
    · exact prior
    · rename_i node found
      exact prior.putTaskNode found _ rfl (fun rejected => rejected)

/-- Child integration preserves earlier failed contributors and fresh-ref exclusion. -/
theorem State.RetainedFailures.maybeIntegrateWork {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (unique : queue.GroupRefsUnique)
    (more : Work) (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork more producer).1.RetainedFailures work failed := by
  let property (current : State) := current.GroupRefsUnique ∧ current.RetainedFailures work failed
  have tasks := fold_preserves property State.addTask more.tasks
    (fun _ task valid => ⟨valid.1.addTask task, valid.2.addTask valid.1 task⟩)
    (queue.addGroups more.groups).1 ⟨unique.addGroups more.groups, prior.addGroups unique more.groups⟩
  exact tasks.2.addStreams more.streams producer

/-- Pruning removes only group shells and leaves task computations unchanged. -/
theorem State.RetainedFailures.pruneEmptyGroups {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.RetainedFailures work failed := by
  have loop (fuel : Nat) (current : State) (remaining kept)
      (valid : current.RetainedFailures work failed)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.RetainedFailures work failed := by
    induction fuel generalizing current remaining kept with
    | zero => exact valid
    | succ fuel ih =>
        cases remaining with
        | nil => exact valid
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ valid
            · split
              · exact ih _ _ _ (valid.filterGroups _)
              · exact ih _ _ _ valid
  exact loop _ queue groups [] prior

/-- Starting a task preserves old first-match computations. -/
theorem State.RetainedFailures.startTask {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (occurrence : Occurrence)
    : (queue.startTask occurrence).RetainedFailures work failed := by
  unfold State.startTask
  split
  · exact prior
  · split
    · exact prior
    · exact prior.appendTaskNodes _

/-- Starting a group preserves every retained rejection, including dormant shared tasks. -/
theorem State.RetainedFailures.startGroup {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (ref : NodeRef)
    : (queue.startGroup ref).RetainedFailures work failed := by
  unfold State.startGroup
  split
  · exact prior
  · exact fold_preserves (fun current => current.RetainedFailures work failed)
      State.startTask _ (fun _ occurrence valid => valid.startTask occurrence) _ prior

/-- Stream activation does not change group membership or retained task computations. -/
theorem State.RetainedFailures.startStream {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (ref : NodeRef)
    : (queue.startStream ref).RetainedFailures work failed := by
  unfold State.startStream
  split <;> exact prior

/-- Activation reuses retained task rejections without changing the failure inventory. -/
theorem State.RetainedFailures.startNewWork {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (more : NewWork)
    : (queue.startNewWork more).RetainedFailures work failed := by
  dsimp only [State.startNewWork]
  apply fold_preserves (fun current => current.RetainedFailures work failed)
    State.startStream _ (fun _ ref valid => valid.startStream ref)
  apply fold_preserves (fun current => current.RetainedFailures work failed)
    State.startGroup _ (fun _ ref valid => valid.startGroup ref)
  exact prior

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
