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
    have registered : ({ queue with
        registeredGroups := queue.registeredGroups ++ [group.node.ref] } : State).RetainedFailures
          work failed := ⟨prior.retained, freshRefs⟩
    have appended : ({ queue with
        registeredGroups := queue.registeredGroups ++ [group.node.ref],
        groupNodes := queue.groupNodes ++ [({ group } : GroupNode)] } : State).RetainedFailures
          work failed := by
      refine ⟨?_, freshRefs⟩
      intro occurrence recorded owners known node member owner
      rcases List.mem_append.mp member with old | new
      · exact prior.retained occurrence recorded owners known node old owner
      · cases List.mem_singleton.mp new
        exact False.elim (prior.fresh group.node.ref absent occurrence recorded owners known owner)
    split
    · exact appended
    · split
      · split <;> exact registered
      · rename_i parent found
        refine ⟨?_, freshRefs⟩
        intro occurrence recorded owners known node member owner
        obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
        by_cases selected : old.group.node.ref = parent.group.node.ref
        · simp only [selected, BEq.rfl, ite_true] at same
          subst node
          exact prior.retained occurrence recorded owners known parent
            (List.mem_of_find?_eq_some found) owner
        · simp only [beq_eq_false_iff_ne.mpr selected, Bool.false_eq_true, ite_false] at same
          subst node
          exact appended.retained occurrence recorded owners known old oldMember owner

/-- Recursive group registration preserves failed task retention. -/
theorem State.RetainedFailures.addGroups {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (unique : queue.GroupRefsUnique)
    (groups : List Group)
    : (queue.addGroups groups).1.RetainedFailures work failed := by
  exact (State.addGroups_preserves
    (fun current => current.GroupRefsUnique ∧ current.RetainedFailures work failed) groups
    (fun _ group _ valid => ⟨valid.1.addGroup group, valid.2.addGroup group⟩)
    queue ⟨unique, prior⟩).2

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
    (queue.addGroups more.groups).1
      ⟨unique.addGroups more.groups, prior.addGroups unique more.groups⟩
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

/-- Exposing more rejected outcomes never clears a retained rejection. -/
theorem State.RetainedFailures.cacheTaskFailures {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).RetainedFailures work failed := by
  induction available generalizing queue with
  | nil => exact prior
  | cons entry rest ih =>
      simp only [State.cacheTaskFailures, List.foldl_cons]
      split
      · exact ih prior
      · rename_i node found
        exact ih (prior.putTaskNode found { node with rejection := some entry.2 } rfl
          (fun _ => rfl))

/-- Starting a task preserves old first-match computations. -/
theorem State.RetainedFailures.startTask {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (occurrence : Occurrence)
    (available : List (Occurrence × Nat) := [])
    : (queue.startTask occurrence available).RetainedFailures work failed := by
  unfold State.startTask
  split
  · exact prior
  · split
    · exact prior
    · exact prior.appendTaskNodes _

/-- Starting a group preserves every retained rejection, including dormant shared tasks. -/
theorem State.RetainedFailures.startGroup {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.RetainedFailures work failed := by
  have cached := prior.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · exact fold_preserves (fun current : State => current.RetainedFailures work failed)
        (fun current occurrence => current.startTask occurrence available) _
        (fun _ occurrence valid => valid.startTask occurrence available) _ cached
    · exact cached.removeGroup _

/-- Stream activation does not change group membership or retained task computations. -/
theorem State.RetainedFailures.startStream {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (ref : NodeRef)
    : (queue.startStream ref).RetainedFailures work failed := by
  unfold State.startStream
  split <;> exact prior

/-- Activation reuses retained task rejections without changing the failure inventory. -/
theorem State.RetainedFailures.startNewWork {queue : State} {work failed}
    (prior : queue.RetainedFailures work failed) (more : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork more available).1.RetainedFailures work failed := by
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (valid : acc.1.RetainedFailures work failed)
      : (refs.foldl
          (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref available
            (next, failures ++ queued)) acc).1.RetainedFailures work failed := by
    induction refs generalizing acc with
    | nil => exact valid
    | cons ref rest ih => exact ih _ (valid.startGroup ref available)
  unfold State.startNewWork
  exact fold_preserves (fun current : State => current.RetainedFailures work failed)
    State.startStream _ (fun _ ref valid => valid.startStream ref) _
    (groups (more.newGroups.map Execution.DeliveryNode.ref)
      (
        {
          queue with
            rootGroups :=
              queue.rootGroups ++ more.newGroups.map Execution.DeliveryNode.ref
        },
        []
      ) prior)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
