import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublishedMemberships
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerOrder

/-! Fresh source child work cannot reinstall a previously published group membership. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Group metadata and fresh task integration preserve publication exclusions
-----------------------------------------------------------------------------------------

/-- Replacing a started task changes no group membership list.
Witness: the update modifies only the task-node map.
-/
theorem State.TaskMembershipAbsent.putTaskNode {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (updated : TaskNode)
    : (queue.putTaskNode updated).TaskMembershipAbsent occurrence :=
  absent

/-- Replacing a group preserves exclusion when its replacement also omits the occurrence.
Witness: every output record is unchanged or is the supplied replacement.
-/
theorem State.TaskMembershipAbsent.putGroupNode {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (updated : GroupNode)
    (missing : occurrence ∉ updated.tasks)
    : (queue.putGroupNode updated).TaskMembershipAbsent occurrence := by
  intro node member
  obtain ⟨old, prior, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact missing
  · subst node; exact absent old prior

/-- Registering a new empty group cannot restore a delivered membership.
Witness: skipped registration is unchanged; accepted registration appends an empty record.
-/
theorem State.TaskMembershipAbsent.addGroup {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (group : Group)
    : (queue.addGroup group).TaskMembershipAbsent occurrence := by
  unfold State.addGroup
  split
  · exact absent
  · split
    · exact absent
    · intro node member
      rcases List.mem_append.mp member with old | added
      · exact absent node old
      · obtain rfl := List.mem_singleton.mp added
        simp

/-- Registration and child-link installation preserve absent task memberships.
Witness: new groups start empty, and linking updates only the child list.
-/
theorem State.TaskMembershipAbsent.addGroups {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (groups : List Group)
    : (queue.addGroups groups).1.TaskMembershipAbsent occurrence := by
  let link (current : State) (group : Group) :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.key then node.childGroups
              else node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have registration (more : List Group) (current : State)
      (prior : current.TaskMembershipAbsent occurrence)
      : (more.foldl State.addGroup current).TaskMembershipAbsent occurrence := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih => exact ih _ (prior.addGroup group)
  have links (more : List Group) (current : State)
      (prior : current.TaskMembershipAbsent occurrence)
      : (more.foldl link current).TaskMembershipAbsent occurrence := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        unfold link
        split
        · exact prior
        · split
          · exact prior
          · rename_i node found
            exact prior.putGroupNode _ (prior node (List.mem_of_find?_eq_some found))
  exact links _ _ (registration _ queue absent)

/-- Adding a different task cannot reintroduce the excluded occurrence.
Witness: each contributor keeps its old list or appends only the fresh task's identity;
optional task-node creation does not change group memberships.
-/
theorem State.TaskMembershipAbsent.addTask {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (task : Task)
    (different : occurrence ≠ task.occurrence)
    : (queue.addTask task).TaskMembershipAbsent occurrence := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have loop (groups : List Execution.DeliveryNode) (current : State)
      (prior : current.TaskMembershipAbsent occurrence)
      : (groups.foldl step current).TaskMembershipAbsent occurrence := by
    induction groups generalizing current with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        unfold step
        split
        · exact prior
        · rename_i node found
          split
          · exact prior
          · exact prior.putGroupNode _ (by
              simpa only [List.mem_append, List.mem_singleton, not_or] using
                And.intro (prior node (List.mem_of_find?_eq_some found)) different)
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let current := task.groups.foldl step registered
  have final := loop task.groups registered absent
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
    { current with taskNodes := current.taskNodes ++ [({ task } : TaskNode)] }
    else current).TaskMembershipAbsent occurrence
  split <;> exact final

/-- Stream registration changes no group membership, including parent-linked streams.
Witness: both branches modify only the stream registry or a task's child-stream list.
-/
theorem State.TaskMembershipAbsent.addStreams {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.TaskMembershipAbsent occurrence := by
  unfold State.addStreams
  split
  · exact absent
  · dsimp only
    split <;> exact absent

/-- Integrating a chunk with no excluded task preserves membership exclusion.
Witness: group registration starts empty; each new task has a different occurrence, and
stream registration changes no group task list. No executable admission premise is used.
-/
theorem State.TaskMembershipAbsent.maybeIntegrateWork {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (work : Work)
    (fresh : ∀ task ∈ work.tasks, occurrence ≠ task.occurrence)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.TaskMembershipAbsent occurrence := by
  have loop (more : List Task) (included : more.Subset work.tasks) (current : State)
      (prior : current.TaskMembershipAbsent occurrence)
      : (more.foldl State.addTask current).TaskMembershipAbsent occurrence := by
    induction more generalizing current with
    | nil => exact prior
    | cons task rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (prior.addTask task (fresh task (included List.mem_cons_self)))
  exact (loop work.tasks (List.Subset.refl _) _ (absent.addGroups work.groups)).addStreams
    work.streams parentTask

-----------------------------------------------------------------------------------------
-- The existing source laws derive freshness against the actual publication inventory
-----------------------------------------------------------------------------------------

/-- A matched fresh input cannot offer a child whose value was already published.
Witness: child source order excludes earlier settlement of that occurrence; every entry
of the exact object inventory has an earlier source-success witness. This derives the
integration exclusion from existing source semantics, not an added freshness law.
-/
theorem GraphEvent.MatchesWork.childTask_not_published
    {work before event} {queue : State} {published : List ObjectPublication} {task : Task}
    (matching : GraphEvent.MatchesWork work event) (valid : ValidGraphEvents work before)
    (fresh : event.Fresh before)
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (member : task ∈ event.childTasks)
    : task.occurrence ∉ published.map Prod.fst := by
  intro emitted
  obtain ⟨publication, listed, same⟩ := List.mem_map.mp emitted
  exact matching.childTasks_unsettled valid fresh member
    (same ▸ (inventory.provenance publication listed).identity)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
