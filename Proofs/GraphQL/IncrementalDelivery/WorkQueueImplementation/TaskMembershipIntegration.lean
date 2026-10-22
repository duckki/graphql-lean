import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskMembershipAbsence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage

/-! Registration preserves absence when the supplied task chunk does not reuse an identity. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

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
  have appended : ({ queue with
      groupNodes := queue.groupNodes ++ [({ group } : GroupNode)] } : State).TaskMembershipAbsent occurrence := by
    intro node member
    rcases List.mem_append.mp member with old | added
    · exact absent node old
    · cases List.mem_singleton.mp added
      simp
  unfold State.addGroup
  split
  · exact absent
  · split
    · exact appended
    · split
      · split <;> exact absent
      · rename_i node found
        exact appended.putGroupNode _ (absent node (List.mem_of_find?_eq_some found))

/-- Recursive installation preserves absent task memberships. -/
theorem State.TaskMembershipAbsent.addGroups {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (groups : List Group)
    : (queue.addGroups groups).1.TaskMembershipAbsent occurrence := by
  exact State.addGroups_preserves (fun current => current.TaskMembershipAbsent occurrence) groups
    (fun _ group _ valid => valid.addGroup group) queue absent

/-- Adding a different task cannot reintroduce the excluded occurrence.
Witness: each contributor keeps its old list or appends only the fresh task's identity;
optional task-node creation does not change group memberships.
-/
theorem State.TaskMembershipAbsent.addTask {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (task : Task)
    (different : occurrence ≠ task.occurrence)
    : (queue.addTask task).TaskMembershipAbsent occurrence := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
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
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
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

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
