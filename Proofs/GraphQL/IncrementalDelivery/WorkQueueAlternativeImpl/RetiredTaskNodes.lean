import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTaskRetirement

/-! A retired computation cannot be recreated by graph maintenance. Its missing node and
absent group memberships are structural facts, independent of notification consumption.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence)

/-- A previously started computation has lost both its node and every group membership. -/
structure State.RetiredTask (queue : State) (occurrence : Occurrence) : Prop where
  missing : queue.taskNode? occurrence = none
  unlinked : queue.TaskMembershipAbsent occurrence

/-- Existing started-task accounting identifies global retirement when its node is gone. -/
theorem State.StartedTaskDisposition.retired {queue occurrence}
    (disposition : State.StartedTaskDisposition queue occurrence)
    (missing : queue.taskNode? occurrence = none)
    : queue.RetiredTask occurrence :=
  ⟨missing, disposition.absent missing⟩

/-- A retired computation contributes no cache slot to overwrite. -/
theorem State.RetiredTask.cacheSelf {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (errors : Nat)
    : queue.cacheTaskFailures [(occurrence, errors)] = queue := by
  simp only [State.cacheTaskFailures, List.foldl_cons, List.foldl_nil, retired.missing]

private theorem missing_of_subset {queue next : State} {occurrence}
    (missing : queue.taskNode? occurrence = none)
    (subset : next.taskNodes.Subset queue.taskNodes)
    : next.taskNode? occurrence = none := by
  apply List.find?_eq_none.mpr
  intro node member
  exact List.find?_eq_none.mp missing node (subset member)

private theorem putTaskNode_missing {queue : State} {occurrence}
    (missing : queue.taskNode? occurrence = none) (updated : TaskNode)
    : (queue.putTaskNode updated).taskNode? occurrence = none := by
  apply List.find?_eq_none.mpr
  intro node member matched
  obtain ⟨old, prior, same⟩ := List.mem_map.mp member
  have identity := (occurrence_beq_iff_eq _ _).mp matched
  have oldIdentity : old.task.occurrence = occurrence := by
    split at same
    · rename_i selected
      exact ((occurrence_beq_iff_eq _ _).mp selected).trans (same ▸ identity)
    · exact same ▸ identity
  exact List.find?_eq_none.mp missing old prior
    ((occurrence_beq_iff_eq _ _).mpr oldIdentity)

/-- Replacement changes no occurrence keys or group task lists. -/
theorem State.RetiredTask.putTaskNode {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (node : TaskNode)
    : (queue.putTaskNode node).RetiredTask occurrence :=
  ⟨putTaskNode_missing retired.missing node, retired.unlinked.putTaskNode node⟩

/-- Removing graph records cannot restore a missing computation. -/
theorem State.RetiredTask.removeGroup {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (ref : Nat)
    : (queue.removeGroup ref).RetiredTask occurrence :=
  ⟨
    missing_of_subset retired.missing (fun _ member => (List.mem_filter.mp member).1),
    retired.unlinked.removeGroup ref
  ⟩

/-- Task removal preserves earlier global retirement. -/
theorem State.RetiredTask.removeTask {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (removed : Occurrence)
    : (queue.removeTask removed).RetiredTask occurrence :=
  ⟨
    missing_of_subset retired.missing (fun _ member => (List.mem_filter.mp member).1),
    retired.unlinked.removeTask removed
  ⟩

/-- Cache exposure writes existing rejection slots and creates no computation. -/
theorem State.RetiredTask.cacheTaskFailures {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).RetiredTask occurrence := by
  unfold State.cacheTaskFailures
  induction available generalizing queue with
  | nil => exact retired
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      apply ih
      split
      · exact retired
      · exact retired.putTaskNode _

private theorem State.RetiredTask.putGroupNode {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (updated : GroupNode)
    (missing : occurrence ∉ updated.tasks)
    : (queue.putGroupNode updated).RetiredTask occurrence :=
  ⟨retired.missing, retired.unlinked.putGroupNode updated missing⟩

/-- Starting another computation cannot recreate this retired occurrence. -/
theorem State.RetiredTask.startTask {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (started : Occurrence)
    (different : occurrence ≠ started) (available : List (Occurrence × Nat))
    : (queue.startTask started available).RetiredTask occurrence := by
  refine ⟨
    ?_,
    fun node member =>
      retired.unlinked node (by rwa [State.startTask_groupNodes] at member)
  ⟩
  unfold State.startTask
  split
  · exact retired.missing
  · split
    · exact retired.missing
    · rename_i task found
      have identity := (occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun task : Task => task.occurrence == started) found)
      change (queue.taskNodes ++ _).find? _ = none
      rw [List.find?_append]
      change (queue.taskNode? occurrence).or _ = none
      have noMatch : (task.occurrence == occurrence) = false :=
        Bool.eq_false_iff.mpr (fun same => different
          (((occurrence_beq_iff_eq _ _).mp same).symm.trans identity))
      simp only [retired.missing, Option.or, List.find?_cons, noMatch, List.find?_nil]

/-- A group cannot start a computation absent from all its task lists. -/
theorem State.RetiredTask.startGroup {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (ref : Nat)
    (available : List (Occurrence × Nat))
    : (queue.startGroup ref available).1.RetiredTask occurrence := by
  have cached := retired.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · rename_i group found
    split
    · have loop (tasks : List Occurrence) (current : State)
          (prior : current.RetiredTask occurrence) (fresh : occurrence ∉ tasks)
          : (tasks.foldl (fun q task => q.startTask task available) current).RetiredTask
              occurrence := by
        induction tasks generalizing current with
        | nil => exact prior
        | cons task rest ih =>
            simp only [List.mem_cons, not_or] at fresh
            exact ih _ (prior.startTask task fresh.1 available) fresh.2
      exact loop group.tasks _ cached
        (cached.unlinked group (List.mem_of_find?_eq_some found))
    · change ((queue.cacheTaskFailures available).removeGroup group.group.node.ref).RetiredTask
        occurrence
      exact cached.removeGroup _

/-- Empty-shell pruning changes no computation nodes and retains membership exclusion. -/
theorem State.RetiredTask.pruneEmptyGroups {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (groups)
    : (queue.pruneEmptyGroups groups).1.RetiredTask occurrence :=
  ⟨
    by
      simpa only [State.taskNode?, State.pruneEmptyGroups_taskNodes]
        using retired.missing,
    retired.unlinked.pruneEmptyGroups groups
  ⟩

/-- Installing delivery groups does not create computation nodes or old memberships. -/
theorem State.RetiredTask.addGroups {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (groups : List Group)
    : (queue.addGroups groups).1.RetiredTask occurrence :=
  ⟨
    by simpa only [State.taskNode?, State.addGroups_taskNodes] using retired.missing,
    retired.unlinked.addGroups groups
  ⟩

/-- Registration of a different occurrence preserves a retired computation. -/
theorem State.RetiredTask.addTask {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (task : Task)
    (different : occurrence ≠ task.occurrence)
    : (queue.addTask task).RetiredTask occurrence := by
  refine ⟨?_, retired.unlinked.addTask task different⟩
  apply List.find?_eq_none.mpr
  intro node member matched
  rcases queue.addTask_startedOldOrNew task member with old | new
  · exact List.find?_eq_none.mp retired.missing node old matched
  · subst node
    exact different (((occurrence_beq_iff_eq _ _).mp matched).symm)

/-- Stream registration updates only child-stream metadata of existing computations. -/
theorem State.RetiredTask.addStreams {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (streams producer)
    : (queue.addStreams streams producer).1.RetiredTask occurrence := by
  refine ⟨?_, retired.unlinked.addStreams streams producer⟩
  unfold State.addStreams
  dsimp only
  split
  · exact retired.missing
  · split
    · exact retired.missing
    · exact putTaskNode_missing retired.missing _

/-- Fresh child work cannot recreate an occurrence already retired before registration. -/
theorem State.RetiredTask.maybeIntegrateWork {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (incoming : Work)
    (fresh : ∀ task ∈ incoming.tasks, occurrence ≠ task.occurrence)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork incoming producer).1.RetiredTask occurrence := by
  have loop (tasks : List Task) (current : State) (prior : current.RetiredTask occurrence)
      (fresh : ∀ task ∈ tasks, occurrence ≠ task.occurrence)
      : (tasks.foldl State.addTask current).RetiredTask occurrence := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih =>
        exact ih _ (prior.addTask task (fresh task List.mem_cons_self))
          (fun next member => fresh next (List.mem_cons_of_mem _ member))
  exact (loop incoming.tasks _ (retired.addGroups incoming.groups) fresh).addStreams
    incoming.streams producer

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
