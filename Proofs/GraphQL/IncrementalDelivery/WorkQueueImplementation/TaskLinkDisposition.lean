import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionIntegration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UnsettledMemberships

/-! A permanent task is completely linked or globally retired. This proof-only distinction
avoids assuming unsettled membership completeness for an already settled/removed task.
It stores no new runtime ledger and imposes no host-source policy.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence)

-----------------------------------------------------------------------------------------
-- Permanent catalogue disposition implies completeness for actual live task records
-----------------------------------------------------------------------------------------

/-- A retired catalogue occurrence has neither a computation node nor live memberships. -/
def State.TaskRetired (queue : State) (occurrence : Occurrence) : Prop :=
  queue.taskNode? occurrence = none ∧ queue.TaskMembershipAbsent occurrence

/-- Complete contributor links, or a genuinely retired occurrence. The registry itself
remains historical. Successful buffering stays in the linked branch; settlement removal
switches to the retired branch without requiring successful output or healthy owners.
-/
def State.TaskLinkDisposition (queue : State) : Prop :=
  ∀ task ∈ queue.tasks,
    queue.TaskLinkedOn task.occurrence (task.groups.map Execution.DeliveryNode.ref)
    ∨ queue.TaskRetired task.occurrence

/-- A findable started record cannot use the retired branch of its registered descriptor. -/
theorem State.TaskLinkDisposition.startedLinks {queue : State}
    (disposition : queue.TaskLinkDisposition) (registered : queue.StartedTasksRegistered)
    {node : TaskNode} (member : node ∈ queue.taskNodes)
    : queue.TaskLinkedOn node.task.occurrence
        (node.task.groups.map Execution.DeliveryNode.ref) := by
  rcases disposition node.task (registered node member) with linked | retired
  · exact linked
  · have excluded := List.find?_eq_none.mp retired.1 node member
    exact (excluded ((occurrence_beq_iff_eq _ _).mpr rfl)).elim

/-- Initial complete catalogue links imply this weaker, transition-stable disposition. -/
theorem State.TaskLinkDisposition.of_initial {queue : State}
    (linked : queue.InitialTaskLinks)
    : queue.TaskLinkDisposition :=
  fun task member => .inl (linked task member)

-----------------------------------------------------------------------------------------
-- Settlement and removal preserve linked-or-retired disposition
-----------------------------------------------------------------------------------------

theorem State.removeTask_taskRetired (queue : State) (occurrence : Occurrence)
    : (queue.removeTask occurrence).TaskRetired occurrence := by
  refine ⟨?_, queue.removeTask_membershipAbsent occurrence⟩
  apply List.find?_eq_none.mpr
  intro node member selected
  have retained := (List.mem_filter.mp member).2
  simp only [bne, selected, Bool.not_true] at retained
  cases retained

theorem State.TaskRetired.removeTask {queue : State} {occurrence : Occurrence}
    (retired : queue.TaskRetired occurrence) (removed : Occurrence)
    : (queue.removeTask removed).TaskRetired occurrence := by
  refine ⟨?_, retired.2.removeTask removed⟩
  apply List.find?_eq_none.mpr
  intro node member
  exact List.find?_eq_none.mp retired.1 node (List.mem_filter.mp member).1

theorem State.TaskLinkDisposition.removeTask {queue : State}
    (disposition : queue.TaskLinkDisposition) (removed : Occurrence)
    : (queue.removeTask removed).TaskLinkDisposition := by
  intro task member
  by_cases same : task.occurrence = removed
  · exact .inr (same ▸ queue.removeTask_taskRetired removed)
  · rcases disposition task member with linked | retired
    · exact .inl (linked.removeOtherTask removed same)
    · exact .inr (retired.removeTask removed)

theorem State.TaskRetired.removeGroup {queue : State} {occurrence : Occurrence}
    (retired : queue.TaskRetired occurrence) (key : Nat)
    : (queue.removeGroup key).TaskRetired occurrence := by
  refine ⟨?_, retired.2.removeGroup key⟩
  apply List.find?_eq_none.mpr
  intro node member
  exact List.find?_eq_none.mp retired.1 node (List.mem_filter.mp member).1

theorem State.TaskLinkDisposition.removeGroup {queue : State}
    (disposition : queue.TaskLinkDisposition) (key : Nat)
    : (queue.removeGroup key).TaskLinkDisposition := by
  intro task member
  rcases disposition task member with linked | retired
  · exact .inl (linked.removeGroup key)
  · exact .inr (retired.removeGroup key)

theorem State.TaskRetired.pruneEmptyGroups {queue : State} {occurrence : Occurrence}
    (retired : queue.TaskRetired occurrence) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.TaskRetired occurrence := by
  refine ⟨?_, retired.2.pruneEmptyGroups groups⟩
  change ((queue.pruneEmptyGroups groups).1.taskNodes.find? _) = none
  rw [State.pruneEmptyGroups_taskNodes]
  exact retired.1

theorem State.TaskLinkDisposition.pruneEmptyGroups {queue : State}
    (disposition : queue.TaskLinkDisposition) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.TaskLinkDisposition := by
  intro task member
  rw [State.pruneEmptyGroups_tasks] at member
  rcases disposition task member with linked | retired
  · exact .inl (linked.pruneEmptyGroups groups)
  · exact .inr (retired.pruneEmptyGroups groups)

-----------------------------------------------------------------------------------------
-- Activation cannot resurrect an occurrence with no membership anywhere
-----------------------------------------------------------------------------------------

private theorem startTask_groups_tasks (queue : State) (occurrence : Occurrence)
    : (queue.startTask occurrence).groupNodes = queue.groupNodes
      ∧ (queue.startTask occurrence).tasks = queue.tasks := by
  unfold State.startTask
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

theorem State.TaskRetired.startOtherTask {queue : State} {occurrence : Occurrence}
    (retired : queue.TaskRetired occurrence) (chosen : Occurrence)
    (different : occurrence ≠ chosen)
    : (queue.startTask chosen).TaskRetired occurrence := by
  refine ⟨?_, ?_⟩
  · unfold State.startTask
    split
    · exact retired.1
    · split
      · exact retired.1
      · rename_i task found
        apply List.find?_eq_none.mpr
        intro node member selected
        rcases List.mem_append.mp member with old | added
        · exact List.find?_eq_none.mp retired.1 node old selected
        · obtain rfl := List.mem_singleton.mp added
          have key := (occurrence_beq_iff_eq _ _).mp
            (List.find?_some (p := fun candidate : Task => candidate.occurrence == chosen) found)
          have same := (occurrence_beq_iff_eq _ _).mp selected
          exact different (same.symm.trans key)
  · intro node member
    rw [(startTask_groups_tasks queue chosen).1] at member
    exact retired.2 node member

/-- Starting an occurrence selected by a real group cannot resurrect a retired task.
The selection witness is from the actual startGroup membership traversal, not a source
freshness or execution-order assumption.
-/
theorem State.TaskLinkDisposition.startLinkedTask {queue : State}
    (disposition : queue.TaskLinkDisposition) (chosen : Occurrence)
    (selected : ∃ group ∈ queue.groupNodes, chosen ∈ group.tasks)
    : (queue.startTask chosen).TaskLinkDisposition := by
  intro task member
  rw [(startTask_groups_tasks queue chosen).2] at member
  rcases disposition task member with linked | retired
  · exact .inl (linked.startTask chosen)
  · apply Or.inr
    apply retired.startOtherTask chosen
    intro same
    obtain ⟨group, present, listed⟩ := selected
    exact retired.2 group present (same ▸ listed)

theorem State.TaskLinkDisposition.startGroup {queue : State}
    (disposition : queue.TaskLinkDisposition) (key : Nat)
    : (queue.startGroup key).TaskLinkDisposition := by
  unfold State.startGroup
  split
  · exact disposition
  · rename_i group found
    have loop (more : List Occurrence) (current : State)
        (included : more.Subset group.tasks) (live : group ∈ current.groupNodes)
        (prior : current.TaskLinkDisposition)
        : (more.foldl State.startTask current).TaskLinkDisposition := by
      induction more generalizing current with
      | nil => exact prior
      | cons chosen rest ih =>
          apply ih _ (fun _ member => included (List.mem_cons_of_mem _ member))
          · rw [(startTask_groups_tasks current chosen).1]
            exact live
          · exact prior.startLinkedTask chosen
              ⟨group, live, included List.mem_cons_self⟩
    exact loop group.tasks queue (List.Subset.refl _) (List.mem_of_find?_eq_some found)
      disposition

theorem State.TaskLinkDisposition.startStream {queue : State}
    (disposition : queue.TaskLinkDisposition) (key : Nat)
    : (queue.startStream key).TaskLinkDisposition := by
  unfold State.startStream
  split <;> exact disposition

theorem State.TaskLinkDisposition.startNewWork {queue : State}
    (disposition : queue.TaskLinkDisposition) (released : NewWork)
    : (queue.startNewWork released).TaskLinkDisposition := by
  have groups (more : List Nat) (current : State) (prior : current.TaskLinkDisposition)
      : (more.foldl State.startGroup current).TaskLinkDisposition := by
    induction more generalizing current with
    | nil => exact prior
    | cons key rest ih => exact ih _ (prior.startGroup key)
  have streams (more : List Nat) (current : State) (prior : current.TaskLinkDisposition)
      : (more.foldl State.startStream current).TaskLinkDisposition := by
    induction more generalizing current with
    | nil => exact prior
    | cons key rest ih => exact ih _ (prior.startStream key)
  exact streams _ _ (groups _ _ disposition)

-----------------------------------------------------------------------------------------
-- Successful flushing and recursive draining use the same disposition
-----------------------------------------------------------------------------------------

theorem State.TaskRetired.filterGroups {queue : State} {occurrence : Occurrence}
    (retired : queue.TaskRetired occurrence) (keep : GroupNode → Bool)
    : ({ queue with groupNodes := queue.groupNodes.filter keep } : State).TaskRetired
        occurrence :=
  ⟨retired.1, fun node member => retired.2 node (List.mem_filter.mp member).1⟩

theorem State.TaskLinkDisposition.filterGroups {queue : State}
    (disposition : queue.TaskLinkDisposition) (keep : GroupNode → Bool)
    : ({ queue with groupNodes := queue.groupNodes.filter keep }
        : State).TaskLinkDisposition := by
  intro task member
  rcases disposition task member with linked | retired
  · exact .inl (fun node member => linked node (List.mem_filter.mp member).1)
  · exact .inr (retired.filterGroups keep)

theorem State.TaskLinkDisposition.flushTasks {queue : State}
    (disposition : queue.TaskLinkDisposition) (tasks : List Occurrence)
    (values : List Execution.ExecutionGroupValue) (streams : WorkQueueSemantics.NodeRefs)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.TaskLinkDisposition := by
  induction tasks generalizing queue values streams with
  | nil => exact disposition
  | cons occurrence rest ih =>
      simp only [List.foldl_cons, flushGroupTask]
      split
      · exact ih disposition _ _
      · exact ih (disposition.removeTask occurrence) _ _

theorem State.TaskLinkDisposition.finishGroupSuccess {queue : State}
    (disposition : queue.TaskLinkDisposition) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.TaskLinkDisposition := by
  have folded := disposition.flushTasks group.tasks [] []
  have filtered := folded.filterGroups (fun node => node.group.node.ref != group.group.node.ref)
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  let current : State := { flushed with
    groupNodes := flushed.groupNodes.filter (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentDisposition : current.TaskLinkDisposition := filtered
  unfold State.finishGroupSuccess
  exact currentDisposition.pruneEmptyGroups _

theorem State.TaskRetired.putTaskNode {queue : State} {occurrence : Occurrence}
    (retired : queue.TaskRetired occurrence) (updated : TaskNode)
    : (queue.putTaskNode updated).TaskRetired occurrence := by
  refine ⟨?_, retired.2.putTaskNode updated⟩
  apply List.find?_eq_none.mpr
  intro node member selected
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · rename_i replacing
    subst node
    have oldKey := (occurrence_beq_iff_eq _ _).mp replacing
    have selectedKey := (occurrence_beq_iff_eq _ _).mp selected
    exact List.find?_eq_none.mp retired.1 old oldMember
      ((occurrence_beq_iff_eq _ _).mpr (oldKey.trans selectedKey))
  · subst node
    exact List.find?_eq_none.mp retired.1 old oldMember selected

theorem State.TaskLinkDisposition.putTaskNode {queue : State}
    (disposition : queue.TaskLinkDisposition) (updated : TaskNode)
    : (queue.putTaskNode updated).TaskLinkDisposition := by
  intro task member
  rcases disposition task member with linked | retired
  · exact .inl linked
  · exact .inr (retired.putTaskNode updated)

/-- Rejected computations retain complete links until all their owners are removed. -/
theorem State.TaskLinkDisposition.taskFailure {queue : State}
    (disposition : queue.TaskLinkDisposition) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.TaskLinkDisposition := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using disposition
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      exact failureGroupFold_preserves State.TaskLinkDisposition
        (fun _ ref prior => prior.removeGroup ref) errors task.task.groups _
        (disposition.putTaskNode _)

theorem State.TaskLinkDisposition.drainReadyGroups_go {queue : State}
    (disposition : queue.TaskLinkDisposition) (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.TaskLinkDisposition := by
  induction fuel generalizing queue with
  | zero => exact disposition
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact disposition
      · rename_i group _
        cases cached : queue.rejectedTask? group with
        | none => exact ih ((disposition.finishGroupSuccess group).startNewWork _)
        | some rejected =>
            obtain ⟨occurrence, errors⟩ := rejected
            exact ih (disposition.taskFailure occurrence errors)

theorem State.TaskLinkDisposition.drainReadyGroups {queue : State}
    (disposition : queue.TaskLinkDisposition)
    : queue.drainReadyGroups.1.TaskLinkDisposition :=
  disposition.drainReadyGroups_go _

-----------------------------------------------------------------------------------------
-- Registration preserves old dispositions and establishes each new task's links
-----------------------------------------------------------------------------------------

theorem State.TaskRetired.addGroups {queue : State} {occurrence : Occurrence}
    (retired : queue.TaskRetired occurrence) (groups : List Group)
    : (queue.addGroups groups).1.TaskRetired occurrence := by
  refine ⟨?_, retired.2.addGroups groups⟩
  change ((queue.addGroups groups).1.taskNodes.find? _) = none
  rw [State.addGroups_taskNodes]
  exact retired.1

theorem State.TaskLinkDisposition.addGroups {queue : State}
    (disposition : queue.TaskLinkDisposition) (unique : queue.GroupRefsUnique)
    (registered : queue.TaskGroupsRegistered) (groups : List Group)
    : (queue.addGroups groups).1.TaskLinkDisposition := by
  intro task member
  rw [State.addGroups_tasks] at member
  rcases disposition task member with linked | retired
  · exact .inl (linked.addRegisteredGroups unique
      (fun _ contributor => registered task member _ contributor) groups)
  · exact .inr (retired.addGroups groups)

theorem State.TaskRetired.addOtherTask {queue : State} {occurrence : Occurrence}
    (retired : queue.TaskRetired occurrence) (task : Task)
    (different : occurrence ≠ task.occurrence)
    : (queue.addTask task).TaskRetired occurrence := by
  refine ⟨?_, retired.2.addTask task different⟩
  apply List.find?_eq_none.mpr
  intro node member selected
  rcases queue.addTask_startedOldOrNew task member with old | new
  · exact List.find?_eq_none.mp retired.1 node old selected
  · subst node
    exact different ((occurrence_beq_iff_eq _ _).mp selected).symm

theorem State.TaskLinkDisposition.addTask {queue : State} {work : Execution.Work}
    (disposition : queue.TaskLinkDisposition) (unique : queue.GroupRefsUnique)
    (matching : queue.RegisteredTasksMatch work) (task : Task)
    (known : TaskMatches work task)
    : (queue.addTask task).TaskLinkDisposition := by
  intro other member
  rw [State.addTask_tasks] at member
  rcases List.mem_append.mp member with old | new
  · rcases disposition other old with linked | retired
    · exact .inl (linked.addTask unique task)
    · by_cases same : other.occurrence = task.occurrence
      · have groups : other.groups = task.groups := by
          apply Option.some.inj
          rw [← (matching other old).2, same, known.2]
        rw [same, groups]
        exact .inl (queue.addTask_links unique task)
      · exact .inr (retired.addOtherTask task same)
  · rw [List.mem_singleton.mp new]
    exact .inl (queue.addTask_links unique task)

theorem State.TaskLinkDisposition.putGroupNodeSameTasks {queue : State}
    (disposition : queue.TaskLinkDisposition) (unique : queue.GroupRefsUnique)
    (node : GroupNode) (present : node ∈ queue.groupNodes) (updated : GroupNode)
    (sameKey : updated.group.node.ref = node.group.node.ref)
    (sameTasks : updated.tasks = node.tasks)
    : (queue.putGroupNode updated).TaskLinkDisposition := by
  intro task member
  rcases disposition task member with linked | retired
  · exact .inl (linked.putGroupNodeSameTasks unique node present updated sameKey sameTasks)
  · exact .inr ⟨retired.1, retired.2.putGroupNode updated (sameTasks ▸ retired.2 node present)⟩

theorem State.TaskLinkDisposition.addStreams {queue : State}
    (disposition : queue.TaskLinkDisposition) (streams : List Stream)
    (producer : Option Occurrence := none)
    : (queue.addStreams streams producer).1.TaskLinkDisposition := by
  cases producer with
  | none => exact disposition
  | some occurrence =>
      unfold State.addStreams
      dsimp only
      split
      · exact disposition
      · apply State.TaskLinkDisposition.putTaskNode
        exact disposition

theorem State.TaskLinkDisposition.maybeIntegrateWork {queue : State}
    {work : Execution.Work} (disposition : queue.TaskLinkDisposition)
    (unique : queue.GroupRefsUnique) (registered : queue.TaskGroupsRegistered)
    (matching : queue.RegisteredTasksMatch work) (incoming : Work)
    (known : ∀ task ∈ incoming.tasks, TaskMatches work task)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork incoming producer).1.TaskLinkDisposition := by
  have loop (tasks : List Task) (current : State) (prior : current.TaskLinkDisposition)
      (keys : current.GroupRefsUnique) (matched : current.RegisteredTasksMatch work)
      (sources : ∀ task ∈ tasks, TaskMatches work task)
      : (tasks.foldl State.addTask current).TaskLinkDisposition := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih =>
        exact ih _ (prior.addTask keys matched task (sources task List.mem_cons_self))
          (keys.addTask task) (matched.addTask task (sources task List.mem_cons_self))
          (fun task member => sources task (List.mem_cons_of_mem _ member))
  exact (loop incoming.tasks (queue.addGroups incoming.groups).1
          (disposition.addGroups unique registered incoming.groups)
          (unique.addGroups incoming.groups) (matching.addGroups incoming.groups)
          known).addStreams
    incoming.streams producer

/-- Initial complete scope links are preserved through pruning and actual activation. -/
theorem createWorkQueue_taskLinkDisposition (work : Work)
    : (State.initialize work).TaskLinkDisposition := by
  let integrated := (({} : State).maybeIntegrateWork work).1
  let newWork := (({} : State).maybeIntegrateWork work).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  have prepared : integrated.TaskLinkDisposition :=
    State.TaskLinkDisposition.of_initial (State.initialWorkTaskLinks work)
  exact (prepared.pruneEmptyGroups newWork.newGroups).startNewWork roots

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
