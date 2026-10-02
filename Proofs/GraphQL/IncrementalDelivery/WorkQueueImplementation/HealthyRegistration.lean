import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyContributors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordCancellation

/-! Registered-task accounting under healthy owners. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Group integration preserves healthy links for old started tasks when no
newly registered healthy group is a previously missing contributor of one. -/
theorem State.HealthyTaskLinks.addGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (unique : queue.GroupKeysUnique)
    (links : queue.HealthyTaskLinks work settled failed)
    (groups : List Group)
    (relevantExisting
      : ∀ taskNode ∈ queue.taskNodes,
          taskNode.task.occurrence ∉ settled
          → ∀ group ∈ groups,
              group.node.key ∈ taskNode.task.groups.map Execution.DeliveryNode.key
              → ¬GroupInvalidated work failed group.node.key
              → ∃ node ∈ queue.groupNodes, node.group.node.key = group.node.key)
    : (queue.addGroups groups).1.HealthyTaskLinks work settled failed := by
  apply State.HealthyTaskLinks.ofFilteredLinks
  intro taskNode taskMember fresh
  have old : taskNode ∈ queue.taskNodes := by
    rw [queue.addGroups_taskNodes groups] at taskMember
    exact taskMember
  apply (links.toTaskLinkedOn old fresh).addGroups unique groups
  intro group groupMember healthyMember
  obtain ⟨contributor, healthy⟩ := mem_healthyContributorKeys_iff.mp
    healthyMember
  exact relevantExisting taskNode old fresh group groupMember contributor healthy

/-- Existing registered tasks keep every healthy contributor membership when
child groups are integrated; a healthy contributor key was already live. -/
theorem State.HealthyRegisteredTaskAccounting.addGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (unique : queue.GroupKeysUnique)
    (groups : List Group)
    : (queue.addGroups groups).1.HealthyRegisteredTaskAccounting work settled failed := by
  intro task taskMember fresh key contributor healthy
  have oldTask : task ∈ queue.tasks := by
    rw [queue.addGroups_tasks groups] at taskMember
    exact taskMember
  obtain ⟨oldNode, oldMember, oldKey, _⟩ :=
    accounted task oldTask fresh key contributor healthy
  have relevantExisting : ∀ group ∈ groups,
      group.node.key ∈ healthyContributorKeys work failed
        (task.groups.map Execution.DeliveryNode.key)
      → ∃ node ∈ queue.groupNodes, node.group.node.key = group.node.key := by
    intro group _ relevant
    obtain ⟨groupContributor, groupHealthy⟩ :=
      mem_healthyContributorKeys_iff.mp relevant
    obtain ⟨node, member, same, _⟩ :=
      accounted task oldTask fresh group.node.key groupContributor groupHealthy
    exact ⟨node, member, same⟩
  have linked := (accounted.taskLinkedOn unique oldTask fresh).addGroups
    unique groups relevantExisting
  have oldKeyMember : key ∈ queue.groupNodes.map
      (fun node => node.group.node.key) :=
    List.mem_map.mpr ⟨oldNode, oldMember, oldKey⟩
  obtain ⟨node, nodeMember, same⟩ := List.mem_map.mp
    (queue.addGroups_includesKeys groups key oldKeyMember)
  have keyMember : key ∈ healthyContributorKeys work failed
      (task.groups.map Execution.DeliveryNode.key) :=
    mem_healthyContributorKeys_iff.mpr ⟨contributor, healthy⟩
  have nodeKeyMember : node.group.node.key ∈ healthyContributorKeys
      work failed (task.groups.map Execution.DeliveryNode.key) := by
    rw [same]
    exact keyMember
  exact ⟨node, nodeMember, same, linked node nodeMember nodeKeyMember⟩

/-- Task registration retains old healthy links and installs all group links
for a newly started task. -/
theorem State.HealthyTaskLinks.addTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (unique : queue.GroupKeysUnique)
    (links : queue.HealthyTaskLinks work settled failed)
    (task : Task)
    : (queue.addTask task).HealthyTaskLinks work settled failed := by
  apply State.HealthyTaskLinks.ofFilteredLinks
  intro taskNode member fresh
  rcases queue.addTask_startedOldOrNew task member with old | new
  · exact (links.toTaskLinkedOn old fresh).addTask unique task
  · subst taskNode
    intro groupNode groupMember keyMember
    obtain ⟨contributor, _⟩ := mem_healthyContributorKeys_iff.mp keyMember
    exact queue.addTask_links unique task groupNode groupMember contributor

/-- Registering a task preserves earlier healthy memberships and installs
the new task's memberships in all already registered contributor groups. -/
theorem State.HealthyRegisteredTaskAccounting.addTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (unique : queue.GroupKeysUnique)
    (task : Task)
    (taskGroupsPresent
      : ∀ key ∈ task.groups.map Execution.DeliveryNode.key,
          ¬GroupInvalidated work failed key
          → ∃ node ∈ queue.groupNodes, node.group.node.key = key)
    : (queue.addTask task).HealthyRegisteredTaskAccounting work settled failed := by
  intro registered taskMember fresh key contributor healthy
  rw [queue.addTask_tasks task] at taskMember
  rcases List.mem_append.mp taskMember with old | new
  · obtain ⟨oldNode, oldMember, oldKey, _⟩ :=
      accounted registered old fresh key contributor healthy
    have linked := (accounted.taskLinkedOn unique old fresh).addTask unique task
    have oldKeyMember : key ∈ queue.groupNodes.map
        (fun node => node.group.node.key) :=
      List.mem_map.mpr ⟨oldNode, oldMember, oldKey⟩
    obtain ⟨node, nodeMember, same⟩ := List.mem_map.mp
      (queue.addTask_includesKeys task key oldKeyMember)
    have keyMember : node.group.node.key ∈ healthyContributorKeys
        work failed (registered.groups.map Execution.DeliveryNode.key) := by
      rw [same]
      exact mem_healthyContributorKeys_iff.mpr ⟨contributor, healthy⟩
    exact ⟨node, nodeMember, same, linked node nodeMember keyMember⟩
  · have same : registered = task := List.mem_singleton.mp new
    subst registered
    obtain ⟨oldNode, oldMember, oldKey⟩ :=
      taskGroupsPresent key contributor healthy
    have oldKeyMember : key ∈ queue.groupNodes.map
        (fun node => node.group.node.key) :=
      List.mem_map.mpr ⟨oldNode, oldMember, oldKey⟩
    obtain ⟨node, nodeMember, same⟩ := List.mem_map.mp
      (queue.addTask_includesKeys task key oldKeyMember)
    have nodeContributor : node.group.node.key ∈
        task.groups.map Execution.DeliveryNode.key := by
      rw [same]
      exact contributor
    exact ⟨node, nodeMember, same,
      queue.addTask_links unique task node nodeMember nodeContributor⟩

/-- Stream registration changes neither task definitions nor group
memberships, so registered-task accounting is unchanged. -/
theorem State.HealthyRegisteredTaskAccounting.addStreams
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (streams : List Stream) (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.HealthyRegisteredTaskAccounting
        work settled failed := by
  intro task taskMember fresh key contributor healthy
  have old : task ∈ queue.tasks := by
    rw [State.addStreams_tasks] at taskMember
    exact taskMember
  unfold State.addStreams
  split
  · exact accounted task old fresh key contributor healthy
  · dsimp
    split <;> exact accounted task old fresh key contributor healthy

/-- Coherent child integration retains old links and registers healthy contributors.
Witness: task provenance identifies actual owners; record-aware cancellation support
prevents refusing their keys even when other candidates are taskless ancestors.
-/
theorem State.HealthyRegisteredTaskAccounting.maybeIntegrateWork
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (unique : queue.GroupKeysUnique)
    (newWork : Work) (parentTask : Option Occurrence)
    (covered
      : ∀ task ∈ newWork.tasks,
        ∀ key ∈ task.groups.map Execution.DeliveryNode.key,
          ∃ group ∈ newWork.groups, group.node.key = key)
    (available : queue.ChildGroupsAvailable work failed newWork)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (taskMatching : ∀ task ∈ newWork.tasks, TaskMatches work task)
    (descriptors
      : ∀ group ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    : (queue.maybeIntegrateWork newWork parentTask).1.HealthyRegisteredTaskAccounting
        work settled failed := by
  let withGroups := (queue.addGroups newWork.groups).1
  let withTasks := newWork.tasks.foldl State.addTask withGroups
  have groupedAccounting : withGroups.HealthyRegisteredTaskAccounting
      work settled failed := accounted.addGroups unique newWork.groups
  have groupedUnique : withGroups.GroupKeysUnique := unique.addGroups newWork.groups
  have taskFold (more : List Task)
      (subset : ∀ task ∈ more, task ∈ newWork.tasks) :
      ∀ current : State,
        current.HealthyRegisteredTaskAccounting work settled failed
        → current.GroupKeysUnique
        → withGroups.GroupKeysIncluded current
        → (more.foldl State.addTask current).HealthyRegisteredTaskAccounting
            work settled failed := by
    induction more with
    | nil => intro current currentAccounting _ _; exact currentAccounting
    | cons task rest ih =>
        intro current currentAccounting currentUnique included
        have taskCovered := covered task (subset task (by simp))
        have taskPresent : ∀ key ∈ task.groups.map Execution.DeliveryNode.key,
            ¬GroupInvalidated work failed key
            → ∃ node ∈ current.groupNodes, node.group.node.key = key := by
          intro key contributor healthy
          obtain ⟨group, groupMember, same⟩ :=
            taskCovered key contributor
          obtain ⟨dependencies, source, producer, known, sourceKey⟩ :=
            (taskMatching task (subset task (by simp))).contributorKnown contributor
          have notCancelled : key ∉ withGroups.cancelledGroups := by
            rw [← sourceKey]
            have grouped := cancelled.addGroups newWork.groups descriptors
            exact grouped.contributor_healthy_not_mem generated known
              (sourceKey.symm ▸ healthy)
          have groupKey : group.node.key ∈ withGroups.groupNodes.map
              (fun node => node.group.node.key) :=
            queue.addGroups_registersKeys newWork.groups group groupMember
              (same ▸ available task (subset task (by simp)) key contributor healthy)
              (same ▸ notCancelled)
          rw [same] at groupKey
          obtain ⟨node, nodeMember, nodeKey⟩ := List.mem_map.mp
            (included key groupKey)
          exact ⟨node, nodeMember, nodeKey⟩
        have tailSubset : ∀ next ∈ rest, next ∈ newWork.tasks := by
          intro next member
          exact subset next (by simp [member])
        exact ih tailSubset (current.addTask task)
          (currentAccounting.addTask currentUnique task taskPresent)
          (currentUnique.addTask task)
          (included.trans (current.addTask_includesKeys task))
  have taskAccounting : withTasks.HealthyRegisteredTaskAccounting
      work settled failed :=
    taskFold newWork.tasks (fun _ member => member) withGroups
      groupedAccounting groupedUnique (by intro key member; exact member)
  change State.HealthyRegisteredTaskAccounting
    (withTasks.addStreams newWork.streams parentTask).1 work settled failed
  exact taskAccounting.addStreams newWork.streams parentTask

/-- Mutable task-node updates change neither the task registry nor group
memberships. -/
theorem State.HealthyRegisteredTaskAccounting.putTaskNode
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (updated : TaskNode)
    : (queue.putTaskNode updated).HealthyRegisteredTaskAccounting work settled failed :=
  accounted

/-- Starting newly released tasks leaves their registered task and group
membership maps untouched. -/
theorem State.HealthyRegisteredTaskAccounting.startNewWork
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (newWork : NewWork)
    : (queue.startNewWork newWork).HealthyRegisteredTaskAccounting
        work settled failed := by
  obtain ⟨sameGroups, sameTasks, _⟩ := queue.startNewWork_groupCore newWork
  intro task taskMember fresh key contributor healthy
  have oldTask : task ∈ queue.tasks := by
    rw [sameTasks] at taskMember
    exact taskMember
  obtain ⟨node, oldMember, same, linked⟩ :=
    accounted task oldTask fresh key contributor healthy
  have finalMember : node ∈ (queue.startNewWork newWork).groupNodes := by
    rw [sameGroups]
    exact oldMember
  exact ⟨node, finalMember, same, linked⟩

/-- A pending-count update preserves every healthy registered-task link when
the group's stable key and task membership list are unchanged. -/
theorem State.HealthyRegisteredTaskAccounting.putGroupNodeSameTasks
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (unique : queue.GroupKeysUnique)
    (node : GroupNode) (nodeMember : node ∈ queue.groupNodes)
    (updated : GroupNode)
    (sameKey : updated.group.node.key = node.group.node.key)
    (sameTasks : updated.tasks = node.tasks)
    : (queue.putGroupNode updated).HealthyRegisteredTaskAccounting
        work settled failed := by
  intro task taskMember fresh key contributor healthy
  obtain ⟨oldNode, oldMember, oldKey, _⟩ :=
    accounted task taskMember fresh key contributor healthy
  have keyMember : key ∈ queue.groupNodes.map
      (fun entry => entry.group.node.key) :=
    List.mem_map.mpr ⟨oldNode, oldMember, oldKey⟩
  rw [← queue.putGroupNode_keys updated] at keyMember
  obtain ⟨newNode, newMember, newKey⟩ := List.mem_map.mp keyMember
  have linked := (accounted.taskLinkedOn unique taskMember fresh).putGroupNodeSameTasks
    unique node nodeMember updated sameKey sameTasks
  have healthyKey : newNode.group.node.key ∈ healthyContributorKeys
      work failed (task.groups.map Execution.DeliveryNode.key) := by
    rw [newKey]
    exact mem_healthyContributorKeys_iff.mpr ⟨contributor, healthy⟩
  exact ⟨newNode, newMember, newKey, linked newNode newMember healthyKey⟩

/-- A longer settlement prefix only weakens registered-task accounting. -/
theorem State.HealthyRegisteredTaskAccounting.weakenSettled
    {queue : State} {work : Execution.Work} {before after failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work before failed)
    (included : before.Subset after)
    : queue.HealthyRegisteredTaskAccounting work after failed := by
  intro task taskMember fresh key contributor healthy
  exact accounted task taskMember
    (by
      intro prior
      exact fresh (included prior))
    key contributor healthy

/-- Additional failures shrink the healthy-key set, preserving every
previously established registered-task link for surviving groups. -/
theorem State.HealthyRegisteredTaskAccounting.weakenFailures
    {queue : State} {work : Execution.Work} {settled before after : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled before)
    (included : before.Subset after)
    : queue.HealthyRegisteredTaskAccounting work settled after := by
  intro task taskMember fresh key contributor healthy
  apply accounted task taskMember fresh key contributor
  intro failedBefore
  exact healthy (GroupInvalidated.mono failedBefore included)

/-- Removing a failed group preserves the registered-task invariant when
every group it removes is invalidated under the enlarged failure set.
The separate cleanup-removal proof must establish this condition. -/
theorem State.HealthyRegisteredTaskAccounting.removeGroup
    {queue : State} {work : Execution.Work} {settled before after : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled before)
    (included : before.Subset after)
    (key : Nat)
    (healthyRetained
      : ∀ node ∈ queue.groupNodes,
          ¬GroupInvalidated work after node.group.node.key
          → node ∈ (queue.removeGroup key).groupNodes)
    : (queue.removeGroup key).HealthyRegisteredTaskAccounting work settled after := by
  intro task taskMember fresh contributorKey contributor healthy
  obtain ⟨node, nodeMember, same, linked⟩ :=
    (accounted.weakenFailures included) task taskMember fresh
      contributorKey contributor healthy
  have nodeHealthy : ¬GroupInvalidated work after node.group.node.key := by
    rw [same]
    exact healthy
  exact ⟨node, healthyRetained node nodeMember nodeHealthy, same, linked⟩

/-- A contributor-settlement pass changes pending counters, not registered
task memberships. -/
theorem State.HealthyRegisteredTaskAccounting.settleTaskGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (unique : queue.GroupKeysUnique)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl
        (fun current group =>
          match current.groupNode? group.key with
          | none => current
          | some node => current.putGroupNode { node with pending := node.pending - 1 })
        queue).HealthyRegisteredTaskAccounting
        work settled failed := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have stepFacts (current : State) (group : Execution.DeliveryNode)
      (currentAccounting : current.HealthyRegisteredTaskAccounting
        work settled failed)
      (currentUnique : current.GroupKeysUnique)
      : (step current group).HealthyRegisteredTaskAccounting
          work settled failed
        ∧ (step current group).GroupKeysUnique := by
    unfold step
    split
    · exact ⟨currentAccounting, currentUnique⟩
    · rename_i node found
      have nodeMember : node ∈ current.groupNodes :=
        List.mem_of_find?_eq_some found
      exact ⟨currentAccounting.putGroupNodeSameTasks currentUnique
          node nodeMember { node with pending := node.pending - 1 } rfl rfl,
        currentUnique.putGroupNode _⟩
  have foldFacts (more : List Execution.DeliveryNode) :
      ∀ current : State,
        current.HealthyRegisteredTaskAccounting work settled failed
        → current.GroupKeysUnique
        → (more.foldl step current).HealthyRegisteredTaskAccounting
            work settled failed := by
    induction more with
    | nil => intro current currentAccounting _; exact currentAccounting
    | cons group rest ih =>
        intro current currentAccounting currentUnique
        obtain ⟨nextAccounting, nextUnique⟩ :=
          stepFacts current group currentAccounting currentUnique
        exact ih (step current group) nextAccounting nextUnique
  exact foldFacts groups queue accounted unique

/-- A registered fresh task keeps each healthy contributor group nonempty,
so pruning cannot erase that group or its task membership. -/
theorem State.HealthyRegisteredTaskAccounting.pruneNonemptyGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (unique : queue.GroupKeysUnique)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.HealthyRegisteredTaskAccounting
        work settled failed := by
  intro task taskMember fresh key contributor healthy
  have oldTask : task ∈ queue.tasks := by
    rw [State.pruneEmptyGroups_tasks] at taskMember
    exact taskMember
  obtain ⟨node, nodeMember, nodeKey, linked⟩ :=
    accounted task oldTask fresh key contributor healthy
  obtain ⟨retained, retainedMember, retainedKey, _⟩ :=
    queue.pruneEmptyGroups_preservesNonempty groups unique
      ⟨node, nodeMember, nodeKey, List.ne_nil_of_mem linked⟩
  have retainedKeyMember : retained.group.node.key ∈ healthyContributorKeys
      work failed (task.groups.map Execution.DeliveryNode.key) := by
    rw [retainedKey]
    exact mem_healthyContributorKeys_iff.mpr ⟨contributor, healthy⟩
  have retainedLink := (accounted.taskLinkedOn unique oldTask fresh).pruneEmptyGroups
    groups retained retainedMember retainedKeyMember
  exact ⟨retained, retainedMember, retainedKey, retainedLink⟩

/-- The former lower-bound interface follows from nonempty membership alone.
Witness: `pruneNonemptyGroups`; pruning does not inspect pending counters.
-/
theorem State.HealthyRegisteredTaskAccounting.pruneEmptyGroups_ofPendingBound
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (_tracks : queue.HealthyPendingBound work settled failed)
    (unique : queue.GroupKeysUnique) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.HealthyRegisteredTaskAccounting
        work settled failed :=
  accounted.pruneNonemptyGroups unique groups

/-- The exact-ledger specialization follows from nonempty membership alone. -/
theorem State.HealthyRegisteredTaskAccounting.pruneEmptyGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (_tracks : queue.HealthyPendingTracks work settled failed)
    (unique : queue.GroupKeysUnique)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.HealthyRegisteredTaskAccounting
        work settled failed := by
  exact accounted.pruneNonemptyGroups unique groups

/-- Flushing an already settled task removes only that task's memberships;
fresh registered tasks retain their healthy contributor links. -/
theorem State.HealthyRegisteredTaskAccounting.removeSettledTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (occurrence : Occurrence) (already : occurrence ∈ settled)
    : (queue.removeTask occurrence).HealthyRegisteredTaskAccounting
        work settled failed := by
  intro task taskMember fresh key contributor healthy
  obtain ⟨node, nodeMember, same, linked⟩ :=
    accounted task taskMember fresh key contributor healthy
  have different : task.occurrence ≠ occurrence := by
    intro equal
    exact fresh (equal ▸ already)
  let retained : GroupNode :=
    { node with tasks := node.tasks.filter (· != occurrence) }
  have retainedMember : retained ∈ (queue.removeTask occurrence).groupNodes :=
    List.mem_map.mpr ⟨node, nodeMember, rfl⟩
  have retainedLink : task.occurrence ∈ retained.tasks := by
    apply List.mem_filter.mpr
    refine ⟨linked, ?_⟩
    have unequal : (task.occurrence == occurrence) = false := by
      cases found : task.occurrence == occurrence with
      | false => rfl
      | true =>
          have contradiction : False :=
            different ((occurrence_beq_iff_eq _ _).mp found)
          exact contradiction.elim
    simp [bne, unequal]
  exact ⟨retained, retainedMember, same, retainedLink⟩

/-- Removing a recorded failed task preserves healthy registered memberships.
Witness: structural task provenance invalidates every owner of that occurrence, so
any task with a healthy owner is distinct and survives the membership filter.
-/
theorem State.HealthyRegisteredTaskAccounting.removeFailedTask
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (recorded : occurrence ∈ failed)
    : (queue.removeTask occurrence).HealthyRegisteredTaskAccounting work settled
        failed := by
  intro task taskMember fresh key contributor healthy
  have different : task.occurrence ≠ occurrence := by
    intro same
    obtain ⟨_, payload, producer, _, known⟩ := (matching task taskMember).1
    exact healthy (.task ⟨producer, payload, known⟩ contributor (same.symm ▸ recorded))
  have enlarged := accounted.weakenSettled
    (after := occurrence :: settled) (by intro item member; simp [member])
  have after := enlarged.removeSettledTask occurrence (by simp)
  exact after task taskMember (by simp [different, fresh]) key contributor healthy

/-- Updating an invalidated group's record cannot change a healthy ownership witness.
Witness: the witness's healthy key differs from the replaced key; no key-uniqueness
premise is needed for this specialized replacement.
-/
theorem State.HealthyRegisteredTaskAccounting.putInvalidatedGroup
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (updated : GroupNode) (invalid : GroupInvalidated work failed updated.group.node.key)
    : (queue.putGroupNode updated).HealthyRegisteredTaskAccounting work settled
        failed := by
  intro task taskMember fresh key contributor healthy
  obtain ⟨node, member, same, linked⟩ := accounted task taskMember fresh key contributor healthy
  have different : node.group.node.key ≠ updated.group.node.key := by
    intro equal
    exact healthy ((equal.symm.trans same) ▸ invalid)
  refine ⟨node, List.mem_map.mpr ⟨node, member, ?_⟩, same, linked⟩
  simp [different]

/-- Removing a group preserves healthy memberships if a healthy closing group has
no fresh contributor. Witness: the original owner survives the key filter.
-/
theorem State.HealthyRegisteredTaskAccounting.filterGroupKey_ifHealthy
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (closedKey : Nat)
    (noFreshContributor
      : ¬GroupInvalidated work failed closedKey
        → ∀ task ∈ queue.tasks,
            task.occurrence ∉ settled
            → closedKey ∉ task.groups.map Execution.DeliveryNode.key)
    : State.HealthyRegisteredTaskAccounting
        ({
          queue with
            groupNodes :=
              queue.groupNodes.filter (fun node => node.group.node.key != closedKey)
            rootGroups := queue.rootGroups.filter (· != closedKey)
        })
        work settled failed := by
  intro task taskMember fresh key contributor healthy
  obtain ⟨node, nodeMember, same, linked⟩ :=
    accounted task taskMember fresh key contributor healthy
  have different : node.group.node.key ≠ closedKey := by
    intro equal
    have closedHealthy : ¬GroupInvalidated work failed closedKey := by
      simpa [← equal, same] using healthy
    exact noFreshContributor closedHealthy task taskMember fresh
      (equal ▸ (same ▸ contributor))
  have retained : node ∈ queue.groupNodes.filter
      (fun candidate => candidate.group.node.key != closedKey) :=
    List.mem_filter.mpr ⟨nodeMember, by simp [different]⟩
  exact ⟨node, retained, same, linked⟩

/-- The unconditional no-fresh-contributor interface is a specialization.
Witness: `filterGroupKey_ifHealthy` ignores the extra health premise.
-/
theorem State.HealthyRegisteredTaskAccounting.filterGroupKey
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (closedKey : Nat)
    (noFreshContributor
      : ∀ task ∈ queue.tasks,
          task.occurrence ∉ settled
          → closedKey ∉ task.groups.map Execution.DeliveryNode.key)
    : State.HealthyRegisteredTaskAccounting
        ({
          queue with
            groupNodes :=
              queue.groupNodes.filter (fun node => node.group.node.key != closedKey)
            rootGroups := queue.rootGroups.filter (· != closedKey)
        })
        work settled failed :=
  accounted.filterGroupKey_ifHealthy closedKey (fun _ => noFreshContributor)

/-- Flushing a group whose memberships are settled preserves healthy registration,
even when the closing group is invalidated. Witness: settled removals, a conditional
key filter, and nonempty membership preservation through descendant pruning.
-/
theorem State.HealthyRegisteredTaskAccounting.finishSettledGroupSuccess
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (unique : queue.GroupKeysUnique)
    (group : GroupNode) (groupMember : group ∈ queue.groupNodes)
    (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.HealthyRegisteredTaskAccounting
        work settled failed := by
  let step (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values :=
          match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have stepFacts (acc : State × List ExecutionGroupValue × Keys)
      (occurrence : Occurrence) (already : occurrence ∈ settled)
      (currentAccounting : acc.1.HealthyRegisteredTaskAccounting
        work settled failed)
      (currentUnique : acc.1.GroupKeysUnique)
      : (step acc occurrence).1.HealthyRegisteredTaskAccounting work settled failed
        ∧ (step acc occurrence).1.GroupKeysUnique
        ∧ (step acc occurrence).1.tasks = acc.1.tasks := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact ⟨currentAccounting, currentUnique, rfl⟩
    · exact ⟨currentAccounting.removeSettledTask occurrence already,
        currentUnique.removeTask occurrence, rfl⟩
  have foldFacts (more : List Occurrence)
      (all : ∀ occurrence ∈ more, occurrence ∈ settled) :
      ∀ acc : State × List ExecutionGroupValue × Keys,
        acc.1.HealthyRegisteredTaskAccounting work settled failed
        → acc.1.GroupKeysUnique
        → (more.foldl step acc).1.HealthyRegisteredTaskAccounting
            work settled failed
          ∧ (more.foldl step acc).1.GroupKeysUnique
          ∧ (more.foldl step acc).1.tasks = acc.1.tasks := by
    induction more with
    | nil =>
        intro acc currentAccounting currentUnique
        exact ⟨currentAccounting, currentUnique, rfl⟩
    | cons occurrence rest ih =>
        intro acc currentAccounting currentUnique
        have head : occurrence ∈ settled := all occurrence (by simp)
        have tail : ∀ task ∈ rest, task ∈ settled := by
          intro task member
          exact all task (by simp [member])
        obtain ⟨nextAccounting, nextUnique, nextTasks⟩ :=
          stepFacts acc occurrence head currentAccounting currentUnique
        obtain ⟨finalAccounting, finalUnique, finalTasks⟩ :=
          ih tail (step acc occurrence) nextAccounting nextUnique
        exact ⟨finalAccounting, finalUnique,
          finalTasks.trans nextTasks⟩
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  obtain ⟨flushedAccounting, flushedUnique, flushedTasks⟩ :=
    foldFacts group.tasks all (queue, [], []) accounted unique
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.key != group.group.node.key)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have noFreshContributor : ¬GroupInvalidated work failed group.group.node.key
      → ∀ task ∈ flushed.tasks,
      task.occurrence ∉ settled
      → group.group.node.key ∉ task.groups.map Execution.DeliveryNode.key := by
    intro healthy task taskMember fresh contributor
    have original : task ∈ queue.tasks := by
      rw [flushedTasks] at taskMember
      exact taskMember
    have groupKey : group.group.node.key ∈ healthyContributorKeys
        work failed (task.groups.map Execution.DeliveryNode.key) :=
      mem_healthyContributorKeys_iff.mpr ⟨contributor, healthy⟩
    have linked : task.occurrence ∈ group.tasks :=
      (accounted.taskLinkedOn unique original fresh) group groupMember groupKey
    exact fresh (all task.occurrence linked)
  have currentAccounting : current.HealthyRegisteredTaskAccounting
      work settled failed :=
    flushedAccounting.filterGroupKey_ifHealthy group.group.node.key noFreshContributor
  have currentUnique : current.GroupKeysUnique :=
    flushedUnique.filterGroupNodes _
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.HealthyRegisteredTaskAccounting
    work settled failed
  exact currentAccounting.pruneNonemptyGroups currentUnique children

/-- The older lower-bound interface follows from settled memberships alone.
Witness: `finishSettledGroupSuccess` needs neither the ledger nor closing-group health.
-/
theorem State.HealthyRegisteredTaskAccounting.finishGroupSuccess_ofPendingBound
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (_tracks : queue.HealthyPendingBound work settled failed)
    (unique : queue.GroupKeysUnique)
    (group : GroupNode) (groupMember : group ∈ queue.groupNodes)
    (_healthy : ¬GroupInvalidated work failed group.group.node.key)
    (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.HealthyRegisteredTaskAccounting
        work settled failed :=
  accounted.finishSettledGroupSuccess unique group groupMember all

/-- The exact-ledger specialization follows from the lower-bound preservation witness. -/
theorem State.HealthyRegisteredTaskAccounting.finishGroupSuccess
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (unique : queue.GroupKeysUnique)
    (group : GroupNode) (groupMember : group ∈ queue.groupNodes)
    (healthy : ¬GroupInvalidated work failed group.group.node.key)
    (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.HealthyRegisteredTaskAccounting
        work settled failed := by
  exact accounted.finishGroupSuccess_ofPendingBound tracks.toBound unique group groupMember
    healthy all

/-- Sequential successful group releases preserve the registered-task
accounting invariant, including child-group pruning. -/
theorem State.HealthyRegisteredTaskAccounting.releaseTaskGroups
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (rootsHealthy : queue.RootGroupsHealthy work failed)
    (unique : queue.GroupKeysUnique)
    (groups : List Execution.DeliveryNode)
    : let final :=
        groups.foldl
          (fun (acc : State × List WorkQueueEvent × NewWork) group =>
            let (current, events, released) := acc
            match current.groupNode? group.key with
            | none => (current, events, released)
            | some node =>
                if current.rootGroups.contains group.key && node.pending == 0 then
                  let (next, finished, newWork) := current.finishGroupSuccess node
                  (
                    next,
                    events ++ finished,
                    ⟨
                      released.newGroups ++ newWork.newGroups,
                      released.newStreams ++ newWork.newStreams
                    ⟩
                  )
                else
                  (current, events, released))
          (queue, [], {})
      final.1.HealthyRegisteredTaskAccounting work settled failed := by
  let step (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent × NewWork :=
    let (current, events, released) := acc
    match current.groupNode? group.key with
    | none => (current, events, released)
    | some node =>
        if current.rootGroups.contains group.key && node.pending == 0 then
          let (next, finished, newWork) := current.finishGroupSuccess node
          (next, events ++ finished,
            ⟨released.newGroups ++ newWork.newGroups,
              released.newStreams ++ newWork.newStreams⟩)
        else (current, events, released)
  have stepFacts (acc : State × List WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode)
      (currentAccounting : acc.1.HealthyRegisteredTaskAccounting work settled failed)
      (currentTracks : acc.1.HealthyPendingTracks work settled failed)
      (currentRoots : acc.1.RootGroupsHealthy work failed)
      (currentUnique : acc.1.GroupKeysUnique)
      : (step acc group).1.HealthyRegisteredTaskAccounting work settled failed
        ∧ (step acc group).1.HealthyPendingTracks work settled failed
        ∧ (step acc group).1.RootGroupsHealthy work failed
        ∧ (step acc group).1.GroupKeysUnique := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [step]
    split
    · exact ⟨currentAccounting, currentTracks, currentRoots, currentUnique⟩
    · rename_i node found
      split
      · rename_i ready
        have active : node.group.node.key ∈ current.rootGroups := by
          have root := (Bool.and_eq_true_iff.mp ready).1
          rw [current.groupNode?_key found]
          exact List.contains_iff_mem.mp root
        have zero : node.pending = 0 :=
          beq_iff_eq.mp (Bool.and_eq_true_iff.mp ready).2
        have nodeMember : node ∈ current.groupNodes :=
          List.mem_of_find?_eq_some found
        have healthy : ¬GroupInvalidated work failed node.group.node.key :=
          currentRoots node.group.node.key active
        have all := GroupNode.PendingTracks.allSettled node settled
          (currentTracks node nodeMember healthy) zero
        exact ⟨currentAccounting.finishGroupSuccess currentTracks currentUnique
            node nodeMember healthy all,
          currentTracks.finishGroupSuccess node all,
          currentRoots.finishGroupSuccess node,
          currentUnique.finishGroupSuccess node⟩
      · exact ⟨currentAccounting, currentTracks, currentRoots, currentUnique⟩
  have foldFacts (more : List Execution.DeliveryNode) :
      ∀ acc : State × List WorkQueueEvent × NewWork,
        acc.1.HealthyRegisteredTaskAccounting work settled failed
        → acc.1.HealthyPendingTracks work settled failed
        → acc.1.RootGroupsHealthy work failed
        → acc.1.GroupKeysUnique
        → (more.foldl step acc).1.HealthyRegisteredTaskAccounting
            work settled failed
          ∧ (more.foldl step acc).1.HealthyPendingTracks work settled failed
          ∧ (more.foldl step acc).1.RootGroupsHealthy work failed
          ∧ (more.foldl step acc).1.GroupKeysUnique := by
    induction more with
    | nil =>
        intro acc currentAccounting currentTracks currentRoots currentUnique
        exact ⟨currentAccounting, currentTracks, currentRoots, currentUnique⟩
    | cons group rest ih =>
        intro acc currentAccounting currentTracks currentRoots currentUnique
        obtain ⟨nextAccounting, nextTracks, nextRoots, nextUnique⟩ :=
          stepFacts acc group currentAccounting currentTracks currentRoots currentUnique
        exact ih (step acc group) nextAccounting nextTracks nextRoots nextUnique
  exact (foldFacts groups (queue, [], {}) accounted tracks rootsHealthy unique).1

/-- Pending-count decrements also preserve uniqueness of live group keys. -/
theorem State.GroupKeysUnique.settleTaskGroups
    {queue : State} (unique : queue.GroupKeysUnique)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl
        (fun current group =>
          match current.groupNode? group.key with
          | none => current
          | some node => current.putGroupNode { node with pending := node.pending - 1 })
        queue).GroupKeysUnique := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some node => current.putGroupNode { node with pending := node.pending - 1 }
  have stepUnique (current : State) (group : Execution.DeliveryNode)
      (currentUnique : current.GroupKeysUnique)
      : (step current group).GroupKeysUnique := by
    unfold step
    split
    · exact currentUnique
    · exact currentUnique.putGroupNode _
  have foldUnique (more : List Execution.DeliveryNode) :
      ∀ current : State,
        current.GroupKeysUnique
        → (more.foldl step current).GroupKeysUnique := by
    induction more with
    | nil => intro current currentUnique; exact currentUnique
    | cons group rest ih =>
        intro current currentUnique
        exact ih (step current group) (stepUnique current group currentUnique)
  exact foldUnique groups queue unique

/-- The first task-success release preserves registered healthy memberships.
Witness: decrement debt through the interleaved loop and nonempty pruning; recursive
drain preservation is a separate obligation after this activation boundary.
-/
theorem State.HealthyRegisteredTaskAccounting.taskSuccess_release
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (rootsHealthy : queue.RootGroupsHealthy work failed)
    (unique : queue.GroupKeysUnique)
    (occurrence : Occurrence) (result : TaskResult)
    (taskNode : TaskNode) (_found : queue.taskNode? occurrence = some taskNode)
    (covered
      : ∀ task ∈ result.work.tasks,
        ∀ key ∈ task.groups.map Execution.DeliveryNode.key,
          ∃ group ∈ result.work.groups, group.node.key = key)
    (available : queue.ChildGroupsAvailable work failed result.work)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (taskMatching : ∀ task ∈ result.work.tasks, TaskMatches work task)
    (descriptors
      : ∀ group ∈ result.work.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (uniqueContributors : (taskNode.task.groups.map Execution.DeliveryNode.key).Nodup)
    (debt
      : let withValue := queue.putTaskNode { taskNode with value := some result.value }
        let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
        integrated.PendingDebt (fun key => ¬GroupInvalidated work failed key)
          (occurrence :: settled) (taskNode.task.groups.map Execution.DeliveryNode.key))
    : let withValue := queue.putTaskNode { taskNode with value := some result.value }
      let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
      let released := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
      (released.1.startNewWork released.2.2).HealthyRegisteredTaskAccounting
        work (occurrence :: settled) failed := by
  let withValue := queue.putTaskNode { taskNode with value := some result.value }
  have withValueAccounting : withValue.HealthyRegisteredTaskAccounting
      work settled failed := accounted.putTaskNode _
  have withValueKeys : withValue.GroupKeysUnique := unique
  let integrated := (withValue.maybeIntegrateWork result.work (some occurrence)).1
  have integratedAccounting : integrated.HealthyRegisteredTaskAccounting
      work settled failed :=
    withValueAccounting.maybeIntegrateWork withValueKeys result.work
      (some occurrence) covered available cancelled generated taskMatching descriptors
  have integratedRoots : integrated.RootGroupsHealthy work failed := by
    intro key member
    rw [State.maybeIntegrateWork_rootGroups] at member
    exact rootsHealthy key member
  have integratedKeys : integrated.GroupKeysUnique :=
    withValueKeys.maybeIntegrateWork result.work (some occurrence)
  let invariant (current : State) :=
    current.GroupKeysUnique ∧ current.RootGroupsHealthy work failed ∧
      current.HealthyRegisteredTaskAccounting work (occurrence :: settled) failed
  have valid : invariant integrated := ⟨integratedKeys, integratedRoots,
    integratedAccounting.weakenSettled (by intro task member; simp [member])⟩
  have facts := successGroupFold_preserves
    (fun key => ¬GroupInvalidated work failed key) (occurrence :: settled)
    invariant (fun _ valid => valid.1) (fun _ valid => valid.2.1)
    (by
      intro current node valid foundNode
      exact ⟨valid.1.putGroupNode _, valid.2.1,
        valid.2.2.putGroupNodeSameTasks valid.1 node
          (List.mem_of_find?_eq_some foundNode) _ rfl rfl⟩)
    (by
      intro current node remaining valid counts member active zero all
      exact ⟨valid.1.finishGroupSuccess node, valid.2.1.finishGroupSuccess node,
        valid.2.2.finishGroupSuccess_ofPendingBound counts.toBound valid.1
          node member (valid.2.1 _ active) all⟩)
    taskNode.task.groups uniqueContributors (integrated, [], {}) valid debt
  exact facts.1.2.2.startNewWork _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
