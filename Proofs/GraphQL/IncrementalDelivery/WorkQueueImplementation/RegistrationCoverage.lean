import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationProvenance

/-! Permanent registration covers live groups and every integrated task contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The registry includes live nodes, even when registration is skipped on lookup
-----------------------------------------------------------------------------------------

/-- Every live group node's ref is recorded in the permanent registration registry. -/
def State.LiveGroupsRegistered (queue : State) : Prop :=
  ∀ node ∈ queue.groupNodes, node.group.node.ref ∈ queue.registeredGroups

/-- Every permanent task contributor has a permanent group registration.
The contributor need not still have a live node or an open notice. -/
def State.TaskGroupsRegistered (queue : State) : Prop :=
  ∀ task ∈ queue.tasks,
  ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref, ref ∈ queue.registeredGroups

/-- A preserved predicate extends through a finite state fold.
Witness: induction over inputs, retaining the actual intermediate state. -/
private theorem fold_preserves {α β : Type} (step : β → α → β) (property : β → Prop)
    (preserved : ∀ state item, property state → property (step state item))
    (items : List α) (state : β) (initial : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact initial
  | cons item rest ih => exact ih _ (preserved state item initial)

/-- Metadata replacement preserves registry coverage when the replacement ref is known.
Witness: each output node is either unchanged or has the supplied registered ref. -/
theorem State.LiveGroupsRegistered.putGroupNode {queue : State}
    (registered : queue.LiveGroupsRegistered) (updated : GroupNode)
    (known : updated.group.node.ref ∈ queue.registeredGroups)
    : (queue.putGroupNode updated).LiveGroupsRegistered := by
  intro node member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact known
  · subst node; exact registered old oldMember

/-- Registration preserves old registry entries and records the supplied group ref.
Witness: a skipped live lookup is already registered; a new group appends its ref. -/
private theorem State.addGroup_registration {queue : State}
    (registered : queue.LiveGroupsRegistered) (group : Group)
    : (queue.addGroup group).LiveGroupsRegistered
      ∧ queue.registeredGroups.Subset (queue.addGroup group).registeredGroups
      ∧ group.node.ref ∈ (queue.addGroup group).registeredGroups := by
  unfold State.addGroup
  split
  · rename_i old
    refine ⟨registered, fun _ member => member, ?_⟩
    have options : group.node.ref ∈ queue.registeredGroups
        ∨ (queue.groupNode? group.node.ref).isSome = true := by simpa using old
    rcases options with known | live
    · exact known
    · cases found : queue.groupNode? group.node.ref with
      | none => simp [found] at live
      | some node =>
          rw [← State.groupNode?_ref found]
          exact registered node (List.mem_of_find?_eq_some found)
  · dsimp only
    split
    · exact ⟨fun node member => List.mem_append_left _ (registered node member),
        List.subset_append_left _ _, by simp⟩
    · refine ⟨?_, List.subset_append_left _ _, by simp⟩
      intro node member
      rcases List.mem_append.mp member with old | added
      · exact List.mem_append_left _ (registered node old)
      · have same := List.mem_singleton.mp added
        subst node
        simp

/-- Group integration preserves live-ref coverage, retains every old registry entry,
and records all supplied candidates, including reused descriptors.
Witness: the fresh registration fold and the registry-neutral parent-link fold. -/
theorem State.addGroups_registration {queue : State}
    (registered : queue.LiveGroupsRegistered) (groups : List Group)
    : (queue.addGroups groups).1.LiveGroupsRegistered
      ∧ queue.registeredGroups.Subset (queue.addGroups groups).1.registeredGroups
      ∧ ∀ group ∈ groups,
          group.node.ref ∈ (queue.addGroups groups).1.registeredGroups := by
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  have register (more : List Group) {current : State}
      (coverage : current.LiveGroupsRegistered)
      : (more.foldl State.addGroup current).LiveGroupsRegistered
        ∧ current.registeredGroups.Subset (more.foldl State.addGroup current).registeredGroups
        ∧ ∀ group ∈ more,
            group.node.ref ∈ (more.foldl State.addGroup current).registeredGroups := by
    induction more generalizing current with
    | nil => exact ⟨coverage, fun _ member => member, by simp⟩
    | cons group rest ih =>
        obtain ⟨covered, earlier, added⟩ := current.addGroup_registration coverage group
        obtain ⟨final, retained, all⟩ := ih covered
        refine ⟨final, earlier.trans retained, ?_⟩
        intro candidate member
        rcases List.mem_cons.mp member with same | later
        · subst candidate; exact retained added
        · exact all candidate later
  let link (current : State) (group : Group) : State :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.ref then node.childGroups
              else node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have linkPreserves (current : State) (group : Group)
      (coverage : current.LiveGroupsRegistered)
      : (link current group).LiveGroupsRegistered
        ∧ (link current group).registeredGroups = current.registeredGroups := by
    unfold link
    split
    · exact ⟨coverage, rfl⟩
    · split
      · exact ⟨coverage, rfl⟩
      · rename_i node found
        exact ⟨coverage.putGroupNode _ (coverage node (List.mem_of_find?_eq_some found)), rfl⟩
  obtain ⟨withGroups, included, allFresh⟩ := register fresh registered
  let initial := fresh.foldl State.addGroup queue
  have linked := fold_preserves link
    (fun current => current.LiveGroupsRegistered
      ∧ current.registeredGroups = initial.registeredGroups)
    (fun current group prior =>
      ⟨(linkPreserves current group prior.1).1,
        (linkPreserves current group prior.1).2.trans prior.2⟩)
    fresh initial ⟨withGroups, rfl⟩
  change (fresh.foldl link initial).LiveGroupsRegistered ∧ _
  refine ⟨linked.1, linked.2 ▸ included, ?_⟩
  intro group member
  change group.node.ref ∈ (fresh.foldl link initial).registeredGroups
  rw [linked.2]
  by_cases prior : group.node.ref ∈ queue.registeredGroups
  · exact included prior
  · have missing : queue.groupNode? group.node.ref = none := by
      cases found : queue.groupNode? group.node.ref with
      | none => rfl
      | some node =>
          exact False.elim (prior ((State.groupNode?_ref found) ▸
            registered node (List.mem_of_find?_eq_some found)))
    exact allFresh group (by simp [fresh, member, prior, missing])

/-- Linking a task changes counters and memberships but not live refs or the registry.
Witness: each updated node keeps the registered ref returned by its lookup. -/
private theorem State.LiveGroupsRegistered.addTask {queue : State}
    (registered : queue.LiveGroupsRegistered) (task : Task)
    : (queue.addTask task).LiveGroupsRegistered := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved (current : State) (group : Execution.DeliveryNode)
      (covered : current.LiveGroupsRegistered) : (step current group).LiveGroupsRegistered := by
    unfold step
    split
    · exact covered
    · rename_i node found
      split
      · exact covered
      · exact covered.putGroupNode _ (covered node (List.mem_of_find?_eq_some found))
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have covered : current.LiveGroupsRegistered :=
    fold_preserves step State.LiveGroupsRegistered preserved task.groups _ registered
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).LiveGroupsRegistered
  split <;> exact covered

-----------------------------------------------------------------------------------------
-- Complete immediate integration records all task contributors
-----------------------------------------------------------------------------------------

/-- Work integration extends registry coverage to every new task contributor.
Witness: register the covered groups first, then append tasks without changing registry
entries or live refs. No generated-work, health, or success assumption is used. -/
theorem State.maybeIntegrateWork_registration {queue : State}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (work : Work)
    (covered
      : ∀ task ∈ work.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ∃ group ∈ work.groups, group.node.ref = ref)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.LiveGroupsRegistered
      ∧ (queue.maybeIntegrateWork work parentTask).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.maybeIntegrateWork work parentTask).1.registeredGroups := by
  let grouped := (queue.addGroups work.groups).1
  let tasked := work.tasks.foldl State.addTask grouped
  obtain ⟨groupCoverage, earlier, all⟩ := queue.addGroups_registration live work.groups
  have afterTasks : tasked.LiveGroupsRegistered
      ∧ tasked.registeredGroups = grouped.registeredGroups :=
    fold_preserves State.addTask
      (fun current => current.LiveGroupsRegistered
        ∧ current.registeredGroups = grouped.registeredGroups)
      (fun current task prior => ⟨prior.1.addTask task,
        (current.addTask_registeredGroups task).trans prior.2⟩)
      work.tasks grouped ⟨groupCoverage, rfl⟩
  have afterStreams : (queue.maybeIntegrateWork work parentTask).1.LiveGroupsRegistered
      ∧ (queue.maybeIntegrateWork work parentTask).1.registeredGroups
          = grouped.registeredGroups := by
    change (tasked.addStreams work.streams parentTask).1.LiveGroupsRegistered
      ∧ (tasked.addStreams work.streams parentTask).1.registeredGroups = grouped.registeredGroups
    unfold State.addStreams
    split
    · exact afterTasks
    · dsimp
      split <;> exact afterTasks
  refine ⟨afterStreams.1, ?_, afterStreams.2 ▸ earlier⟩
  intro task member ref contributes
  rw [State.maybeIntegrateWork_tasks_append] at member
  rw [afterStreams.2]
  rcases List.mem_append.mp member with old | new
  · exact earlier (tasks task old ref contributes)
  · obtain ⟨group, groupMember, same⟩ := covered task new ref contributes
    exact same ▸ all group groupMember

-----------------------------------------------------------------------------------------
-- Activation and cancellation retain the permanent registry
-----------------------------------------------------------------------------------------

/-- Starting work does not modify permanent group registrations.
Witness: the task/group/stream activation folds change only active roots and task nodes.
-/
theorem State.startNewWork_registeredGroups (queue : State) (work : NewWork)
    : (queue.startNewWork work).registeredGroups = queue.registeredGroups := by
  have task (current : State) (occurrence : Occurrence)
      : (current.startTask occurrence).registeredGroups = current.registeredGroups := by
    unfold State.startTask
    split
    · rfl
    · split <;> rfl
  have group (current : State) (ref : NodeRef)
      : (current.startGroup ref).registeredGroups = current.registeredGroups := by
    unfold State.startGroup
    split
    · rfl
    · split
      · rfl
      · exact fold_preserves State.startTask
          (fun state => state.registeredGroups = current.registeredGroups)
          (fun state occurrence prior => (task state occurrence).trans prior) _ current rfl
  have stream (current : State) (ref : NodeRef)
      : (current.startStream ref).registeredGroups = current.registeredGroups := by
    unfold State.startStream
    split <;> rfl
  unfold State.startNewWork
  apply fold_preserves State.startStream
    (fun state => state.registeredGroups = queue.registeredGroups)
    (fun state ref prior => (stream state ref).trans prior)
  exact fold_preserves State.startGroup
    (fun state => state.registeredGroups = queue.registeredGroups)
    (fun state ref prior => (group state ref).trans prior) _ _ rfl

/-- Pruning preserves live/task registry coverage and the exact permanent registry.
Witness: each recursive removal only filters live nodes; task definitions remain stored.
-/
theorem State.pruneEmptyGroups_registration {queue : State}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.LiveGroupsRegistered
      ∧ (queue.pruneEmptyGroups groups).1.TaskGroupsRegistered
      ∧ (queue.pruneEmptyGroups groups).1.registeredGroups = queue.registeredGroups := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (covered : current.LiveGroupsRegistered) (taskCoverage : current.TaskGroupsRegistered)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.LiveGroupsRegistered
        ∧ (State.pruneEmptyGroups.go fuel current remaining kept).1.TaskGroupsRegistered
        ∧ (State.pruneEmptyGroups.go fuel current remaining kept).1.registeredGroups
            = current.registeredGroups := by
    induction fuel generalizing current remaining kept with
    | zero => exact ⟨covered, taskCoverage, rfl⟩
    | succ fuel ih =>
        cases remaining with
        | nil => exact ⟨covered, taskCoverage, rfl⟩
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ covered taskCoverage
            · split
              · exact ih _ _ _ (fun node member => covered node (List.mem_filter.mp member).1)
                  taskCoverage
              · exact ih _ _ _ covered taskCoverage
  exact loop _ queue groups [] live tasks

/-- Activation retains registry coverage of live groups and permanent tasks.
Witness: its exact group/task/registry projection equations. -/
theorem State.startNewWork_registration {queue : State}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (work : NewWork)
    : (queue.startNewWork work).LiveGroupsRegistered
      ∧ (queue.startNewWork work).TaskGroupsRegistered := by
  constructor
  · intro node member
    rw [(queue.startNewWork_groupCore work).1] at member
    rw [State.startNewWork_registeredGroups]
    exact live node member
  · intro task member ref contributor
    rw [(queue.startNewWork_groupCore work).2.1] at member
    rw [State.startNewWork_registeredGroups]
    exact tasks task member ref contributor

/-- Initial lowering records every contributor ref, even for groups later pruned.
Witness: immediate lowering covers task contributors, followed by pruning and activation.
No generated-work metadata or initialization-admission premise is needed. -/
theorem createWorkQueue_registration (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).LiveGroupsRegistered
      ∧ (State.initialize (Work.fromExecution work)).TaskGroupsRegistered := by
  have integrated := State.maybeIntegrateWork_registration
    (queue := {}) (by intro node member; cases member)
    (by intro task member; cases member) (Work.fromExecution work)
    (workFromSpec_immediateGroupsCoverTasks work [])
  have pruned := State.pruneEmptyGroups_registration integrated.1 integrated.2.1
    (({} : State).maybeIntegrateWork (Work.fromExecution work)).2.newGroups
  exact State.startNewWork_registration pruned.1 pruned.2.1 _

/-- Failure cleanup retains registry coverage and every permanent registration.
Witness: each contributor removal filters live nodes, without deleting task definitions
or registry entries. This requires no source validity or generated-work assumption. -/
theorem State.taskFailure_registration {queue : State}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.LiveGroupsRegistered
      ∧ (queue.taskFailure occurrence errors).1.TaskGroupsRegistered
      ∧ (queue.taskFailure occurrence errors).1.registeredGroups
        = queue.registeredGroups := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    let (current, events) := acc
    match current.groupNode? group.ref with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.ref then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else (current.putGroupNode
          { node with
            pending := node.pending - 1
            failure := some (node.failure.getD 0 + errors) }, events)
  let property (acc : State × List WorkQueueEvent) := acc.1.LiveGroupsRegistered
    ∧ acc.1.TaskGroupsRegistered ∧ acc.1.registeredGroups = queue.registeredGroups
  have removed (current : State) (ref : NodeRef) (prior : property (current, []))
      : property (current.removeGroup ref, []) := by
    exact ⟨fun node member => prior.1 node (List.mem_filter.mp member).1, prior.2⟩
  have preserved (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (prior : property acc) : property (step acc group) := by
    obtain ⟨current, events⟩ := acc
    dsimp only [step]
    split
    · exact prior
    · rename_i node found
      split
      · exact removed current _ prior
      · exact ⟨prior.1.putGroupNode _
          (prior.1 node (List.mem_of_find?_eq_some found)), prior.2⟩
  unfold State.taskFailure
  split
  · exact ⟨live, tasks, rfl⟩
  · split
    · refine ⟨?_, tasks, rfl⟩
      intro node member
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      exact live old oldMember
    apply fold_preserves step property preserved
    refine ⟨?_, tasks, rfl⟩
    intro node member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    exact live old oldMember

/-- Proof notation for one stream-item integration, before the handler's final drain.
Witness: this is the literal integration, pruning, and activation step in `streamItems`.
-/
def State.integrateStreamItem (queue : State) (item : StreamItem) : State :=
  let (integrated, newWork) := queue.maybeIntegrateWork item.work
  let (pruned, groups) := integrated.pruneEmptyGroups newWork.newGroups
  pruned.startNewWork { newWork with newGroups := groups }

/-- One matched stream item extends both registry coverage facts monotonically.
Witness: contributor coverage from source matching, followed by pruning and activation.
-/
theorem State.integrateStreamItem_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : (queue.integrateStreamItem item).LiveGroupsRegistered
      ∧ (queue.integrateStreamItem item).TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.integrateStreamItem item).registeredGroups := by
  have integrated := queue.maybeIntegrateWork_registration live tasks item.work
    (matching.streamItem_childTasksCovered member)
  have pruned := State.pruneEmptyGroups_registration integrated.1 integrated.2.1
    (queue.maybeIntegrateWork item.work).2.newGroups
  have started := State.startNewWork_registration pruned.1 pruned.2.1
    { (queue.maybeIntegrateWork item.work).2 with
      newGroups := ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
        (queue.maybeIntegrateWork item.work).2.newGroups).2 }
  refine ⟨started.1, started.2, ?_⟩
  unfold State.integrateStreamItem
  rw [State.startNewWork_registeredGroups, pruned.2.2]
  exact integrated.2.2

-----------------------------------------------------------------------------------------
-- Successful settlements preserve coverage while registering their child work
-----------------------------------------------------------------------------------------

/-- Successful group cleanup never changes the permanent task registry.
Witness: flushing removes live task nodes only, and pruning preserves registered tasks. -/
theorem State.finishGroupSuccess_tasks (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.tasks = queue.tasks := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    match acc.1.taskNode? occurrence with
    | none => acc
    | some node =>
        let values := match node.value with
          | none => acc.2.1
          | some value => acc.2.1 ++ [value]
        (acc.1.removeTask occurrence, values, acc.2.2 ++ node.childStreams)
  have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      : (tasks.foldl step acc).1.tasks = acc.1.tasks := by
    induction tasks generalizing acc with
    | nil => rfl
    | cons task rest ih =>
        rw [List.foldl_cons, ih]
        unfold step
        split <;> rfl
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  change (current.pruneEmptyGroups
    (group.childGroups.filterMap (fun ref =>
      (current.groupNode? ref).map (fun node => node.group.node)))).1.tasks = queue.tasks
  rw [State.pruneEmptyGroups_tasks]
  exact loop group.tasks (queue, [], [])

/-- Successful flushing retains registry coverage and the exact permanent registry.
Witness: task removal preserves node refs; closing and pruning only filter live nodes. -/
theorem State.finishGroupSuccess_registration {queue : State}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (group : GroupNode)
    : (queue.finishGroupSuccess group).1.LiveGroupsRegistered
      ∧ (queue.finishGroupSuccess group).1.TaskGroupsRegistered
      ∧ (queue.finishGroupSuccess group).1.registeredGroups = queue.registeredGroups := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (task : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? task with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask task, values, streams ++ taskNode.childStreams)
  let property (acc : State × List ExecutionGroupValue × NodeRefs) :=
    acc.1.LiveGroupsRegistered ∧ acc.1.TaskGroupsRegistered
      ∧ acc.1.registeredGroups = queue.registeredGroups
  have preserved (acc : State × List ExecutionGroupValue × NodeRefs) (task : Occurrence)
      (prior : property acc) : property (step acc task) := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact prior
    · refine ⟨?_, prior.2⟩
      intro node member
      obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
      subst node
      exact prior.1 old oldMember
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedCovered := fold_preserves step property preserved
    group.tasks (queue, [], []) ⟨live, tasks, rfl⟩
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentLive : current.LiveGroupsRegistered :=
    fun node member => flushedCovered.1 node (List.mem_filter.mp member).1
  have pruned := current.pruneEmptyGroups_registration currentLive flushedCovered.2.1
    (group.childGroups.filterMap
      (fun ref => (current.groupNode? ref).map (fun node => node.group.node)))
  exact ⟨pruned.1, pruned.2.1, pruned.2.2.trans flushedCovered.2.2⟩

/-- Recursive release preserves registry coverage and every permanent registration.
Witness: drain induction; successful closure and activation preserve the registry,
while failed closure filters only live nodes and started tasks.
-/
theorem State.drainReadyGroups_registration {queue : State}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    : queue.drainReadyGroups.1.LiveGroupsRegistered
      ∧ queue.drainReadyGroups.1.TaskGroupsRegistered
      ∧ queue.drainReadyGroups.1.registeredGroups = queue.registeredGroups := by
  apply State.drainReadyGroups_preserves
    (fun current =>
      current.LiveGroupsRegistered
      ∧ current.TaskGroupsRegistered
      ∧ current.registeredGroups = queue.registeredGroups)
    (by
      intro current node prior _ _ _ _
      have closed := current.finishGroupSuccess_registration prior.1 prior.2.1 node
      have started := State.startNewWork_registration closed.1 closed.2.1
        (current.finishGroupSuccess node).2.2
      refine ⟨started.1, started.2, ?_⟩
      rw [State.startNewWork_registeredGroups, closed.2.2, prior.2.2])
    (by
      intro current node errors prior _ _ _
      exact ⟨fun other member => prior.1 other (List.mem_filter.mp member).1, prior.2⟩)
    ⟨live, tasks, rfl⟩

/-- Task success preserves coverage and can only enlarge the permanent registry.
Witness: covered child integration, the actual single-pass contributor fold, and
registry-neutral activation. Matching supplies coverage without any health premise. -/
theorem State.taskSuccess_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    {occurrence : Occurrence} {result : TaskResult}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : (queue.taskSuccess occurrence result).1.LiveGroupsRegistered
      ∧ (queue.taskSuccess occurrence result).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.taskSuccess occurrence result).1.registeredGroups := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa [State.taskSuccess, found]
        using And.intro live
          (And.intro tasks
            (show queue.registeredGroups.Subset queue.registeredGroups from fun _
                member =>
              member))
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · refine ⟨?_, tasks, fun _ member => member⟩
        intro group member
        obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
        exact live old oldMember
      let stored := queue.putTaskNode { node with value := some result.value }
      have storedLive : stored.LiveGroupsRegistered := live
      have storedTasks : stored.TaskGroupsRegistered := tasks
      let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
      have integratedCovered := stored.maybeIntegrateWork_registration
        storedLive storedTasks result.work matching.childTasksCovered (some occurrence)
      let property (acc : State × List WorkQueueEvent × NewWork) :=
        acc.1.LiveGroupsRegistered ∧ acc.1.TaskGroupsRegistered
          ∧ acc.1.registeredGroups = integrated.registeredGroups
      have preserved (acc : State × List WorkQueueEvent × NewWork)
          (group : Execution.DeliveryNode) (prior : property acc)
          : property (successGroupStep acc group) := by
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact prior
        · rename_i groupNode found
          have updatedLive := prior.1.putGroupNode
            { groupNode with pending := groupNode.pending - 1 }
            (prior.1 groupNode (List.mem_of_find?_eq_some found))
          split
          · have finished := State.finishGroupSuccess_registration updatedLive prior.2.1
              { groupNode with pending := groupNode.pending - 1 }
            exact ⟨finished.1, finished.2.1, finished.2.2.trans prior.2.2⟩
          · exact ⟨updatedLive, prior.2⟩
      let folded := node.task.groups.foldl successGroupStep (integrated, [], {})
      have final := fold_preserves successGroupStep property preserved
        node.task.groups (integrated, [], {})
        ⟨integratedCovered.1, integratedCovered.2.1, rfl⟩
      have activated := State.startNewWork_registration final.1 final.2.1 folded.2.2
      have drained := State.drainReadyGroups_registration activated.1 activated.2
      refine ⟨drained.1, drained.2.1, ?_⟩
      rw [drained.2.2, State.startNewWork_registeredGroups, final.2.2]
      exact integratedCovered.2.2

-----------------------------------------------------------------------------------------
-- Coverage and registry monotonicity hold for every matching replay
-----------------------------------------------------------------------------------------

/-- Streaming extends registration monotonically at every actual intermediate item.
Witness: the itemwise integration theorem, including pruning and activation. -/
theorem State.streamItems_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.streamItems stream items).1.LiveGroupsRegistered
      ∧ (queue.streamItems stream items).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.streamItems stream items).1.registeredGroups := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  let property (current : State) := current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ queue.registeredGroups.Subset current.registeredGroups
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : property acc.1) : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        have next := acc.1.integrateStreamItem_registration prior.1 prior.2.1
          matching (included List.mem_cons_self)
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          ⟨next.1, next.2.1, prior.2.2.trans next.2.2⟩
  unfold State.streamItems
  split
  · exact ⟨live, tasks, fun _ member => member⟩
  · have folded := loop items (fun _ member => member) (queue, [], [], [])
      ⟨live, tasks, fun _ member => member⟩
    have drained := State.drainReadyGroups_registration folded.1 folded.2.1
    exact ⟨drained.1, drained.2.1, drained.2.2 ▸ folded.2.2⟩

/-- Every matching graph event preserves coverage and all existing registrations.
Witness: successful integration, failure cleanup, or stream-only closure. No generated
work, start discipline, freshness, root health, or admission premise is needed. -/
theorem State.handleGraphEvent_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.LiveGroupsRegistered
      ∧ (queue.handleGraphEvent event).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.handleGraphEvent event).1.registeredGroups := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_registration live tasks matching
  | taskFailure occurrence errors =>
      obtain ⟨nextLive, nextTasks, same⟩ := queue.taskFailure_registration live tasks
        occurrence errors
      exact ⟨nextLive, nextTasks, same ▸ (fun _ member => member)⟩
  | streamItems stream items => exact queue.streamItems_registration live tasks matching
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact ⟨live, tasks, fun _ member => member⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact ⟨live, tasks, fun _ member => member⟩

/-- Batch handling retains coverage and never forgets an earlier registration.
Witness: the executable event fold; termination changes neither registry projection. -/
theorem State.handleGraphEvents_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.LiveGroupsRegistered
      ∧ (queue.handleGraphEvents events).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.handleGraphEvents events).1.registeredGroups := by
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  let property (current : State) := current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ queue.registeredGroups.Subset current.registeredGroups
  have loop (more : List GraphEvent) (included : more.Subset events)
      (acc : State × List WorkQueueEvent) (prior : property acc.1)
      : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons event rest ih =>
        have next := acc.1.handleGraphEvent_registration prior.1 prior.2.1 event
          (matching event (included List.mem_cons_self))
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          ⟨next.1, next.2.1, prior.2.2.trans next.2.2⟩
  have folded := loop events (fun _ member => member) (queue, [])
    ⟨live, tasks, fun _ member => member⟩
  unfold State.handleGraphEvents
  split
  · exact ⟨live, tasks, fun _ member => member⟩
  · dsimp only
    split <;> exact folded

/-- Publisher normalization preserves coverage and monotonically extends registrations.
Witness: induction through matching batches, including batches ignored after termination.
-/
theorem State.runNormalized_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    : (queue.runNormalized batches).1.LiveGroupsRegistered
      ∧ (queue.runNormalized batches).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.runNormalized batches).1.registeredGroups := by
  let property (current : State) := current.LiveGroupsRegistered
    ∧ current.TaskGroupsRegistered ∧ queue.registeredGroups.Subset current.registeredGroups
  have stepCovered (acc : NormalizedAcc) (batch : List GraphEvent)
      (batchMatch : ∀ event ∈ batch, event.MatchesWork work) (prior : property acc.1)
      : property (normalizedStep acc batch).1 := by
    obtain ⟨current, publisher, outputs⟩ := acc
    have next := current.handleGraphEvents_registration prior.1 prior.2.1 batch batchMatch
    have covered : property (current.handleGraphEvents batch).1 :=
      ⟨next.1, next.2.1, prior.2.2.trans next.2.2⟩
    unfold normalizedStep
    dsimp only
    split <;> exact covered
  have loop (more : List (List GraphEvent)) (included : more.Subset batches)
      (acc : NormalizedAcc) (prior : property acc.1)
      : property (more.foldl normalizedStep acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (stepCovered acc batch (matching batch (included List.mem_cons_self)) prior)
  exact loop batches (fun _ member => member)
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, [])
    ⟨live, tasks, fun _ member => member⟩

/-- All live nodes and permanent task contributors stay registered during valid replay.
Witness: initialization followed by matching-event preservation, including arbitrary
successes, failures, and streamed child work. No generated-work or acceptance premise. -/
theorem createWorkQueue_runNormalized_registration
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : let queue := (State.initialize (Work.fromExecution work)).runNormalized batches
      queue.1.LiveGroupsRegistered
      ∧ queue.1.TaskGroupsRegistered
      ∧ (State.initialize (Work.fromExecution work)).registeredGroups.Subset
          queue.1.registeredGroups :=
  State.runNormalized_registration (createWorkQueue_registration work).1
    (createWorkQueue_registration work).2 batches
    (fun _ batchMember _ eventMember =>
      valid.eachMatches (List.mem_flatten.mpr ⟨_, batchMember, eventMember⟩))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
