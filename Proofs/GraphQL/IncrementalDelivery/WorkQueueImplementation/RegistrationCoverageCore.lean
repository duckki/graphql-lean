import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DeclarationLowering

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
  · have old : ({ queue with
        registeredGroups := queue.registeredGroups ++ [group.node.ref] } : State).LiveGroupsRegistered :=
      fun node member => List.mem_append_left _ (registered node member)
    have appended : ({ queue with
        registeredGroups := queue.registeredGroups ++ [group.node.ref],
        groupNodes := queue.groupNodes ++ [({ group } : GroupNode)] } : State).LiveGroupsRegistered := by
      intro node member
      rcases List.mem_append.mp member with earlier | added
      · exact List.mem_append_left _ (registered node earlier)
      · cases List.mem_singleton.mp added
        simp
    split
    · exact ⟨appended, List.subset_append_left _ _, by simp⟩
    · split
      · split <;> exact ⟨old, List.subset_append_left _ _, by simp⟩
      · rename_i node found
        exact ⟨appended.putGroupNode _ (List.mem_append_left _
          (registered node (List.mem_of_find?_eq_some found))), List.subset_append_left _ _,
          by simp [State.putGroupNode]⟩

/-- One immediate installation permanently registers every resulting live record. -/
theorem State.LiveGroupsRegistered.addGroup {queue : State}
    (registered : queue.LiveGroupsRegistered) (group : Group)
    : (queue.addGroup group).LiveGroupsRegistered :=
  (State.addGroup_registration registered group).1

/-- Recursive registration retains old refs and accounts for every visited candidate.
Refs already in the incoming visited set may still be awaiting their ancestor caller's install.
-/
theorem State.addGroups.go_registration (candidates : List Group) (fuel : Nat)
    (queue : State) (roots : List Execution.DeliveryNode) (visited : NodeRefs)
    (group : Group) (registered : queue.LiveGroupsRegistered)
    : let next := State.addGroups.go candidates fuel (queue, roots, visited) group
      next.1.LiveGroupsRegistered
      ∧ queue.registeredGroups ⊆ next.1.registeredGroups
      ∧ (∀ ref ∈ next.2.2, ref ∈ next.1.registeredGroups ∨ ref ∈ visited)
      ∧ (0 < fuel
          → group.node.ref ∈ next.1.registeredGroups ∨ group.node.ref ∈ visited) := by
  induction fuel generalizing queue roots visited group with
  | zero => exact ⟨registered, List.Subset.refl _, fun _ member => Or.inr member,
      fun positive => by cases positive⟩
  | succ fuel ih =>
      simp only [State.addGroups.go]
      split
      · rename_i seen
        exact ⟨registered, List.Subset.refl _, fun _ member => Or.inr member,
          fun _ => Or.inr (List.contains_iff_mem.mp seen)⟩
      · split
        · rename_i known
          have member : group.node.ref ∈ queue.registeredGroups := by
            rcases Bool.or_eq_true_iff.mp known with prior | live
            · exact List.contains_iff_mem.mp prior
            · obtain ⟨node, found⟩ := Option.isSome_iff_exists.mp live
              exact (State.groupNode?_ref found) ▸
                registered node (List.mem_of_find?_eq_some found)
          refine ⟨registered, List.Subset.refl _, ?_, fun _ => Or.inl member⟩
          intro ref included
          rcases List.mem_append.mp included with old | new
          · exact Or.inr old
          · cases List.mem_singleton.mp new; exact Or.inl member
        · let reached := match group.parent.bind (fun parent =>
                candidates.find? (fun candidate => candidate.node.ref == parent)) with
            | none => (queue, roots, visited ++ [group.node.ref])
            | some parent => State.addGroups.go candidates fuel
                (queue, roots, visited ++ [group.node.ref]) parent
          have prepared : reached.1.LiveGroupsRegistered
              ∧ queue.registeredGroups ⊆ reached.1.registeredGroups
              ∧ ∀ ref ∈ reached.2.2,
                ref ∈ reached.1.registeredGroups ∨ ref ∈ visited ++ [group.node.ref] := by
            dsimp only [reached]
            split
            · exact ⟨registered, List.Subset.refl _, fun _ member => Or.inr member⟩
            · exact ⟨(ih _ _ _ _ registered).1, (ih _ _ _ _ registered).2.1,
                (ih _ _ _ _ registered).2.2.1⟩
          obtain ⟨coverage, included, installed⟩ := reached.1.addGroup_registration prepared.1 group
          refine ⟨coverage, prepared.2.1.trans included, ?_, fun _ => Or.inl installed⟩
          intro ref member
          rcases prepared.2.2 ref member with old | earlier
          · exact Or.inl (included old)
          · rcases List.mem_append.mp earlier with old | new
            · exact Or.inr old
            · cases List.mem_singleton.mp new; exact Or.inl installed

/-- Group integration preserves live-ref coverage, retains every old registry entry,
and records all supplied candidates, including reused descriptors.
Witness: the fresh registration fold and the registry-neutral parent-link fold. -/
theorem State.addGroups_registration {queue : State}
    (registered : queue.LiveGroupsRegistered) (groups : List Group)
    : (queue.addGroups groups).1.LiveGroupsRegistered
      ∧ queue.registeredGroups.Subset (queue.addGroups groups).1.registeredGroups
      ∧ ∀ group ∈ groups,
          group.node.ref ∈ (queue.addGroups groups).1.registeredGroups := by
  let step := fun acc group => State.addGroups.go groups (groups.length + 1) acc group
  have fold (more : List Group) (current : State) (roots : List Execution.DeliveryNode)
      (visited : NodeRefs) (coverage : current.LiveGroupsRegistered)
      (visitedRegistered : visited ⊆ current.registeredGroups)
      : let next := more.foldl step (current, roots, visited)
        next.1.LiveGroupsRegistered ∧ current.registeredGroups ⊆ next.1.registeredGroups
        ∧ next.2.2 ⊆ next.1.registeredGroups
        ∧ ∀ group ∈ more, group.node.ref ∈ next.1.registeredGroups := by
    induction more generalizing current roots visited with
    | nil => exact ⟨coverage, List.Subset.refl _, visitedRegistered, by simp⟩
    | cons group rest ih =>
        let next := step (current, roots, visited) group
        have installed := State.addGroups.go_registration groups (groups.length + 1)
          current roots visited group coverage
        have known : group.node.ref ∈ next.1.registeredGroups :=
          (installed.2.2.2 (by omega)).elim id (fun old => installed.2.1 (visitedRegistered old))
        have allVisited : next.2.2 ⊆ next.1.registeredGroups := fun ref member =>
          (installed.2.2.1 ref member).elim id (fun old => installed.2.1 (visitedRegistered old))
        obtain ⟨covered, retained, seen, all⟩ := ih next.1 next.2.1 next.2.2 installed.1 allVisited
        refine ⟨covered, installed.2.1.trans retained, seen, ?_⟩
        intro candidate member
        rcases List.mem_cons.mp member with same | later
        · subst candidate; exact retained known
        · exact all candidate later
  have result := fold groups queue [] [] registered (by simp)
  exact ⟨result.1, result.2.1, result.2.2.2⟩

/-- Linking a task changes counters and memberships but not live refs or the registry.
Witness: each updated node keeps the registered ref returned by its lookup. -/
theorem State.LiveGroupsRegistered.addTask {queue : State}
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
          ref ∈ queue.registeredGroups ∨ ∃ group ∈ work.groups, group.node.ref = ref)
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
  · rcases covered task new ref contributes with prior | fresh
    · exact earlier prior
    · obtain ⟨group, groupMember, same⟩ := fresh
      exact same ▸ all group groupMember

/-- Task and stream integration preserve the group-registration fold's exact history. -/
theorem State.maybeIntegrateWork_registeredGroups_eq (queue : State) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.registeredGroups
      = (queue.addGroups work.groups).1.registeredGroups := by
  let grouped := (queue.addGroups work.groups).1
  have taskFold (more : List Task) (current : State)
      : (more.foldl State.addTask current).registeredGroups
        = current.registeredGroups := by
    induction more generalizing current with
    | nil => rfl
    | cons task rest ih => rw [List.foldl_cons, ih, State.addTask_registeredGroups]
  change ((work.tasks.foldl State.addTask grouped).addStreams work.streams parentTask).1.registeredGroups
    = grouped.registeredGroups
  unfold State.addStreams
  split
  · exact taskFold _ _
  · dsimp only
    split <;> exact taskFold _ _

/-- Every prior ref and supplied candidate is registered after integration. -/
theorem State.maybeIntegrateWork_registrationContext {queue : State}
    (live : queue.LiveGroupsRegistered) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.registeredGroups ++ DeclarationCoverage.candidateRefs work).Subset
        (queue.maybeIntegrateWork work parentTask).1.registeredGroups := by
  intro ref member
  rw [State.maybeIntegrateWork_registeredGroups_eq queue work parentTask]
  obtain ⟨_, earlier, all⟩ := queue.addGroups_registration live work.groups
  rcases List.mem_append.mp member with prior | candidate
  · exact earlier prior
  · obtain ⟨group, groupMember, rfl⟩ := List.mem_map.mp candidate
    exact all group groupMember

-----------------------------------------------------------------------------------------
-- Activation and cancellation retain the permanent registry
-----------------------------------------------------------------------------------------

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
    (work : NewWork) (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork work available).1.LiveGroupsRegistered
      ∧ (queue.startNewWork work available).1.TaskGroupsRegistered := by
  constructor
  · intro node member
    rw [State.startNewWork_registeredGroups]
    exact live node ((queue.startNewWork_groupNodes_sublist work available).subset member)
  · intro task member ref contributor
    rw [State.startNewWork_tasks] at member
    rw [State.startNewWork_registeredGroups]
    exact tasks task member ref contributor

/-- Exposing rejection caches leaves registry coverage unchanged. -/
theorem State.cacheTaskFailures_registration {queue : State}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).LiveGroupsRegistered
      ∧ (queue.cacheTaskFailures available).TaskGroupsRegistered := by
  constructor
  · intro node member
    rw [State.cacheTaskFailures_registeredGroups]
    rw [State.cacheTaskFailures_groupNodes] at member
    exact live node member
  · intro task member ref contributor
    rw [State.cacheTaskFailures_tasks] at member
    rw [State.cacheTaskFailures_registeredGroups]
    exact tasks task member ref contributor

/-- Initial lowering records every contributor ref, even for groups later pruned.
Witness: immediate lowering covers task contributors, followed by pruning and activation.
The declaration certificate comes from execution and adds no source premise. -/
theorem createWorkQueue_registration (work : Execution.Work)
    (certified : DeclarationCoverage.Certified [] work)
    : (State.initialize (Work.fromExecution work)).LiveGroupsRegistered
      ∧ (State.initialize (Work.fromExecution work)).TaskGroupsRegistered := by
  dsimp only [State.initialize, State.enqueueGroupFailures, State.LiveGroupsRegistered,
    State.TaskGroupsRegistered]
  have integrated := State.maybeIntegrateWork_registration
    (queue := {}) (by intro node member; cases member)
    (by intro task member; cases member) (Work.fromExecution work)
    (fun task member ref contributes => by
      have covered := certified.immediate [] member contributes
      exact .inr (List.mem_map.mp ((List.mem_append.mp covered).resolve_left (by simp))))
  have pruned := State.pruneEmptyGroups_registration integrated.1 integrated.2.1
    (({} : State).maybeIntegrateWork (Work.fromExecution work)).2.newGroups
  let integratedWork := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  have started := State.startNewWork_registration pruned.1 pruned.2.1
    { integratedWork.2 with
      newGroups := (integratedWork.1.pruneEmptyGroups integratedWork.2.newGroups).2 }
  constructor
  · intro node member
    exact started.1 node member
  · intro task member ref contributes
    exact started.2 task member ref contributes

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
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskFailure, found]
      exact ⟨live, tasks, trivial⟩
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves
        (fun state => state.LiveGroupsRegistered ∧ state.TaskGroupsRegistered
          ∧ state.registeredGroups = queue.registeredGroups)
        (fun _ _ prior => ⟨fun other member => prior.1 other (List.mem_filter.mp member).1,
          prior.2⟩) _ _ _ ⟨live, tasks, rfl⟩

/-- Proof notation for one stream-item integration, before the handler's final drain.
Witness: this is the literal integration, pruning, and activation step in `streamItems`.
-/
def State.integrateStreamItem (queue : State) (item : StreamItem)
    (available : List (Occurrence × Nat) := [])
    : State :=
  let (integrated, newWork) := queue.maybeIntegrateWork item.work
  let (pruned, groups) := integrated.pruneEmptyGroups newWork.newGroups
  (pruned.startNewWork { newWork with newGroups := groups } available).1

/-- One matched stream item extends both registry coverage facts monotonically.
Witness: contributor coverage from source matching, followed by pruning and activation.
-/
theorem State.integrateStreamItem_registration_of_certificate
    {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (item : StreamItem)
    (certificate
      : DeclarationCoverage.WorkCertificate work queue.registeredGroups item.work)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).LiveGroupsRegistered
      ∧ (queue.integrateStreamItem item available).TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.integrateStreamItem item available).registeredGroups := by
  have integrated := queue.maybeIntegrateWork_registration live tasks item.work
    certificate.contributors
  have pruned := State.pruneEmptyGroups_registration integrated.1 integrated.2.1
    (queue.maybeIntegrateWork item.work).2.newGroups
  have started := State.startNewWork_registration pruned.1 pruned.2.1
    { (queue.maybeIntegrateWork item.work).2 with
      newGroups := ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
        (queue.maybeIntegrateWork item.work).2.newGroups).2 } available
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
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.LiveGroupsRegistered
      ∧ (queue.drainReadyGroups available).1.TaskGroupsRegistered
      ∧ (queue.drainReadyGroups available).1.registeredGroups
        = queue.registeredGroups := by
  apply State.drainReadyGroups_preserves
    (fun current => current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
      ∧ current.registeredGroups = queue.registeredGroups)
    (available := available) (valid := ⟨live, tasks, rfl⟩)
  intro current node prior _ _ _
  have closed := current.finishGroupSuccess_registration prior.1 prior.2.1 node
  have started := State.startNewWork_registration closed.1 closed.2.1
    (current.finishGroupSuccess node).2.2 available
  refine ⟨started.1, started.2, ?_⟩
  rw [State.startNewWork_registeredGroups, closed.2.2, prior.2.2]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
