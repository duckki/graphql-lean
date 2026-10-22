import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNodeKeys
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Successful draining preserves an already rejection-free active frontier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every active live group has no retained member rejection to replay. -/
def State.NoActiveCachedFailure (queue : State) : Prop :=
  ∀ node ∈ queue.groupNodes,
    node.group.node.ref ∈ queue.rootGroups → queue.rejectedTask? node = none

private def ClearGroups (queue : State) (keep : NodeRef → Prop) : Prop :=
  ∀ group ∈ queue.groupNodes,
    keep group.group.node.ref
    → ∀ task ∈ queue.taskNodes, task.task.occurrence ∈ group.tasks → task.rejection = none

private theorem ClearGroups.mono {queue : State} {keep next : NodeRef → Prop}
    (clear : ClearGroups queue keep) (included : ∀ ref, next ref → keep ref)
    : ClearGroups queue next := by
  intro group member selected
  exact clear group member (included _ selected)

private theorem ClearGroups.startTask {queue : State} {keep}
    (clear : ClearGroups queue keep) (occurrence : Occurrence)
    : ClearGroups (queue.startTask occurrence) keep := by
  unfold State.startTask
  split
  · exact clear
  · split
    · exact clear
    · intro group member selected task included listed
      rcases List.mem_append.mp included with old | fresh
      · exact clear group member selected task old listed
      · obtain rfl := List.mem_singleton.mp fresh
        rfl

private theorem ClearGroups.startTasks {queue : State} {keep}
    (clear : ClearGroups queue keep) (tasks : List Occurrence)
    : ClearGroups (tasks.foldl (fun current task => current.startTask task) queue)
        keep := by
  induction tasks generalizing queue with
  | nil => exact clear
  | cons task rest ih => exact ih (clear.startTask task)

private theorem ClearGroups.removeGroup {queue : State} {keep}
    (clear : ClearGroups queue keep) (ref : NodeRef)
    : ClearGroups (queue.removeGroup ref) keep := by
  intro group member selected task included listed
  exact clear group (List.mem_filter.mp member).1 selected task
    (List.mem_filter.mp included).1 listed

private theorem ClearGroups.startGroup {queue : State} {keep}
    (clear : ClearGroups queue keep) (ref : NodeRef)
    : ClearGroups (queue.startGroup ref).1 keep := by
  unfold State.startGroup
  dsimp only [State.cacheTaskFailures, List.foldl_nil]
  split
  · exact clear
  · split
    · exact clear.startTasks _
    · exact clear.removeGroup _

private theorem ClearGroups.startGroup_selected {queue : State}
    (groups : queue.GroupRefsUnique) (tasks : queue.TaskNodeKeysUnique) (ref : NodeRef)
    : ClearGroups (queue.startGroup ref).1 (· = ref) := by
  cases found : queue.groupNode? ref with
  | none =>
      have empty : ClearGroups queue (· = ref) := by
        intro group member selected task included listed
        have lookup := groups.groupNode?_of_mem member
        rw [selected, found] at lookup
        contradiction
      simpa only [State.startGroup, State.cacheTaskFailures, List.foldl_nil, found]
        using empty
  | some group =>
      unfold State.startGroup
      dsimp only [State.cacheTaskFailures, List.foldl_nil]
      rw [found]
      dsimp only
      split
      · rename_i noErrors
        have empty : ClearGroups queue (· = ref) := by
          intro other member selected task included listed
          have lookup := groups.groupNode?_of_mem member
          rw [selected, found] at lookup
          cases Option.some.inj lookup
          have noMember : (group.tasks.filterMap
              (fun occurrence => (queue.taskNode? occurrence).bind (·.rejection))) = [] :=
            List.isEmpty_iff.mp noErrors
          cases rejected : task.rejection with
          | none => rfl
          | some errors =>
              have cached : errors ∈ group.tasks.filterMap
                  (fun occurrence => (queue.taskNode? occurrence).bind (·.rejection)) := by
                apply List.mem_filterMap.mpr
                exact ⟨task.task.occurrence, listed, by rw [tasks.lookup included]; exact rejected⟩
              rw [noMember] at cached
              cases cached
        exact empty.startTasks _
      · intro other member selected task included listed
        have absent := queue.removeGroup_ownGroupAbsent group.group.node.ref
        have same : group.group.node.ref = ref := State.groupNode?_ref found
        have lookup := (groups.removeGroup group.group.node.ref).groupNode?_of_mem member
        rw [selected, ← same, absent] at lookup
        contradiction

private theorem ClearGroups.startNewWork {queue : State}
    (clear : ClearGroups queue (fun ref => ref ∈ queue.rootGroups))
    (groups : queue.GroupRefsUnique) (tasks : queue.TaskNodeKeysUnique)
    (released : NewWork)
    : (queue.startNewWork released).1.NoActiveCachedFailure := by
  let newRefs := released.newGroups.map Execution.DeliveryNode.ref
  let initial : State := { queue with rootGroups := queue.rootGroups ++ newRefs }
  have fold (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (groups : acc.1.GroupRefsUnique) (tasks : acc.1.TaskNodeKeysUnique)
      {keep : NodeRef → Prop} (clear : ClearGroups acc.1 keep)
      : let final := (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref
          (next, failures ++ queued)) acc).1
        ClearGroups final (fun ref => keep ref ∨ ref ∈ refs) := by
    induction refs generalizing acc keep with
    | nil => simpa only [List.foldl_nil, List.not_mem_nil, or_false] using clear
    | cons ref rest ih =>
        have next : ClearGroups (acc.1.startGroup ref).1
            (fun other => keep other ∨ other = ref) := by
          intro group member selected
          rcases selected with old | same
          · exact clear.startGroup ref group member old
          · exact ClearGroups.startGroup_selected groups tasks ref group member same
        have keys := tasks.startGroup ref
        have refs : (acc.1.startGroup ref).1.GroupRefsUnique :=
          groups.sublist ((acc.1.startGroup_groupNodes_sublist ref []).map _)
        have restClear := ih ((acc.1.startGroup ref).1, acc.2 ++ (acc.1.startGroup ref).2)
          refs keys next
        exact restClear.mono (fun other included => by
          rcases included with old | listed
          · exact .inl (.inl old)
          · rcases List.mem_cons.mp listed with same | later
            · exact .inl (.inr same)
            · exact .inr later)
  let started := (newRefs.foldl (fun (current, failures) ref =>
    let (next, queued) := current.startGroup ref
    (next, failures ++ queued)) (initial, [])).1
  have cleared : ClearGroups started
      (fun ref => ref ∈ queue.rootGroups ∨ ref ∈ newRefs) :=
    fold newRefs (initial, []) groups tasks clear
  have streams (refs : NodeRefs) (current : State)
      (clear : ClearGroups current (fun ref => ref ∈ queue.rootGroups ∨ ref ∈ newRefs))
      : ClearGroups (refs.foldl State.startStream current)
          (fun ref => ref ∈ queue.rootGroups ∨ ref ∈ newRefs) := by
    induction refs generalizing current with
    | nil => exact clear
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact clear
  have final := streams (released.newStreams.map Execution.DeliveryNode.ref) started cleared
  intro group member active
  apply State.rejectedTask?_eq_none_iff.mpr
  intro occurrence listed task found
  have included := (State.taskNode?_some found).1
  have identity := (State.taskNode?_some found).2
  exact final group member
    (List.mem_append.mp
      ((queue.startNewWork_rootGroups_sublist released []).subset active))
    task included (identity ▸ listed)

private theorem ClearGroups.removeTask {queue : State} {keep}
    (clear : ClearGroups queue keep) (occurrence : Occurrence)
    : ClearGroups (queue.removeTask occurrence) keep := by
  intro group member selected task included listed
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact clear old oldMember selected task (List.mem_filter.mp included).1
    (List.mem_filter.mp listed).1

private theorem ClearGroups.pruneEmptyGroups {queue : State} {keep}
    (clear : ClearGroups queue keep) (groups : List Execution.DeliveryNode)
    : ClearGroups (queue.pruneEmptyGroups groups).1 keep := by
  intro group member selected task included listed
  rw [State.pruneEmptyGroups_taskNodes] at included
  exact clear group (queue.pruneEmptyGroups_groupNodes_sublist groups |>.subset member)
    selected task included listed

private theorem ClearGroups.finishGroupSuccess {queue : State} {keep}
    (clear : ClearGroups queue keep) (group : GroupNode)
    : ClearGroups (queue.finishGroupSuccess group).1 keep := by
  let step := fun (acc : State × List Execution.ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence) =>
    match acc.1.taskNode? occurrence with
    | none => acc
    | some task =>
        (acc.1.removeTask occurrence,
          match task.value with
          | none => acc.2.1
          | some value => acc.2.1 ++ [value],
          acc.2.2 ++ task.childStreams)
  have fold (tasks : List Occurrence) (acc : State × List Execution.ExecutionGroupValue × NodeRefs)
      (clear : ClearGroups acc.1 keep)
      : ClearGroups (tasks.foldl step acc).1 keep := by
    induction tasks generalizing acc with
    | nil => exact clear
    | cons task rest ih =>
        apply ih
        dsimp only [step]
        split
        · exact clear
        · exact clear.removeTask task
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have initial : ClearGroups flushed keep := fold group.tasks (queue, [], []) clear
  let closed : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have filtered : ClearGroups closed keep := by
    intro node member selected task included listed
    exact initial node (List.mem_filter.mp member).1 selected task included listed
  exact filtered.pruneEmptyGroups _

private theorem State.NoActiveCachedFailure.clearGroups {queue : State}
    (clear : queue.NoActiveCachedFailure) (unique : queue.TaskNodeKeysUnique)
    : ClearGroups queue (fun ref => ref ∈ queue.rootGroups) := by
  intro group member active task included listed
  exact State.rejectedTask?_eq_none_iff.mp (clear group member active)
    task.task.occurrence listed task (unique.lookup included)

private theorem ClearGroups.noActiveCachedFailure {queue : State}
    (clear : ClearGroups queue (fun ref => ref ∈ queue.rootGroups))
    : queue.NoActiveCachedFailure := by
  intro group member active
  apply State.rejectedTask?_eq_none_iff.mpr
  intro occurrence listed task found
  exact clear group member active task (State.taskNode?_some found).1
    ((State.taskNode?_some found).2 ▸ listed)

private theorem ClearGroups.putGroupNode {queue : State} {keep}
    (clear : ClearGroups queue keep) (updated : GroupNode)
    (clean
      : keep updated.group.node.ref
        → ∀ task ∈ queue.taskNodes,
            task.task.occurrence ∈ updated.tasks → task.rejection = none)
    : ClearGroups (queue.putGroupNode updated) keep := by
  intro group member selected task included listed
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst group
    exact clean selected task included listed
  · subst group
    exact clear old oldMember selected task included listed

private theorem ClearGroups.appendEmpty {queue : State} {keep}
    (clear : ClearGroups queue keep) (group : Group) (registeredGroups : NodeRefs)
    : ClearGroups
        ({
              queue with
                registeredGroups := registeredGroups
                groupNodes := queue.groupNodes ++ [{ group }]
            }
          : State)
        keep := by
  intro node member selected task included listed
  rcases List.mem_append.mp member with old | fresh
  · exact clear node old selected task included listed
  · obtain rfl := List.mem_singleton.mp fresh
    cases listed

private theorem ClearGroups.addGroup {queue : State} {keep}
    (clear : ClearGroups queue keep) (group : Group)
    : ClearGroups (queue.addGroup group) keep := by
  unfold State.addGroup
  split
  · exact clear
  · split
    · exact clear.appendEmpty group _
    · split
      · split <;> exact clear
      · rename_i node found
        apply (clear.appendEmpty group _).putGroupNode _
        exact clear node (List.mem_of_find?_eq_some found)

private theorem ClearGroups.addGroups {queue : State} {keep}
    (clear : ClearGroups queue keep) (groups : List Group)
    : ClearGroups (queue.addGroups groups).1 keep :=
  State.addGroups_preserves (fun current => ClearGroups current keep) groups
    (fun _ group _ current => current.addGroup group) queue clear

private theorem ClearGroups.addTask {queue : State} {keep}
    (clear : ClearGroups queue keep) (incoming : Task)
    (clean
      : ∀ task ∈ queue.taskNodes,
          task.task.occurrence = incoming.occurrence → task.rejection = none)
    : ClearGroups (queue.addTask incoming) keep := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains incoming.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [incoming.occurrence], pending := node.pending + 1 }
  have fold (groups : List Execution.DeliveryNode) (current : State)
      (clear : ClearGroups current keep)
      (clean : ∀ task ∈ current.taskNodes,
        task.task.occurrence = incoming.occurrence → task.rejection = none)
      : ClearGroups (groups.foldl step current) keep
        ∧ (groups.foldl step current).taskNodes = current.taskNodes := by
    induction groups generalizing current with
    | nil => exact ⟨clear, rfl⟩
    | cons group rest ih =>
        have next : ClearGroups (step current group) keep := by
          unfold step
          split
          · exact clear
          · rename_i node found
            split
            · exact clear
            · apply clear.putGroupNode
              intro selected task included listed
              rcases List.mem_append.mp listed with old | fresh
              · exact clear node (List.mem_of_find?_eq_some found) selected task included old
              · exact clean task included (List.mem_singleton.mp fresh)
        have same : (step current group).taskNodes = current.taskNodes := by
          unfold step
          split
          · rfl
          · split <;> rfl
        have result := ih (step current group) next (same ▸ clean)
        exact ⟨result.1, result.2.trans same⟩
  let registered : State := { queue with tasks := queue.tasks ++ [incoming] }
  let current := incoming.groups.foldl step registered
  have result := fold incoming.groups registered clear clean
  change ClearGroups (if incoming.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? incoming.occurrence).isNone then
    { current with taskNodes := current.taskNodes ++ [({ task := incoming } : TaskNode)] }
    else current) keep
  split
  · intro group member selected task included listed
    rcases List.mem_append.mp included with old | fresh
    · exact result.1 group member selected task old listed
    · obtain rfl := List.mem_singleton.mp fresh
      rfl
  · exact result.1

private theorem ClearGroups.putTaskNode {queue : State} {keep}
    (clear : ClearGroups queue keep) (updated : TaskNode)
    (clean
      : ∀ group ∈ queue.groupNodes,
          keep group.group.node.ref
          → updated.task.occurrence ∈ group.tasks
          → updated.rejection = none)
    : ClearGroups (queue.putTaskNode updated) keep := by
  intro group member selected task included listed
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp included
  split at same
  · subst task
    exact clean group member selected listed
  · subst task
    exact clear group member selected old oldMember listed

private theorem ClearGroups.addStreams {queue : State} {keep}
    (clear : ClearGroups queue keep) (streams : List Stream)
    (producer : Option Occurrence)
    : ClearGroups (queue.addStreams streams producer).1 keep := by
  unfold State.addStreams
  dsimp only
  split
  · exact clear
  · split
    · exact clear
    · rename_i node found
      exact clear.putTaskNode _ (fun group member selected listed =>
        clear group member selected node (List.mem_of_find?_eq_some found) listed)

/-- Integrating fresh child tasks preserves a clear active frontier.
Witness: cached rejections exclude the incoming task identities; registration adds empty
records and membership entries only for those clean tasks. No activation occurs here.
-/
theorem State.NoActiveCachedFailure.maybeIntegrateWork {queue : State}
    (clear : queue.NoActiveCachedFailure) (unique : queue.TaskNodeKeysUnique)
    (more : Work) (producer : Option Occurrence)
    (rejections
      : queue.TaskRejectionsSatisfy
          (fun occurrence _ => ∀ task ∈ more.tasks, occurrence ≠ task.occurrence))
    : (queue.maybeIntegrateWork more producer).1.NoActiveCachedFailure := by
  let keep := fun ref => ref ∈ queue.rootGroups
  have initial := (clear.clearGroups unique).addGroups more.groups
  let registered := (queue.addGroups more.groups).1
  have fold (tasks : List Task) (current : State) (clear : ClearGroups current keep)
      (rejections : current.TaskRejectionsSatisfy
        (fun occurrence _ => ∀ task ∈ more.tasks, occurrence ≠ task.occurrence))
      (known : tasks.Subset more.tasks)
      : ClearGroups (tasks.foldl State.addTask current) keep := by
    induction tasks generalizing current with
    | nil => exact clear
    | cons incoming rest ih =>
        apply ih (current.addTask incoming) ?_ (rejections.addTask incoming)
          (fun task member => known (List.mem_cons_of_mem incoming member))
        apply clear.addTask
        intro task member same
        cases failed : task.rejection with
        | none => rfl
        | some errors =>
            exact False.elim (rejections task member errors failed incoming
              (known List.mem_cons_self) same)
  have final := (fold more.tasks registered initial (rejections.addGroups more.groups)
    (List.Subset.refl _)).addStreams more.streams producer
  apply ClearGroups.noActiveCachedFailure
  intro group member active task included listed
  have previous : group.group.node.ref ∈ queue.rootGroups := by
    rwa [State.maybeIntegrateWork_rootGroups] at active
  exact final group member previous task included listed

/-- Startup preserves clear active owners and removes newly released cached failures.
Witness: unchanged task records stay clear; each new root is inspected before activation.
This statement uses the empty extra cache snapshot.
-/
theorem State.NoActiveCachedFailure.startNewWork {queue : State}
    (clear : queue.NoActiveCachedFailure) (groups : queue.GroupRefsUnique)
    (tasks : queue.TaskNodeKeysUnique) (released : NewWork)
    : (queue.startNewWork released).1.NoActiveCachedFailure :=
  (clear.clearGroups tasks).startNewWork groups tasks released

/-- Successful flushing preserves rejection freedom on the remaining active frontier.
Witness: task removal only filters memberships and live records, while roots shrink.
-/
theorem State.NoActiveCachedFailure.finishGroupSuccess {queue : State}
    (clear : queue.NoActiveCachedFailure) (tasks : queue.TaskNodeKeysUnique)
    (group : GroupNode)
    : (queue.finishGroupSuccess group).1.NoActiveCachedFailure :=
  (((clear.clearGroups tasks).finishGroupSuccess group).mono
    (fun _ active =>
      queue.finishGroupSuccess_rootsSubset group active)).noActiveCachedFailure

/-- A rejection-free active frontier remains rejection-free through successful draining.
Witness: flushing only removes task memberships; startup inspects a released group's
cached rejections before starting its private tasks. The initial frontier must already
be clear: draining does not consume pending FIFO task-failure notifications.
-/
theorem State.NoActiveCachedFailure.drainReadyGroups {queue : State}
    (clear : queue.NoActiveCachedFailure) (groups : queue.GroupRefsUnique)
    (tasks : queue.TaskNodeKeysUnique)
    : queue.drainReadyGroups.1.NoActiveCachedFailure := by
  have loop (fuel : Nat) (current : State) (clear : current.NoActiveCachedFailure)
      (groups : current.GroupRefsUnique) (tasks : current.TaskNodeKeysUnique)
      : (State.drainReadyGroups.go [] fuel current).1.NoActiveCachedFailure := by
    induction fuel generalizing current with
    | zero => exact clear
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact clear
        · rename_i node selected
          let closed := (current.finishGroupSuccess node).1
          have next : ClearGroups closed (fun ref => ref ∈ closed.rootGroups) :=
            ((clear.clearGroups tasks).finishGroupSuccess node).mono
              (fun ref active => current.finishGroupSuccess_rootsSubset node active)
          exact ih _ (next.startNewWork (groups.finishGroupSuccess node)
              (tasks.finishGroupSuccess node) _)
            ((groups.finishGroupSuccess node).startNewWork _)
            ((tasks.finishGroupSuccess node).startNewWork _)
  exact loop _ queue clear groups tasks

/-- Successful settlement preserves clear active owners when incoming children are clean.
Witness: child integration excludes old rejected identities, contributor updates retain
membership lists, and successful flush/startup/drain preserve the clear frontier.
-/
theorem State.NoActiveCachedFailure.taskSuccess_of_cleanChildren {queue : State}
    (clear : queue.NoActiveCachedFailure) (groups : queue.GroupRefsUnique)
    (tasks : queue.TaskNodeKeysUnique) (occurrence : Occurrence) (result : TaskResult)
    (rejections
      : queue.TaskRejectionsSatisfy
          (fun occurrence _ => ∀ task ∈ result.work.tasks, occurrence ≠ task.occurrence))
    : (queue.taskSuccess occurrence result).1.NoActiveCachedFailure := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using clear
  | some taskNode =>
      let stored := queue.putTaskNode { taskNode with value := some result.value }
      have storedClear : stored.NoActiveCachedFailure := by
        apply ClearGroups.noActiveCachedFailure
        exact (clear.clearGroups tasks).putTaskNode _
          (fun group member selected listed =>
            (clear.clearGroups tasks) group member selected taskNode
              (List.mem_of_find?_eq_some found) listed)
      have storedRejections := rejections.putTaskNode
        { taskNode with value := some result.value }
        (rejections taskNode (List.mem_of_find?_eq_some found))
      have initial := storedClear.maybeIntegrateWork (tasks.putTaskNode _)
        result.work (some occurrence) storedRejections
      let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
      have fold (refs : List Execution.DeliveryNode)
          (acc : State × List Execution.WorkQueueEvent × NewWork)
          (clear : acc.1.NoActiveCachedFailure) (groups : acc.1.GroupRefsUnique)
          (tasks : acc.1.TaskNodeKeysUnique)
          : (refs.foldl successGroupStep acc).1.NoActiveCachedFailure
            ∧ (refs.foldl successGroupStep acc).1.GroupRefsUnique
            ∧ (refs.foldl successGroupStep acc).1.TaskNodeKeysUnique := by
        induction refs generalizing acc with
        | nil => exact ⟨clear, groups, tasks⟩
        | cons ref rest ih =>
            apply ih
            all_goals
              obtain ⟨current, events, released⟩ := acc
              dsimp only [successGroupStep]
              split
              · assumption
              · rename_i node found
                have updatedClear : (current.putGroupNode
                    { node with pending := node.pending - 1 }).NoActiveCachedFailure :=
                  ((clear.clearGroups tasks).putGroupNode
                    { node with pending := node.pending - 1 }
                    ((clear.clearGroups tasks) node
                      (List.mem_of_find?_eq_some found))).noActiveCachedFailure
                have updatedGroups := groups.putGroupNode
                  { node with pending := node.pending - 1 }
                have updatedTasks := tasks.putGroupNode
                  { node with pending := node.pending - 1 }
                split
                · first
                  | exact updatedClear.finishGroupSuccess updatedTasks _
                  | exact updatedGroups.finishGroupSuccess _
                  | exact updatedTasks.finishGroupSuccess _
                · assumption
      have final := fold taskNode.task.groups (integrated, [], {}) initial
        ((show stored.GroupRefsUnique from groups).maybeIntegrateWork result.work
          (some occurrence))
        ((tasks.putTaskNode _).maybeIntegrateWork result.work (some occurrence))
      rw [queue.taskSuccess_eq occurrence result taskNode found]
      exact (final.1.startNewWork final.2.1 final.2.2 _).drainReadyGroups
        (final.2.1.startNewWork _) (final.2.2.startNewWork _)

/-- Pruning empty shells preserves rejection freedom on active owners.
Witness: surviving group records and task nodes are unchanged, as are active root refs.
-/
theorem State.NoActiveCachedFailure.pruneEmptyGroups {queue : State}
    (clear : queue.NoActiveCachedFailure) (unique : queue.TaskNodeKeysUnique)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.NoActiveCachedFailure := by
  apply ClearGroups.noActiveCachedFailure
  apply ((clear.clearGroups unique).pruneEmptyGroups groups).mono
  intro ref member
  rwa [State.pruneEmptyGroups_rootGroups] at member

/-- Item integration preserves a clear frontier when all incoming children are clean.
Witness: rejection provenance excludes the supplied child identities across the whole
item fold; each integration, pruning, startup and successful drain preserves clarity.
-/
theorem State.NoActiveCachedFailure.streamItems_of_cleanChildren {queue : State}
    (clear : queue.NoActiveCachedFailure) (groups : queue.GroupRefsUnique)
    (tasks : queue.TaskNodeKeysUnique) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (rejections
      : queue.TaskRejectionsSatisfy
          (fun occurrence _ =>
            ∀ item ∈ items, ∀ task ∈ item.work.tasks, occurrence ≠ task.occurrence))
    : (queue.streamItems stream items).1.NoActiveCachedFailure := by
  let property := fun occurrence (_ : Nat) =>
    ∀ item ∈ items, ∀ task ∈ item.work.tasks, occurrence ≠ task.occurrence
  have fold (remaining : List StreamItem)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List Execution.StreamItemValue × List GroupFailureEvent)
      (clear : acc.1.NoActiveCachedFailure) (groups : acc.1.GroupRefsUnique)
      (tasks : acc.1.TaskNodeKeysUnique) (rejections : acc.1.TaskRejectionsSatisfy property)
      (included : remaining.Subset items)
      : let final := (remaining.foldl (fun acc item => streamItemStep acc item) acc).1
        final.NoActiveCachedFailure ∧ final.GroupRefsUnique ∧ final.TaskNodeKeysUnique := by
    induction remaining generalizing acc with
    | nil => exact ⟨clear, groups, tasks⟩
    | cons item rest ih =>
        let integrated := acc.1.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        let released : NewWork := { integrated.2 with newGroups := pruned.2 }
        have incoming := rejections.mono (fun occurrence errors rejected task member =>
          rejected item (included List.mem_cons_self) task member)
        have integratedClear := clear.maybeIntegrateWork tasks item.work none incoming
        have integratedGroups := groups.maybeIntegrateWork item.work
        have integratedTasks := tasks.maybeIntegrateWork item.work
        have prunedClear := integratedClear.pruneEmptyGroups integratedTasks integrated.2.newGroups
        have prunedGroups := integratedGroups.pruneEmptyGroups integrated.2.newGroups
        have prunedTasks := integratedTasks.pruneEmptyGroups integrated.2.newGroups
        have started := prunedClear.startNewWork prunedGroups prunedTasks released
        have supported := ((rejections.maybeIntegrateWork item.work).pruneEmptyGroups
          integrated.2.newGroups).startNewWork released
        exact ih (streamItemStep acc item) started (prunedGroups.startNewWork released)
          (prunedTasks.startNewWork released) supported
          (fun item member => included (List.mem_cons_of_mem _ member))
  rw [queue.streamItems_eq stream items]
  split
  · exact clear
  · have final := fold items (queue, [], [], [], []) clear groups tasks rejections
      (List.Subset.refl _)
    exact final.1.drainReadyGroups final.2.1 final.2.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
