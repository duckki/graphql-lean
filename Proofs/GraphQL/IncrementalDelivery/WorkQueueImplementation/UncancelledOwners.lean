import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredRecordHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm

/-! Cancellation-aware owner evidence for the interval between cache exposure and notification.
These predicates and preservation lemmas concern existing queue records only.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)

/-- Every unsettled registered task retains each contributor that has not been cancelled.
Unlike failure-indexed owner accounting, cancellation here follows the actual queue even
when startup removed a group before its source failure notification was consumed.
-/
def State.UncancelledTaskAccounting (queue : State) (settled : List Occurrence) : Prop :=
  ∀ task ∈ queue.tasks,
    task.occurrence ∉ settled
    → ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
        ref ∉ queue.cancelledGroups
        → ∃ node ∈ queue.groupNodes,
            node.group.node.ref = ref ∧ task.occurrence ∈ node.tasks

/-- Enlarging consumed settlements weakens the remaining owner obligation. -/
theorem State.UncancelledTaskAccounting.weakenSettled {queue : State} {before after}
    (prior : queue.UncancelledTaskAccounting before) (included : before.Subset after)
    : queue.UncancelledTaskAccounting after := by
  intro task member fresh ref contributes uncancelled
  exact prior task member (fun settled => fresh (included settled)) ref contributes uncancelled

/-- Initialization has every contributor linked, independently of failure metadata. -/
theorem createWorkQueue_uncancelledTaskAccounting (work : Execution.Work)
    (generated : ExecutedWork work)
    : (State.initialize (Work.fromExecution work)).UncancelledTaskAccounting [] := by
  intro task member fresh ref contributes _
  exact createWorkQueue_healthyRegisteredTaskAccounting work generated task member fresh ref contributes
    (fun invalid => invalid.nonempty rfl)

/-- Cache exposure preserves the cancellation-aware owner certificate. -/
theorem State.UncancelledTaskAccounting.cacheTaskFailures {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).UncancelledTaskAccounting settled := by
  simpa only [State.UncancelledTaskAccounting, State.cacheTaskFailures_tasks,
    State.cacheTaskFailures_cancelledGroups, State.cacheTaskFailures_groupNodes]
    using prior

/-- Computation replacement leaves contributor membership and cancellation unchanged. -/
theorem State.UncancelledTaskAccounting.putTaskNode {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (updated : TaskNode)
    : (queue.putTaskNode updated).UncancelledTaskAccounting settled :=
  prior

/-- A single uncancelled contributor has the complete membership link used by registration. -/
theorem State.UncancelledTaskAccounting.linkedAt {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (unique : queue.GroupRefsUnique)
    {task : Task} (registered : task ∈ queue.tasks) (fresh : task.occurrence ∉ settled)
    {ref : NodeRef} (contributes : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    (uncancelled : ref ∉ queue.cancelledGroups)
    : queue.TaskLinkedOn task.occurrence [ref] := by
  intro node member selected
  have same := List.mem_singleton.mp selected
  obtain ⟨owner, ownerMember, identity, linked⟩ :=
    prior task registered fresh ref contributes uncancelled
  have equal := unique.sameNode ownerMember member (identity.trans same.symm)
  exact equal ▸ linked

/-- Registering group candidates retains each old uncancelled contributor and its link. -/
theorem State.UncancelledTaskAccounting.addGroups {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (unique : queue.GroupRefsUnique)
    (groups : List Group)
    : (queue.addGroups groups).1.UncancelledTaskAccounting settled := by
  intro task registered fresh ref contributes uncancelled
  rw [State.addGroups_tasks] at registered
  have oldUncancelled : ref ∉ queue.cancelledGroups := fun member =>
    uncancelled (queue.addGroups_cancelledGroups_subset groups member)
  obtain ⟨owner, ownerMember, identity, _⟩ :=
    prior task registered fresh ref contributes oldUncancelled
  have linked := (prior.linkedAt unique registered fresh contributes oldUncancelled).addGroups
    unique groups (by
      intro group _ selected
      have same := List.mem_singleton.mp selected
      exact ⟨owner, ownerMember, identity.trans same.symm⟩)
  obtain ⟨node, member, same⟩ := List.mem_map.mp (queue.addGroups_includesRefs groups ref
    (List.mem_map.mpr ⟨owner, ownerMember, identity⟩))
  exact ⟨node, member, same, linked node member (List.mem_singleton.mpr same)⟩

/-- Task registration preserves old links and installs every new uncancelled owner link. -/
theorem State.UncancelledTaskAccounting.addTask {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (unique : queue.GroupRefsUnique)
    (task : Task)
    (present
      : ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ref ∉ queue.cancelledGroups
          → ∃ node ∈ queue.groupNodes, node.group.node.ref = ref)
    : (queue.addTask task).UncancelledTaskAccounting settled := by
  intro other registered fresh ref contributes uncancelled
  rw [State.addTask_tasks] at registered
  rw [State.addTask_cancelledGroups] at uncancelled
  rcases List.mem_append.mp registered with old | new
  · obtain ⟨owner, ownerMember, identity, _⟩ :=
      prior other old fresh ref contributes uncancelled
    have linked := (prior.linkedAt unique old fresh contributes uncancelled).addTask unique task
    obtain ⟨node, member, same⟩ := List.mem_map.mp (queue.addTask_includesRefs task ref
      (List.mem_map.mpr ⟨owner, ownerMember, identity⟩))
    exact ⟨node, member, same, linked node member (List.mem_singleton.mpr same)⟩
  · have sameTask : other = task := List.mem_singleton.mp new
    subst other
    obtain ⟨owner, ownerMember, identity⟩ := present ref contributes uncancelled
    obtain ⟨node, member, same⟩ := List.mem_map.mp (queue.addTask_includesRefs task ref
      (List.mem_map.mpr ⟨owner, ownerMember, identity⟩))
    exact ⟨node, member, same,
      queue.addTask_links unique task node member (same.symm ▸ contributes)⟩

/-- Source attachment leaves registered task definitions and group memberships intact. -/
theorem State.UncancelledTaskAccounting.addStreams {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (streams : List Stream)
    (producer : Option Occurrence := none)
    : (queue.addStreams streams producer).1.UncancelledTaskAccounting settled := by
  intro task registered fresh ref contributes uncancelled
  rw [State.addStreams_tasks] at registered
  rw [State.addStreams_cancelledGroups] at uncancelled
  unfold State.addStreams
  split
  · exact prior task registered fresh ref contributes uncancelled
  · dsimp only
    split <;> exact prior task registered fresh ref contributes uncancelled

/-- Integrating tasks retains uncancelled owners when their installed groups are present.
Witness: the group stage retains old links; the task fold installs every remaining
uncancelled contributor membership. Callers must derive presence at the actual completed
registration boundary, including refusal below successfully retired parents.
-/
theorem State.UncancelledTaskAccounting.maybeIntegrateWork_of_present {queue : State}
    {settled} (prior : queue.UncancelledTaskAccounting settled)
    (unique : queue.GroupRefsUnique) (incoming : Work)
    (producer : Option Occurrence := none)
    (present
      : ∀ task ∈ incoming.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ref ∉ (queue.addGroups incoming.groups).1.cancelledGroups
          → ref
            ∈ (queue.addGroups incoming.groups).1.groupNodes.map
                (fun node => node.group.node.ref))
    : (queue.maybeIntegrateWork incoming producer).1.UncancelledTaskAccounting
        settled := by
  let grouped := (queue.addGroups incoming.groups).1
  have fold (tasks : List Task) (included : tasks.Subset incoming.tasks) (current : State)
      (accounted : current.UncancelledTaskAccounting settled) (keys : current.GroupRefsUnique)
      (refs : grouped.GroupRefsIncluded current)
      (cancelled : current.cancelledGroups = grouped.cancelledGroups)
      : (tasks.foldl State.addTask current).UncancelledTaskAccounting settled := by
    induction tasks generalizing current with
    | nil => exact accounted
    | cons task rest ih =>
        have taskPresent : ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
            ref ∉ current.cancelledGroups
              → ∃ node ∈ current.groupNodes, node.group.node.ref = ref := by
          intro ref contributes uncancelled
          have groupedUncancelled : ref ∉ grouped.cancelledGroups := by
            rwa [cancelled] at uncancelled
          have live := present task (included List.mem_cons_self) ref contributes groupedUncancelled
          exact List.mem_map.mp (refs ref live)
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (current.addTask task) (accounted.addTask keys task taskPresent)
          (keys.addTask task) (refs.trans (current.addTask_includesRefs task))
        exact (current.addTask_cancelledGroups task).trans cancelled
  have registered := fold incoming.tasks (List.Subset.refl _) grouped
    (prior.addGroups unique incoming.groups) (unique.addGroups incoming.groups)
    (by intro ref member; exact member) rfl
  exact registered.addStreams incoming.streams producer

/-- Owner metadata replacement preserves the same task memberships. -/
theorem State.UncancelledTaskAccounting.putGroupNodeSameTasks {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (unique : queue.GroupRefsUnique)
    (old : GroupNode) (member : old ∈ queue.groupNodes) (updated : GroupNode)
    (sameRef : updated.group.node.ref = old.group.node.ref)
    (sameTasks : updated.tasks = old.tasks)
    : (queue.putGroupNode updated).UncancelledTaskAccounting settled := by
  intro task registered fresh ref contributes uncancelled
  obtain ⟨node, live, identity, linked⟩ := prior task registered fresh ref contributes uncancelled
  by_cases same : node.group.node.ref = old.group.node.ref
  · have equal := unique.sameNode live member same
    subst node
    refine ⟨updated, ?_, sameRef.trans identity, ?_⟩
    · exact List.mem_map.mpr ⟨old, member, by
        simp only [sameRef, beq_self_eq_true, ↓reduceIte]⟩
    · rw [sameTasks]
      exact linked
  · refine ⟨node, ?_, identity, linked⟩
    exact List.mem_map.mpr ⟨node, live, by
      simp only [sameRef, beq_iff_eq, same, ↓reduceIte]⟩

/-- Actual group removal cancels every removed owner and retains every other membership.
No failure-inventory equality or source-notification premise is used.
-/
theorem State.UncancelledTaskAccounting.removeGroup {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (root : NodeRef)
    : (queue.removeGroup root).UncancelledTaskAccounting settled := by
  intro task registered fresh ref contributes uncancelled
  have oldUncancelled : ref ∉ queue.cancelledGroups := fun member =>
    uncancelled (List.mem_append_left _ member)
  obtain ⟨node, member, same, linked⟩ :=
    prior task registered fresh ref contributes oldUncancelled
  refine ⟨node, List.mem_filter.mpr ⟨member, ?_⟩, same, linked⟩
  have absent : ref ∉ State.removeGroup.collect (queue.groupNodes.length + 1) queue [root] [] :=
    fun removed => uncancelled (List.mem_append_right _ removed)
  simp only [same, List.contains_eq_mem, absent, decide_false, Bool.not_false]

/-- Empty-shell pruning cannot remove an unsettled task's listed contributor. -/
theorem State.UncancelledTaskAccounting.pruneEmptyGroups {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.UncancelledTaskAccounting settled := by
  intro task registered fresh ref contributes uncancelled
  rw [State.pruneEmptyGroups_tasks] at registered
  rw [State.pruneEmptyGroups_cancelledGroups] at uncancelled
  obtain ⟨node, member, same, linked⟩ := prior task registered fresh ref contributes uncancelled
  obtain ⟨retained, live, identity, _⟩ :=
    queue.pruneEmptyGroups_preservesNonempty groups unique
      ⟨node, member, same, List.ne_nil_of_mem linked⟩
  have oldMember := (queue.pruneEmptyGroups_groupNodes_sublist groups).subset live
  have equal := unique.sameNode oldMember member (identity.trans same.symm)
  exact ⟨retained, live, identity, equal.symm ▸ linked⟩

/-- Removing an already consumed task preserves all still-unsettled owner links. -/
theorem State.UncancelledTaskAccounting.removeSettledTask {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (occurrence : Occurrence)
    (consumed : occurrence ∈ settled)
    : (queue.removeTask occurrence).UncancelledTaskAccounting settled := by
  intro task registered fresh ref contributes uncancelled
  obtain ⟨node, member, identity, linked⟩ := prior task registered fresh ref contributes uncancelled
  have different : task.occurrence ≠ occurrence := fun same => fresh (same.symm ▸ consumed)
  refine ⟨{ node with tasks := node.tasks.filter (· != occurrence) },
    List.mem_map.mpr ⟨node, member, rfl⟩, identity, ?_⟩
  exact List.mem_filter.mpr
    ⟨
      linked,
      by
        have unequal : (task.occurrence == occurrence) = false := by
          cases same : task.occurrence == occurrence with
          | false => rfl
          | true => exact (different ((occurrence_beq_iff_eq _ _).mp same)).elim
        simp only [bne, unequal, Bool.not_false]
    ⟩

/-- A successful ref filter is safe when no fresh task has that uncancelled contributor. -/
theorem State.UncancelledTaskAccounting.filterGroupRef {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (closedRef : NodeRef)
    (noFresh
      : closedRef ∉ queue.cancelledGroups
        → ∀ task ∈ queue.tasks,
            task.occurrence ∉ settled
            → closedRef ∉ task.groups.map Execution.DeliveryNode.ref)
    : ({
            queue with
              groupNodes :=
                queue.groupNodes.filter (fun node => node.group.node.ref != closedRef)
              rootGroups := queue.rootGroups.filter (· != closedRef)
          }
        : State).UncancelledTaskAccounting
        settled := by
  intro task registered fresh ref contributes uncancelled
  obtain ⟨node, member, identity, linked⟩ := prior task registered fresh ref contributes uncancelled
  have different : node.group.node.ref ≠ closedRef := by
    intro same
    have closedUncancelled : closedRef ∉ queue.cancelledGroups :=
      same ▸ identity.symm ▸ uncancelled
    exact noFresh closedUncancelled task registered fresh (same ▸ identity.symm ▸ contributes)
  exact ⟨
    node,
    List.mem_filter.mpr ⟨member, by simpa only [bne_iff_ne] using different⟩,
    identity,
    linked
  ⟩

/-- Settled successful closure preserves every still-unsettled uncancelled owner.
Witness: each flushed task is consumed, the removed group has no fresh contributor,
and descendant pruning retains every nonempty owner membership.
-/
theorem State.UncancelledTaskAccounting.finishSettledGroupSuccess
    {queue : State} {settled : List Occurrence}
    (accounted : queue.UncancelledTaskAccounting settled)
    (unique : queue.GroupRefsUnique)
    (group : GroupNode) (groupMember : group ∈ queue.groupNodes)
    (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.UncancelledTaskAccounting settled := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs)
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
  have stepFacts (acc : State × List ExecutionGroupValue × NodeRefs)
      (occurrence : Occurrence) (already : occurrence ∈ settled)
      (currentAccounting : acc.1.UncancelledTaskAccounting settled)
      (currentUnique : acc.1.GroupRefsUnique)
      : (step acc occurrence).1.UncancelledTaskAccounting settled
        ∧ (step acc occurrence).1.GroupRefsUnique
        ∧ (step acc occurrence).1.tasks = acc.1.tasks
        ∧ (step acc occurrence).1.cancelledGroups = acc.1.cancelledGroups := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact ⟨currentAccounting, currentUnique, rfl, rfl⟩
    · exact ⟨currentAccounting.removeSettledTask occurrence already,
        currentUnique.removeTask occurrence, rfl, rfl⟩
  have foldFacts (more : List Occurrence)
      (all : ∀ occurrence ∈ more, occurrence ∈ settled) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.UncancelledTaskAccounting settled
        → acc.1.GroupRefsUnique
        → (more.foldl step acc).1.UncancelledTaskAccounting settled
          ∧ (more.foldl step acc).1.GroupRefsUnique
          ∧ (more.foldl step acc).1.tasks = acc.1.tasks
          ∧ (more.foldl step acc).1.cancelledGroups = acc.1.cancelledGroups := by
    induction more with
    | nil =>
        intro acc currentAccounting currentUnique
        exact ⟨currentAccounting, currentUnique, rfl, rfl⟩
    | cons occurrence rest ih =>
        intro acc currentAccounting currentUnique
        have head : occurrence ∈ settled := all occurrence (by simp)
        have tail : ∀ task ∈ rest, task ∈ settled := by
          intro task member
          exact all task (by simp [member])
        obtain ⟨nextAccounting, nextUnique, nextTasks, nextCancelled⟩ :=
          stepFacts acc occurrence head currentAccounting currentUnique
        obtain ⟨finalAccounting, finalUnique, finalTasks, finalCancelled⟩ :=
          ih tail (step acc occurrence) nextAccounting nextUnique
        exact ⟨finalAccounting, finalUnique,
          finalTasks.trans nextTasks, finalCancelled.trans nextCancelled⟩
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  obtain ⟨flushedAccounting, flushedUnique, flushedTasks, flushedCancelled⟩ :=
    foldFacts group.tasks all (queue, [], []) accounted unique
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have noFreshContributor : group.group.node.ref ∉ queue.cancelledGroups
      → ∀ task ∈ flushed.tasks,
      task.occurrence ∉ settled
      → group.group.node.ref ∉ task.groups.map Execution.DeliveryNode.ref := by
    intro healthy task taskMember fresh contributor
    have original : task ∈ queue.tasks := by
      rw [flushedTasks] at taskMember
      exact taskMember
    have linked : task.occurrence ∈ group.tasks :=
      (accounted.linkedAt unique original fresh contributor healthy) group groupMember
        List.mem_cons_self
    exact fresh (all task.occurrence linked)
  have currentAccounting : current.UncancelledTaskAccounting settled :=
    flushedAccounting.filterGroupRef group.group.node.ref (by
      intro uncancelled
      apply noFreshContributor
      rwa [← flushedCancelled])
  have currentUnique : current.GroupRefsUnique :=
    flushedUnique.filterGroupNodes _
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.UncancelledTaskAccounting settled
  exact currentAccounting.pruneEmptyGroups currentUnique children

/-- Starting a computation changes no group membership or cancellation marker. -/
theorem State.UncancelledTaskAccounting.startTask {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (occurrence : Occurrence)
    (available : List (Occurrence × Nat) := [])
    : (queue.startTask occurrence available).UncancelledTaskAccounting settled := by
  unfold State.startTask
  split
  · exact prior
  · split <;> exact prior

/-- Cached group startup preserves owners, marking immediate removals cancelled. -/
theorem State.UncancelledTaskAccounting.startGroup {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.UncancelledTaskAccounting settled := by
  have cached := prior.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · rename_i node _
    split
    · have fold (tasks : List Occurrence) (current : State)
          (accounted : current.UncancelledTaskAccounting settled)
          : (tasks.foldl (fun next task => next.startTask task available)
              current).UncancelledTaskAccounting settled := by
        induction tasks generalizing current with
        | nil => exact accounted
        | cons task rest ih => exact ih _ (accounted.startTask task available)
      exact fold node.tasks _ cached
    · exact cached.removeGroup node.group.node.ref

/-- Released group/source startup preserves cancellation-aware task accounting. -/
theorem State.UncancelledTaskAccounting.startNewWork {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.UncancelledTaskAccounting settled := by
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let (next, queued) := acc.1.startGroup ref available
    (next, acc.2 ++ queued)
  have fold (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (accounted : acc.1.UncancelledTaskAccounting settled)
      : (refs.foldl step acc).1.UncancelledTaskAccounting settled := by
    induction refs generalizing acc with
    | nil => exact accounted
    | cons ref rest ih => exact ih _ (accounted.startGroup ref available)
  have grouped := fold (released.newGroups.map Execution.DeliveryNode.ref)
    ({ queue with rootGroups := queue.rootGroups ++
      released.newGroups.map Execution.DeliveryNode.ref }, []) prior
  have streams (refs : NodeRefs) (current : State)
      (accounted : current.UncancelledTaskAccounting settled)
      : (refs.foldl State.startStream current).UncancelledTaskAccounting settled := by
    induction refs generalizing current with
    | nil => exact accounted
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact accounted
  exact streams (released.newStreams.map Execution.DeliveryNode.ref) _ grouped

/-- A task rejection preserves the ledger even before its notification is recorded as consumed.
Every removed owner has a cancellation marker; surviving dormant owners retain membership.
-/
theorem State.UncancelledTaskAccounting.taskFailure {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.UncancelledTaskAccounting settled := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using prior
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves (fun current => current.UncancelledTaskAccounting settled)
        (fun _ ref accounted => accounted.removeGroup ref) errors node.task.groups
        (queue.putTaskNode { node with rejection := some errors }, []) (prior.putTaskNode _)

/-- Successful ready draining preserves the same success-only settlement coordinate.
Witness: zero pending debt makes each flushed membership consumed; cached startup cancels
removed owners without waiting for FIFO rejection notification.
-/
theorem State.UncancelledTaskAccounting.drainReadyGroups {queue : State} {settled}
    (prior : queue.UncancelledTaskAccounting settled) (unique : queue.GroupRefsUnique)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.UncancelledTaskAccounting settled := by
  let invariant (current : State) := current.UncancelledTaskAccounting settled
    ∧ current.GroupRefsUnique ∧ current.PendingBound (fun _ => True) settled
  have result : invariant (queue.drainReadyGroups available).1 := by
    apply State.drainReadyGroups_preserves invariant (available := available)
      (valid := ⟨prior, unique, bounded⟩)
    intro current node frame member _ zero
    have all := frame.2.2.allSettled member trivial zero
    exact ⟨(frame.1.finishSettledGroupSuccess frame.2.1 node member all).startNewWork _ available,
      (frame.2.1.finishGroupSuccess node).startNewWork _ available,
      (frame.2.2.finishGroupSuccess node all).startNewWork _ available⟩
  exact result.1

/-- An uncancelled retired contributor belongs only to already consumed registered tasks. -/
theorem State.UncancelledTaskAccounting.retired_contributor_settled {queue : State}
    {settled} (prior : queue.UncancelledTaskAccounting settled) {task : Task}
    (registered : task ∈ queue.tasks) {ref : NodeRef}
    (contributes : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    (uncancelled : ref ∉ queue.cancelledGroups) (retired : queue.RetiredGroup ref)
    : task.occurrence ∈ settled := by
  apply Classical.byContradiction
  intro fresh
  obtain ⟨node, member, same, _⟩ := prior task registered fresh ref contributes uncancelled
  exact retired.2 (List.mem_map.mpr ⟨node, member, same⟩)

/-- A fresh failure cannot invalidate an uncancelled retired record with uncancelled ancestors.
Witness: a new invalidation names a direct contributor in that record's ancestry. Its
retirement and uncancelled marker force the registered task to be consumed already.
Unlike failure-indexed owner accounting, this uses the actual cancellation markers.
-/
theorem State.RetiredGroup.healthy_cons_fresh_of_uncancelledAccounting {queue : State}
    {work settled failed node dependencies}
    (retired : queue.RetiredGroup node.ref)
    (ancestors : queue.AncestorsRetired work node.ref)
    (uncancelled : node.ref ∉ queue.cancelledGroups)
    (ancestorMarkers
      : ∀ ancestor ∈ dependencies,
          ∀ occurrence owners,
            TaskHasOwners work occurrence owners
            → ancestor ∈ owners
            → ancestor ∉ queue.cancelledGroups)
    (generated : ExecutedWork work) (known : GroupRecordAt work node dependencies)
    (healthy : ¬GroupRecordInvalidated work failed node.ref)
    (accounted : queue.UncancelledTaskAccounting settled)
    {task : Task} (registered : task ∈ queue.tasks) (matching : TaskMatches work task)
    (fresh : task.occurrence ∉ settled)
    : ¬GroupRecordInvalidated work (task.occurrence :: failed) node.ref := by
  intro invalid
  obtain ⟨occurrence, owners, owner, descriptor, recorded, contributes, inChain⟩ :=
    (generated.groupRecordInvalidated_iff known).mp invalid
  rcases List.mem_cons.mp recorded with same | old
  · subst occurrence
    obtain ⟨producer, payload, structural⟩ := descriptor
    obtain ⟨⟨address, actualPayload, actualProducer, _, actual⟩, _⟩ := matching
    have contributor : owner ∈ task.groups.map Execution.DeliveryNode.ref :=
      (structural.unique actual).1 ▸ contributes
    have ownerRetired : queue.RetiredGroup owner := by
      rcases List.mem_cons.mp inChain with same | ancestor
      · exact same ▸ retired
      · exact ancestors node dependencies known rfl owner ancestor
          task.occurrence owners ⟨producer, payload, structural⟩ contributes
    have ownerUncancelled : owner ∉ queue.cancelledGroups := by
      rcases List.mem_cons.mp inChain with same | ancestor
      · exact same ▸ uncancelled
      · exact ancestorMarkers owner ancestor task.occurrence owners
          ⟨producer, payload, structural⟩ contributes
    exact fresh (accounted.retired_contributor_settled registered contributor ownerUncancelled
      ownerRetired)
  · exact healthy ((generated.groupRecordInvalidated_iff known).mpr
      ⟨occurrence, owners, owner, descriptor, old, contributes, inChain⟩)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
