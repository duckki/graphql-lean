import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication

/-! Cancellation history across integration, activation, and successful retirement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A pointwise state invariant extends through a finite fold.
Witness: list induction threads the actual intermediate state. -/
private theorem fold_preserves {α β : Type} (property : β → Prop) (step : β → α → β)
    (preserved : ∀ current item, property current → property (step current item))
    (items : List α) (current : β) (prior : property current)
    : property (items.foldl step current) := by
  induction items generalizing current with
  | nil => exact prior
  | cons item rest ih => exact ih _ (preserved current item prior)

-----------------------------------------------------------------------------------------
-- Only group registration can add cancellation refs during work integration
-----------------------------------------------------------------------------------------

/-- Task registration leaves cancellation history unchanged.
Witness: membership installation and optional activation update only group/task nodes. -/
theorem State.addTask_cancelledGroups (queue : State) (task : Task)
    : (queue.addTask task).cancelledGroups = queue.cancelledGroups := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved (current : State) (group : Execution.DeliveryNode)
      (prior : current.cancelledGroups = queue.cancelledGroups)
      : (step current group).cancelledGroups = queue.cancelledGroups := by
    unfold step
    split
    · exact prior
    · split <;> exact prior
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let current := task.groups.foldl step registered
  have same : current.cancelledGroups = queue.cancelledGroups :=
    fold_preserves (fun current : State => current.cancelledGroups = queue.cancelledGroups)
      step preserved task.groups registered rfl
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).cancelledGroups = queue.cancelledGroups
  split <;> exact same

/-- Stream integration does not alter group cancellation history.
Witness: both root and producer-linked registration update only streams and task nodes. -/
theorem State.addStreams_cancelledGroups (queue : State) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.cancelledGroups
      = queue.cancelledGroups := by
  unfold State.addStreams
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- Work integration changes cancellation refs exactly as its group-registration stage.
Witness: task folds and stream registration preserve that stage's resulting history. -/
theorem State.maybeIntegrateWork_cancelledGroups (queue : State) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.cancelledGroups
      = (queue.addGroups work.groups).1.cancelledGroups := by
  let grouped := (queue.addGroups work.groups).1
  have preserved (current : State) (task : Task)
      (prior : current.cancelledGroups = grouped.cancelledGroups)
      : (current.addTask task).cancelledGroups = grouped.cancelledGroups := by
    rw [State.addTask_cancelledGroups, prior]
  have folded := fold_preserves
    (fun current : State => current.cancelledGroups = grouped.cancelledGroups)
    State.addTask preserved work.tasks grouped rfl
  let tasked := work.tasks.foldl State.addTask grouped
  change (tasked.addStreams work.streams parentTask).1.cancelledGroups = grouped.cancelledGroups
  rw [State.addStreams_cancelledGroups]
  exact folded

/-- More failed occurrences retain every existing cancellation witness.
Witness: monotonicity of the independent invalidation relation. -/
theorem State.CancelledGroupsSupported.weaken {queue work before after}
    (supported : State.CancelledGroupsSupported queue work before)
    (included : before.Subset after)
    : queue.CancelledGroupsSupported work after := by
  intro ref member
  exact (supported ref member).mono included

/-- Integrating a matched work chunk preserves causal cancellation provenance.
Witness: group registration propagates invalidation; later stages do not alter its refs.
-/
theorem State.CancelledGroupsSupported.maybeIntegrateWork {queue work failed}
    (supported : State.CancelledGroupsSupported queue work failed) (newWork : Work)
    (parentTask : Option Occurrence)
    (matching
      : ∀ group ∈ newWork.groups,
          ∃ dependencies producer,
            NodeAt work group.node .group dependencies producer
            ∧ group.parent = dependencies.head?)
    : (queue.maybeIntegrateWork newWork parentTask).1.CancelledGroupsSupported work
        failed := by
  intro ref member
  rw [State.maybeIntegrateWork_cancelledGroups queue newWork parentTask] at member
  exact supported.addGroups newWork.groups matching ref member

-----------------------------------------------------------------------------------------
-- Successful retirement preserves history; startup may append cancellation markers
-----------------------------------------------------------------------------------------

/-- Empty-shell pruning preserves cancellation history exactly.
Witness: its recursive traversal filters live nodes but never records failure refs. -/
theorem State.pruneEmptyGroups_cancelledGroups (queue : State)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.cancelledGroups = queue.cancelledGroups := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.cancelledGroups
        = current.cancelledGroups := by
    induction fuel generalizing current remaining kept with
    | zero => rfl
    | succ fuel ih =>
        cases remaining with
        | nil => rfl
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _
            · split <;> exact ih _ _ _
  exact loop _ queue groups []

/-- Exposing task caches leaves the cancellation history unchanged. -/
theorem State.cacheTaskFailures_cancelledGroups (queue : State)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).cancelledGroups = queue.cancelledGroups := by
  have frame := congrArg State.cancelledGroups (queue.cacheTaskFailures_frame available)
  exact frame

/-- Startup retains all prior cancellation markers, even when cached failure adds more. -/
theorem State.startGroup_cancelledGroups_prefix (queue : State) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    : queue.cancelledGroups.IsPrefix
        (queue.startGroup ref available).1.cancelledGroups := by
  have tasks (more : List Occurrence) (current : State)
      : (more.foldl (fun current task => current.startTask task available)
          current).cancelledGroups = current.cancelledGroups := by
    induction more generalizing current with
    | nil => rfl
    | cons task rest ih =>
        simp only [List.foldl_cons, ih]
        unfold State.startTask
        split
        · rfl
        · split <;> rfl
  unfold State.startGroup
  dsimp only
  split
  · rw [State.cacheTaskFailures_cancelledGroups]
    exact List.prefix_refl _
  · split
    · rw [tasks, State.cacheTaskFailures_cancelledGroups]
      exact List.prefix_refl _
    · simp only [State.finishGroupFailure, State.removeGroup,
        State.cacheTaskFailures_cancelledGroups]
      exact List.prefix_append _ _

/-- Released-work activation preserves the order of every existing cancellation marker. -/
theorem State.startNewWork_cancelledGroups_prefix (queue : State) (work : NewWork)
    (available : List (Occurrence × Nat) := [])
    : queue.cancelledGroups.IsPrefix
        (queue.startNewWork work available).1.cancelledGroups := by
  have streams (refs : NodeRefs) (current : State)
      : (refs.foldl State.startStream current).cancelledGroups = current.cancelledGroups := by
    induction refs generalizing current with
    | nil => rfl
    | cons ref rest ih =>
        simp only [List.foldl_cons, ih]
        unfold State.startStream
        split <;> rfl
  have groups (refs : NodeRefs) (current : State) (failures : List GroupFailureEvent)
      : current.cancelledGroups.IsPrefix (refs.foldl
          (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref available
            (next, failures ++ queued)) (current, failures)).1.cancelledGroups := by
    induction refs generalizing current failures with
    | nil => exact List.prefix_refl _
    | cons ref rest ih =>
        simp only [List.foldl_cons]
        exact (current.startGroup_cancelledGroups_prefix ref available).trans (ih _ _)
  unfold State.startNewWork
  simp only [streams]
  exact groups (work.newGroups.map Execution.DeliveryNode.ref)
    {
      queue with
        rootGroups := queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.ref
    } []

/-- Startup never removes a previously recorded cancellation. -/
theorem State.startNewWork_cancelledGroups_subset (queue : State) (work : NewWork)
    (available : List (Occurrence × Nat) := [])
    : queue.cancelledGroups.Subset
        (queue.startNewWork work available).1.cancelledGroups :=
  (queue.startNewWork_cancelledGroups_prefix work available).subset

private theorem startTask_unrejected (queue : State) (task : Occurrence)
    (unrejected : ∀ node ∈ queue.taskNodes, node.rejection = none)
    : (queue.startTask task).cancelledGroups = queue.cancelledGroups
      ∧ ∀ node ∈ (queue.startTask task).taskNodes, node.rejection = none := by
  unfold State.startTask
  split
  · exact ⟨rfl, unrejected⟩
  · split
    · exact ⟨rfl, unrejected⟩
    · refine ⟨rfl, ?_⟩
      intro node member
      rcases List.mem_append.mp member with old | added
      · exact unrejected node old
      · cases List.mem_singleton.mp added
        rfl

/-- Without an available or retained rejection, activation records no cancellation. -/
theorem State.startNewWork_cancelledGroups_of_no_cached_failures (queue : State)
    (work : NewWork) (unrejected : ∀ node ∈ queue.taskNodes, node.rejection = none)
    : (queue.startNewWork work).1.cancelledGroups = queue.cancelledGroups := by
  have startGroup (current : State) (ref : NodeRef)
      (clean : ∀ node ∈ current.taskNodes, node.rejection = none)
      : (current.startGroup ref).1.cancelledGroups = current.cancelledGroups
        ∧ ∀ node ∈ (current.startGroup ref).1.taskNodes, node.rejection = none := by
    have tasks (more : List Occurrence) (current : State)
        (clean : ∀ node ∈ current.taskNodes, node.rejection = none)
        : (more.foldl (fun current task => current.startTask task) current).cancelledGroups
            = current.cancelledGroups
          ∧ ∀ node ∈ (more.foldl (fun current task => current.startTask task) current).taskNodes,
              node.rejection = none := by
      induction more generalizing current with
      | nil => exact ⟨rfl, clean⟩
      | cons task rest ih =>
          have next := startTask_unrejected current task clean
          have later := ih _ next.2
          exact ⟨later.1.trans next.1, later.2⟩
    cases found : current.groupNode? ref with
    | none =>
        simpa only [State.startGroup, State.cacheTaskFailures, List.foldl_nil, found]
          using And.intro (Eq.refl current.cancelledGroups) clean
    | some group =>
        have errors : group.tasks.filterMap
            (fun task => (current.taskNode? task).bind (·.rejection)) = [] := by
          apply List.filterMap_eq_nil_iff.mpr
          intro task member
          cases known : current.taskNode? task with
          | none => rfl
          | some node =>
              simp only [Option.bind_some]
              exact clean node (List.mem_of_find?_eq_some known)
        simpa only [State.startGroup, State.cacheTaskFailures, List.foldl_nil, found,
          errors, List.isEmpty_nil, ite_true]
          using tasks group.tasks current clean
  have groups (refs : NodeRefs) (current : State) (failures : List GroupFailureEvent)
      (clean : ∀ node ∈ current.taskNodes, node.rejection = none)
      : (refs.foldl
          (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref
            (next, failures ++ queued)) (current, failures)).1.cancelledGroups
          = current.cancelledGroups := by
    induction refs generalizing current failures with
    | nil => rfl
    | cons ref rest ih =>
        simp only [List.foldl_cons]
        have next := startGroup current ref clean
        exact (ih _ _ next.2).trans next.1
  have streams (refs : NodeRefs) (current : State)
      : (refs.foldl State.startStream current).cancelledGroups = current.cancelledGroups := by
    induction refs generalizing current with
    | nil => rfl
    | cons ref rest ih =>
        simp only [List.foldl_cons, ih]
        unfold State.startStream
        split <;> rfl
  unfold State.startNewWork
  simp only [streams]
  exact groups _ _ [] unrejected

/-- Successful group closure preserves every earlier cancellation ref and adds none.
Witness: flushing task memberships, removing the successful shell, and child pruning
each leave cancellation history unchanged. -/
theorem State.finishGroupSuccess_cancelledGroups (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.cancelledGroups = queue.cancelledGroups := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (task : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? task with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask task, values, streams ++ taskNode.childStreams)
  have preserved (acc : State × List ExecutionGroupValue × NodeRefs) (task : Occurrence)
      (prior : acc.1.cancelledGroups = queue.cancelledGroups)
      : (step acc task).1.cancelledGroups = queue.cancelledGroups := by
    unfold step
    dsimp only
    split <;> exact prior
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have same : flushed.cancelledGroups = queue.cancelledGroups :=
    fold_preserves (fun acc : State × List ExecutionGroupValue × NodeRefs =>
      acc.1.cancelledGroups = queue.cancelledGroups)
      step preserved group.tasks (queue, [], []) rfl
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.cancelledGroups = queue.cancelledGroups
  exact (current.pruneEmptyGroups_cancelledGroups children).trans same

-----------------------------------------------------------------------------------------
-- Queue initialization supplies the base case without source assumptions
-----------------------------------------------------------------------------------------

private theorem integration_unrejected (queue : State) (work : Work)
    (unrejected : ∀ node ∈ queue.taskNodes, node.rejection = none)
    : ∀ node ∈ (queue.maybeIntegrateWork work).1.taskNodes, node.rejection = none := by
  have groupNodes (current : State) (group : Group)
      : (current.addGroup group).taskNodes = current.taskNodes := by
    unfold State.addGroup
    split
    · rfl
    · split
      · rfl
      · split
        · split <;> rfl
        · rfl
  have grouped : (queue.addGroups work.groups).1.taskNodes = queue.taskNodes :=
    State.addGroups_projection State.taskNodes groupNodes queue work.groups
  have projected {α : Type} (step : State → α → State)
      (same : ∀ current item, (step current item).taskNodes = current.taskNodes)
      (items : List α) (current : State)
      : (items.foldl step current).taskNodes = current.taskNodes := by
    induction items generalizing current with
    | nil => rfl
    | cons item rest ih => exact (ih _).trans (same current item)
  have addTask (current : State) (task : Task)
      (clean : ∀ node ∈ current.taskNodes, node.rejection = none)
      : ∀ node ∈ (current.addTask task).taskNodes, node.rejection = none := by
    let step (current : State) (group : Execution.DeliveryNode) :=
      match current.groupNode? group.ref with
      | none => current
      | some node => if node.tasks.contains task.occurrence then current
          else current.putGroupNode
            { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
    have same (current : State) (group : Execution.DeliveryNode)
        : (step current group).taskNodes = current.taskNodes := by
      dsimp only [step]
      split
      · rfl
      · split <;> rfl
    have core := projected step same task.groups { current with tasks := current.tasks ++ [task] }
    intro node member
    unfold State.addTask at member
    dsimp only at member
    split at member
    ·
      rcases List.mem_append.mp member with old | added
      · exact clean node (core ▸ old)
      · cases List.mem_singleton.mp added
        rfl
    · exact clean node (core ▸ member)
  have cleanGroups : ∀ node ∈ (queue.addGroups work.groups).1.taskNodes, node.rejection = none := by
    simpa only [grouped] using unrejected
  exact fold_preserves
    (fun current : State => ∀ node ∈ current.taskNodes, node.rejection = none)
    State.addTask addTask work.tasks (queue.addGroups work.groups).1 cleanGroups

/-- No initial work chunk starts with a group marked cancelled.
Witness: empty-history registration followed only by pruning and activation. -/
theorem createWorkQueue_cancelledGroups_empty (work : Work)
    : (State.initialize work).cancelledGroups = [] := by
  let integrated := ({} : State).maybeIntegrateWork work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have clean : ∀ node ∈ pruned.1.taskNodes, node.rejection = none := by
    simpa only [pruned, integrated, State.pruneEmptyGroups_taskNodes]
      using integration_unrejected ({} : State) work (by simp)
  change (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 }).1.cancelledGroups = []
  rw [State.startNewWork_cancelledGroups_of_no_cached_failures _ _ clean,
    State.pruneEmptyGroups_cancelledGroups, State.maybeIntegrateWork_cancelledGroups,
    State.addGroups_cancelledGroups_empty rfl]

/-- Initial cancellation provenance is unconditional, even for raw work chunks.
Witness: the cancellation history is empty; no host-source or output premise is used. -/
theorem createWorkQueue_cancelledGroupsSupported (initialWork : Work)
    (work : Execution.Work) (failed : List Occurrence)
    : (State.initialize initialWork).CancelledGroupsSupported work failed := by
  intro ref member
  rw [createWorkQueue_cancelledGroups_empty] at member
  cases member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
