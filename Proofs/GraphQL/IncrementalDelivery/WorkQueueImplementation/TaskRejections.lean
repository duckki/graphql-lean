import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTasks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskSettlements

/-! Occurrence-indexed rejection provenance through integration, release, and recursive draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Queue bookkeeping preserves arbitrary occurrence-indexed rejection facts
-----------------------------------------------------------------------------------------

private theorem taskNode_occurrence {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node)
    : node.task.occurrence = occurrence :=
  (occurrence_beq_iff_eq _ _).mp
    (List.find?_some
      (p :=
        fun candidate : TaskNode =>
          candidate.task.occurrence == occurrence)
      found)

/-- Every retained task rejection certifies a fact about its own computation identity.
This proof-only predicate adds no runtime metadata.
-/
def State.TaskRejectionsSatisfy (queue : State) (property : Occurrence → Nat → Prop)
    : Prop :=
  ∀ node ∈ queue.taskNodes,
    ∀ errors, node.rejection = some errors → property node.task.occurrence errors

/-- Pointwise implication weakens the facts certified by every retained task rejection.
Witness: apply the implication to each live node's exact count.
-/
theorem State.TaskRejectionsSatisfy.mono {queue : State} {before after}
    (rejectiond : queue.TaskRejectionsSatisfy before)
    (weaken : ∀ ref errors, before ref errors → after ref errors)
    : queue.TaskRejectionsSatisfy after :=
  fun node member errors same => weaken _ _ (rejectiond node member errors same)

/-- A pointwise invariant is preserved by folding individually preserving steps.
Witness: list induction threads the actual state, without queue-admission assumptions.
-/
private theorem fold_preserves {α β : Type} (property : β → Prop)
    (step : β → α → β) (items : List α)
    (preserved : ∀ state item, property state → property (step state item))
    (state : β) (valid : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact valid
  | cons item rest ih => exact ih _ (preserved state item valid)

/-- Group metadata updates leave retained task rejections unchanged. -/
theorem State.TaskRejectionsSatisfy.putGroupNode {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (updated : GroupNode)
    : (queue.putGroupNode updated).TaskRejectionsSatisfy property :=
  supported

/-- Task metadata replacement preserves certified rejection causes. -/
theorem State.TaskRejectionsSatisfy.putTaskNode {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (updated : TaskNode)
    (replacement
      : ∀ errors,
          updated.rejection = some errors → property updated.task.occurrence errors)
    : (queue.putTaskNode updated).TaskRejectionsSatisfy property := by
  intro node member errors rejectiond
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact replacement errors rejectiond
  · subst node; exact supported old oldMember errors rejectiond

-----------------------------------------------------------------------------------------
-- Integration and activation do not introduce failure rejections
-----------------------------------------------------------------------------------------

/-- Fresh group registration starts with no task rejection.
Witness: existing nodes retain their witnesses and the appended node has `none`.
-/
theorem State.TaskRejectionsSatisfy.addGroup {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (group : Group)
    : (queue.addGroup group).TaskRejectionsSatisfy property := by
  unfold State.addGroup
  split
  · exact supported
  · split <;> exact supported

/-- Parent-link installation leaves every rejection and contributor refs unchanged.
Witness: the two actual folds register empty nodes and replace only child links.
-/
theorem State.TaskRejectionsSatisfy.addGroups {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (groups : List Group)
    : (queue.addGroups groups).1.TaskRejectionsSatisfy property := by
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  let link (current : State) (group : Group) :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.ref then
              node.childGroups else node.childGroups ++ [group.node.ref]
            current.putGroupNode { node with childGroups := children }
  have linked (current : State) (group : Group)
      (valid : current.TaskRejectionsSatisfy property)
      : (link current group).TaskRejectionsSatisfy property := by
    unfold link
    split
    · exact valid
    · split
      · exact valid
      · rename_i node found
        exact valid.putGroupNode _
  change (fresh.foldl link (fresh.foldl State.addGroup queue)).TaskRejectionsSatisfy
    property
  exact fold_preserves _ link fresh linked _
    (fold_preserves (fun current : State => current.TaskRejectionsSatisfy property)
      State.addGroup fresh (fun _ group valid => valid.addGroup group)
      queue supported)

/-- Adding a task changes membership and counters, never the task's retained rejection.
Witness: induction through contributing groups and the unchanged rejection projection.
-/
theorem State.TaskRejectionsSatisfy.addTask {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (task : Task)
    : (queue.addTask task).TaskRejectionsSatisfy property := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stable (current : State) (group : Execution.DeliveryNode)
      (valid : current.TaskRejectionsSatisfy property)
      : (step current group).TaskRejectionsSatisfy property := by
    unfold step
    split
    · exact valid
    · rename_i node found
      split
      · exact valid
      · exact valid.putGroupNode _
  have folded := fold_preserves _ step task.groups stable registered supported
  dsimp only [State.addTask]
  split
  · intro node member errors rejectiond
    rcases List.mem_append.mp member with old | new
    · exact folded node old errors rejectiond
    · have same := List.mem_singleton.mp new
      subst node
      cases rejectiond
  · exact folded

/-- Stream registration leaves task rejections untouched.
Witness: only stream and producer-task registries are updated.
-/
theorem State.TaskRejectionsSatisfy.addStreams {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (streams : List Stream)
    (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.TaskRejectionsSatisfy property := by
  dsimp only [State.addStreams]
  split
  · exact supported
  · split
    · exact supported
    · rename_i node found
      exact supported.putTaskNode _ (supported node (List.mem_of_find?_eq_some found))

/-- Immediate work integration preserves rejection-cause facts.
Witness: group, task, and stream integration preserve it individually.
-/
theorem State.TaskRejectionsSatisfy.maybeIntegrateWork {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (more : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork more producer).1.TaskRejectionsSatisfy property := by
  exact (fold_preserves (fun current : State => current.TaskRejectionsSatisfy property)
    State.addTask more.tasks
    (fun _ task valid => valid.addTask task) _
    (supported.addGroups more.groups)).addStreams more.streams producer

/-- Pruning preserves rejections on surviving groups.
Witness: each iteration retains or filters nodes, and creates no new rejection.
-/
theorem State.TaskRejectionsSatisfy.pruneEmptyGroups {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.TaskRejectionsSatisfy property := by
  have loop (fuel : Nat) (current : State) (remaining kept)
      (valid : current.TaskRejectionsSatisfy property)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.TaskRejectionsSatisfy
          property := by
    induction fuel generalizing current remaining kept with
    | zero => exact valid
    | succ fuel ih =>
        cases remaining with
        | nil => exact valid
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ valid
            · split
              · exact ih _ _ _ valid
              · exact ih _ _ _ valid
  exact loop _ queue groups [] supported

/-- Starting a computation creates a node with no retained rejection. -/
theorem State.TaskRejectionsSatisfy.startTask {queue : State} {property}
    (valid : queue.TaskRejectionsSatisfy property) (occurrence : Occurrence)
    : (queue.startTask occurrence).TaskRejectionsSatisfy property := by
  unfold State.startTask
  split
  · exact valid
  · split
    · exact valid
    · intro node member errors rejected
      rcases List.mem_append.mp member with old | new
      · exact valid node old errors rejected
      · have same := List.mem_singleton.mp new
        subst node
        cases rejected

/-- Activation starts host work without changing task rejections.
Witness: task, group, and stream start folds preserve the task-rejection facts.
-/
theorem State.TaskRejectionsSatisfy.startNewWork {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (more : NewWork)
    : (queue.startNewWork more).TaskRejectionsSatisfy property := by
  have groupStable (current : State) (ref : NodeRef)
      (valid : current.TaskRejectionsSatisfy property)
      : (current.startGroup ref).TaskRejectionsSatisfy property := by
    unfold State.startGroup
    split
    · exact valid
    · rename_i node found
      exact fold_preserves (fun current : State => current.TaskRejectionsSatisfy property) State.startTask node.tasks (fun _ occurrence prior => prior.startTask occurrence) current valid
  have streamStable (current : State) (ref : NodeRef)
      (valid : current.TaskRejectionsSatisfy property)
      : (current.startStream ref).TaskRejectionsSatisfy property := by
    unfold State.startStream
    split <;> exact valid
  exact fold_preserves _ State.startStream _ streamStable _
    (fold_preserves _ State.startGroup _ groupStable _ supported)

/-- Queue creation contains no uncertified rejectiond failure.
Witness: the empty state, immediate integration, pruning, and activation.
-/
theorem createWorkQueue_taskRejections (input : Work) (property : Occurrence → Nat → Prop)
    : (State.initialize input).TaskRejectionsSatisfy property := by
  have empty : ({} : State).TaskRejectionsSatisfy property := by
    intro node member
    cases member
  exact ((empty.maybeIntegrateWork input).pruneEmptyGroups _).startNewWork _

-----------------------------------------------------------------------------------------
-- Publication, cleanup, and recursive release retain rejection-cause facts
-----------------------------------------------------------------------------------------

/-- Task retirement changes only memberships, retaining every rejection-cause witness.
Witness: the group map leaves each delivery ref and rejectiond error unchanged.
-/
theorem State.TaskRejectionsSatisfy.removeTask {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (occurrence : Occurrence)
    : (queue.removeTask occurrence).TaskRejectionsSatisfy property := by
  intro node member errors rejectiond
  exact supported node (List.mem_filter.mp member).1 errors rejectiond

/-- Group cancellation filters nodes without modifying retained rejections.
Witness: every surviving node and witness belonged to the original queue.
-/
theorem State.TaskRejectionsSatisfy.removeGroup {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (ref : NodeRef)
    : (queue.removeGroup ref).TaskRejectionsSatisfy property := by
  intro node member
  exact supported node (List.mem_filter.mp member).1

/-- A successful flush retires tasks and prunes shells without creating failures.
Witness: the task fold preserves rejections, and subsequent node filters retain error facts.
-/
theorem State.TaskRejectionsSatisfy.finishGroupSuccess {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.TaskRejectionsSatisfy property := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some node =>
        let values := match node.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ node.childStreams)
  have stable (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence)
      (valid : acc.1.TaskRejectionsSatisfy property)
      : (step acc occurrence).1.TaskRejectionsSatisfy property := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact valid
    · exact valid.removeTask occurrence
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have prior : flushed.TaskRejectionsSatisfy property :=
    fold_preserves _ step group.tasks stable (queue, [], []) supported
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have filtered : current.TaskRejectionsSatisfy property := by
    exact prior
  exact filtered.pruneEmptyGroups _

/-- Retaining a certified incoming rejection preserves all retained cause facts. -/
theorem State.TaskRejectionsSatisfy.taskFailure {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : queue.TaskRejectionsSatisfy property) (occurrence : Occurrence)
    (errors : Nat) (cause : property occurrence errors)
    : (queue.taskFailure occurrence errors).1.TaskRejectionsSatisfy property := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using supported
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      apply failureGroupFold_preserves (fun state => state.TaskRejectionsSatisfy property)
        (fun _ ref prior => prior.removeGroup ref)
      exact supported.putTaskNode _
        (by
          intro count same
          cases Option.some.inj same
          exact (taskNode_occurrence found).symm ▸ cause)

/-- Recursive release preserves rejection-cause facts through both kinds of closure.
Witness: the actual bounded drain alternates supported success flushes and failure removal.
-/
theorem State.TaskRejectionsSatisfy.drainReadyGroups {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property)
    : queue.drainReadyGroups.1.TaskRejectionsSatisfy property := by
  apply State.drainReadyGroups_preserves
    (fun current => current.TaskRejectionsSatisfy property) (valid := supported)
  · intro current node valid _ _ _ _
    exact (valid.finishGroupSuccess node).startNewWork _
  · intro current node occurrence errors valid _ _ selected
    obtain ⟨_, task, found, rejected⟩ := State.rejectedTask?_sound selected
    apply valid.taskFailure occurrence errors
    exact (taskNode_occurrence found) ▸
      valid task (List.mem_of_find?_eq_some found) errors rejected

/-- A prefix of successful owner settlement creates no rejection. -/
theorem State.TaskRejectionsSatisfy.successGroupFold {queue : State} {property}
    (supported : queue.TaskRejectionsSatisfy property)
    (groups : List Execution.DeliveryNode)
    : (groups.foldl successGroupStep (queue, [], {})).1.TaskRejectionsSatisfy
        property := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (prior : acc.1.TaskRejectionsSatisfy property)
      : (groups.foldl successGroupStep acc).1.TaskRejectionsSatisfy property := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        simp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ prior
        · rename_i node found
          have updated := prior.putGroupNode { node with pending := node.pending - 1 }
          split
          · exact ih _ (updated.finishGroupSuccess _)
          · exact ih _ updated
  exact loop groups (queue, [], {}) supported

/-- Successful settlement never introduces a new retained failure.
Witness: child integration, each contributor decrement/flush, activation, and full drain.
-/
theorem State.TaskRejectionsSatisfy.taskSuccess {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.TaskRejectionsSatisfy property := by
  let step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode) :=
    let (current, outputs, released) := acc
    match current.groupNode? group.ref with
    | none => (current, outputs, released)
    | some old =>
        let node := { old with pending := old.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.ref && node.pending == 0 then
          let (next, finished, more) := current.finishGroupSuccess node
          (next, outputs ++ finished,
            ⟨released.newGroups ++ more.newGroups, released.newStreams ++ more.newStreams⟩)
        else (current, outputs, released)
  have stable (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (valid : acc.1.TaskRejectionsSatisfy property)
      : (step acc group).1.TaskRejectionsSatisfy property := by
    obtain ⟨current, outputs, released⟩ := acc
    dsimp only [step]
    split
    · exact valid
    · rename_i node found
      have updated := valid.putGroupNode { node with pending := node.pending - 1 }
      split
      · exact updated.finishGroupSuccess _
      · exact updated
  unfold State.taskSuccess
  split
  · exact supported
  · rename_i taskNode found
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have before : withValue.TaskRejectionsSatisfy property :=
      supported.putTaskNode _ (supported taskNode (List.mem_of_find?_eq_some found))
    have integrated := before.maybeIntegrateWork result.work (some occurrence)
    have released := fold_preserves _ step taskNode.task.groups stable
      ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {}) integrated
    exact (released.startNewWork _).drainReadyGroups

/-- Stream-item integration and its final drain preserve rejectiond-failure support.
Witness: each item integrates fresh work, prunes, and activates without inventing rejections.
-/
theorem State.TaskRejectionsSatisfy.streamItems {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : (queue.streamItems stream items).1.TaskRejectionsSatisfy property := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    (pruned.startNewWork { more with newGroups := nonempty }, groups ++ nonempty,
      streams ++ more.newStreams, values ++ [item.value])
  have stable (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem)
      (valid : acc.1.TaskRejectionsSatisfy property)
      : (step acc item).1.TaskRejectionsSatisfy property :=
    ((valid.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
  dsimp only [State.streamItems]
  split
  · exact supported
  · exact (fold_preserves _ step items stable (queue, [], [], []) supported).drainReadyGroups

/-- Replaying inputs attributes every retained rejection to a supplied task failure. -/
theorem State.TaskRejectionsSatisfy.replayGraphEvents {queue : State}
    {settled : List Occurrence}
    (supported : queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (events : List GraphEvent)
    : (queue.replayGraphEvents events).TaskRejectionsSatisfy
        (fun occurrence _ =>
          occurrence ∈ settled ++ events.flatMap GraphEvent.groupFailures) := by
  induction events generalizing queue settled with
  | nil => simpa [State.replayGraphEvents] using supported
  | cons event rest ih =>
      have prior := supported.mono (fun _ _ member =>
        List.mem_append_left event.groupFailures member)
      have next : (queue.handleGraphEvent event).1.TaskRejectionsSatisfy
          (fun occurrence _ => occurrence ∈ settled ++ event.groupFailures) := by
        cases event with
        | taskSuccess occurrence result => exact prior.taskSuccess occurrence result
        | taskFailure occurrence errors =>
            exact prior.taskFailure occurrence errors
              (List.mem_append_right _ List.mem_cons_self)
        | streamItems stream items => exact prior.streamItems stream items
        | streamSuccess stream =>
            change (queue.streamSuccess stream).1.TaskRejectionsSatisfy _
            unfold State.streamSuccess
            split <;> exact prior
        | streamFailure stream errors =>
            change (queue.streamFailure stream errors).1.TaskRejectionsSatisfy _
            unfold State.streamFailure
            split <;> exact prior
      simpa only [State.replayGraphEvents, List.foldl_cons, List.flatMap_cons,
        List.append_assoc]
        using ih next

/-- Initial replay retains rejections only for received task settlements. -/
theorem createWorkQueue_replay_taskRejections (work : Execution.Work)
    (events : List GraphEvent)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).TaskRejectionsSatisfy
        (fun occurrence _ => occurrence ∈ GraphEvent.taskSettlements events) := by
  have prior := (createWorkQueue_taskRejections (Work.fromExecution work)
    (fun occurrence _ => occurrence ∈ ([] : List Occurrence))).replayGraphEvents events
  exact prior.mono
    (fun occurrence _ member =>
      GraphEvent.mem_taskSettlements.mpr
        (Or.inr
          (by
            simpa only [GraphEvent.failureSettlements, List.mem_reverse, List.nil_append]
              using member)))

/-- Excluding a computation from rejection provenance clears its cleanup rejection test. -/
theorem State.TaskRejectionsSatisfy.unrejected_lookup {queue : State} {occurrence}
    (prior : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ occurrence))
    : (queue.taskNode? occurrence).any (fun node => node.rejection.isSome) = false := by
  cases found : queue.taskNode? occurrence with
  | none => rfl
  | some node =>
      cases failed : node.rejection with
      | none => simp only [Option.any_some, failed, Option.isSome_none]
      | some errors =>
          exact False.elim (prior node (List.mem_of_find?_eq_some found) errors failed
            (taskNode_occurrence found))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
