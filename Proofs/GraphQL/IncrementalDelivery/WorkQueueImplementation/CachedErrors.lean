import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTasks

/-! Selected task-rejection facts through integration, release, and recursive draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Queue bookkeeping preserves arbitrary contributor-indexed rejection facts
-----------------------------------------------------------------------------------------

/-- Every retained task rejection certifies its selected cause for each contributor.
The predicate observes task computations and introduces no group-level failure cache.
-/
def State.CachedErrorsSatisfy (queue : State) (property : Nat → Nat → Prop) : Prop :=
  ∀ node ∈ queue.taskNodes,
    ∀ errors,
      node.rejection = some errors → ∀ group ∈ node.task.groups, property group.ref errors

/-- Pointwise implication weakens the facts certified by every retained task rejection.
Witness: apply the implication to each live node's exact count.
-/
theorem State.CachedErrorsSatisfy.mono {queue : State} {before after}
    (cached : queue.CachedErrorsSatisfy before)
    (weaken : ∀ ref errors, before ref errors → after ref errors)
    : queue.CachedErrorsSatisfy after :=
  fun node member errors same group included =>
    weaken _ _ (cached node member errors same group included)

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
theorem State.CachedErrorsSatisfy.putGroupNode {queue : State}
    {property : Nat → Nat → Prop} (supported : State.CachedErrorsSatisfy queue property)
    (updated : GroupNode)
    : (queue.putGroupNode updated).CachedErrorsSatisfy property :=
  supported

/-- Task metadata replacement preserves certified rejection causes. -/
theorem State.CachedErrorsSatisfy.putTaskNode {queue : State}
    {property : Nat → Nat → Prop} (supported : State.CachedErrorsSatisfy queue property)
    (updated : TaskNode)
    (replacement
      : ∀ errors,
          updated.rejection = some errors
          → ∀ group ∈ updated.task.groups, property group.ref errors)
    : (queue.putTaskNode updated).CachedErrorsSatisfy property := by
  intro node member errors cached
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact replacement errors cached
  · subst node; exact supported old oldMember errors cached

-----------------------------------------------------------------------------------------
-- Integration and activation do not introduce failure caches
-----------------------------------------------------------------------------------------

/-- Fresh group registration starts with no task rejection.
Witness: existing nodes retain their witnesses and the appended node has `none`.
-/
theorem State.CachedErrorsSatisfy.addGroup {queue : State} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property) (group : Group)
    : (queue.addGroup group).CachedErrorsSatisfy property := by
  unfold State.addGroup
  split
  · exact supported
  · split <;> exact supported

/-- Parent-link installation leaves every rejection and contributor refs unchanged.
Witness: the two actual folds register empty nodes and replace only child links.
-/
theorem State.CachedErrorsSatisfy.addGroups {queue : State} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property) (groups : List Group)
    : (queue.addGroups groups).1.CachedErrorsSatisfy property := by
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
      (valid : current.CachedErrorsSatisfy property)
      : (link current group).CachedErrorsSatisfy property := by
    unfold link
    split
    · exact valid
    · split
      · exact valid
      · rename_i node found
        exact valid.putGroupNode _
  change (fresh.foldl link (fresh.foldl State.addGroup queue)).CachedErrorsSatisfy
    property
  exact fold_preserves _ link fresh linked _
    (fold_preserves (fun current : State => current.CachedErrorsSatisfy property)
      State.addGroup fresh (fun _ group valid => valid.addGroup group)
      queue supported)

/-- Adding a task changes membership and counters, never the task's retained rejection.
Witness: induction through contributing groups and the unchanged rejection projection.
-/
theorem State.CachedErrorsSatisfy.addTask {queue : State} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property) (task : Task)
    : (queue.addTask task).CachedErrorsSatisfy property := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have stable (current : State) (group : Execution.DeliveryNode)
      (valid : current.CachedErrorsSatisfy property)
      : (step current group).CachedErrorsSatisfy property := by
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
  · intro node member errors cached
    rcases List.mem_append.mp member with old | new
    · exact folded node old errors cached
    · have same := List.mem_singleton.mp new
      subst node
      cases cached
  · exact folded

/-- Stream registration leaves task rejections untouched.
Witness: only stream and producer-task registries are updated.
-/
theorem State.CachedErrorsSatisfy.addStreams {queue : State} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property) (streams : List Stream)
    (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.CachedErrorsSatisfy property := by
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
theorem State.CachedErrorsSatisfy.maybeIntegrateWork {queue : State}
    {property : Nat → Nat → Prop} (supported : State.CachedErrorsSatisfy queue property)
    (more : Work) (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork more producer).1.CachedErrorsSatisfy property := by
  exact (fold_preserves (fun current : State => current.CachedErrorsSatisfy property)
    State.addTask more.tasks
    (fun _ task valid => valid.addTask task) _
    (supported.addGroups more.groups)).addStreams more.streams producer

/-- Pruning preserves caches on surviving groups.
Witness: each iteration retains or filters nodes, and creates no new cache.
-/
theorem State.CachedErrorsSatisfy.pruneEmptyGroups {queue : State}
    {property : Nat → Nat → Prop} (supported : State.CachedErrorsSatisfy queue property)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.CachedErrorsSatisfy property := by
  have loop (fuel : Nat) (current : State) (remaining kept)
      (valid : current.CachedErrorsSatisfy property)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.CachedErrorsSatisfy
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

/-- Activation starts host work without changing task rejections.
Witness: task, group, and stream start folds preserve the task-rejection facts.
-/
theorem State.CachedErrorsSatisfy.startNewWork {queue : State}
    {property : Nat → Nat → Prop} (supported : State.CachedErrorsSatisfy queue property)
    (more : NewWork)
    : (queue.startNewWork more).CachedErrorsSatisfy property := by
  have taskStable (current : State) (occurrence : Occurrence)
      (valid : current.CachedErrorsSatisfy property)
      : (current.startTask occurrence).CachedErrorsSatisfy property := by
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
  have groupStable (current : State) (ref : NodeRef)
      (valid : current.CachedErrorsSatisfy property)
      : (current.startGroup ref).CachedErrorsSatisfy property := by
    unfold State.startGroup
    split
    · exact valid
    · rename_i node found
      exact fold_preserves _ State.startTask node.tasks taskStable current valid
  have streamStable (current : State) (ref : NodeRef)
      (valid : current.CachedErrorsSatisfy property)
      : (current.startStream ref).CachedErrorsSatisfy property := by
    unfold State.startStream
    split <;> exact valid
  exact fold_preserves _ State.startStream _ streamStable _
    (fold_preserves _ State.startGroup _ groupStable _ supported)

/-- Queue creation contains no uncertified cached failure.
Witness: the empty state, immediate integration, pruning, and activation.
-/
theorem createWorkQueue_cachedErrors (input : Work) (property : Nat → Nat → Prop)
    : (State.initialize input).CachedErrorsSatisfy property := by
  have empty : ({} : State).CachedErrorsSatisfy property := by
    intro node member
    cases member
  exact ((empty.maybeIntegrateWork input).pruneEmptyGroups _).startNewWork _

-----------------------------------------------------------------------------------------
-- Publication, cleanup, and recursive release retain rejection-cause facts
-----------------------------------------------------------------------------------------

/-- Task retirement changes only memberships, retaining every rejection-cause witness.
Witness: the group map leaves each delivery ref and cached error unchanged.
-/
theorem State.CachedErrorsSatisfy.removeTask {queue : State} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (occurrence : Occurrence)
    : (queue.removeTask occurrence).CachedErrorsSatisfy property := by
  intro node member errors cached
  exact supported node (List.mem_filter.mp member).1 errors cached

/-- Group cancellation filters nodes without modifying retained rejections.
Witness: every surviving node and witness belonged to the original queue.
-/
theorem State.CachedErrorsSatisfy.removeGroup {queue : State}
    {property : Nat → Nat → Prop} (supported : State.CachedErrorsSatisfy queue property)
    (ref : NodeRef)
    : (queue.removeGroup ref).CachedErrorsSatisfy property := by
  intro node member
  exact supported node (List.mem_filter.mp member).1

/-- A successful flush retires tasks and prunes shells without creating failures.
Witness: the task fold preserves caches, and subsequent node filters retain error facts.
-/
theorem State.CachedErrorsSatisfy.finishGroupSuccess {queue : State}
    {property : Nat → Nat → Prop} (supported : State.CachedErrorsSatisfy queue property)
    (group : GroupNode)
    : (queue.finishGroupSuccess group).1.CachedErrorsSatisfy property := by
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
      (valid : acc.1.CachedErrorsSatisfy property)
      : (step acc occurrence).1.CachedErrorsSatisfy property := by
    obtain ⟨current, values, streams⟩ := acc
    dsimp only [step]
    split
    · exact valid
    · exact valid.removeTask occurrence
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have prior : flushed.CachedErrorsSatisfy property :=
    fold_preserves _ step group.tasks stable (queue, [], []) supported
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have filtered : current.CachedErrorsSatisfy property := by
    exact prior
  exact filtered.pruneEmptyGroups _

/-- Retaining a certified incoming rejection preserves all retained cause facts. -/
theorem State.CachedErrorsSatisfy.taskFailure {queue : State}
    {property : Nat → Nat → Prop} (supported : queue.CachedErrorsSatisfy property)
    (occurrence : Occurrence) (errors : Nat)
    (cause
      : ∀ node,
          queue.taskNode? occurrence = some node
          → ∀ group ∈ node.task.groups, property group.ref errors)
    : (queue.taskFailure occurrence errors).1.CachedErrorsSatisfy property := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using supported
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      apply failureGroupFold_preserves (fun state => state.CachedErrorsSatisfy property)
        (fun _ ref prior => prior.removeGroup ref)
      exact supported.putTaskNode _
        (by
          intro count same
          cases Option.some.inj same
          exact cause node found)

/-- Recursive release preserves rejection-cause facts through both kinds of closure.
Witness: the actual bounded drain alternates supported success flushes and failure removal.
-/
theorem State.CachedErrorsSatisfy.drainReadyGroups {queue : State}
    {property : Nat → Nat → Prop} (supported : State.CachedErrorsSatisfy queue property)
    : queue.drainReadyGroups.1.CachedErrorsSatisfy property := by
  apply State.drainReadyGroups_preserves
    (fun current => current.CachedErrorsSatisfy property) (valid := supported)
  · intro current node valid _ _ _ _
    exact (valid.finishGroupSuccess node).startNewWork _
  · intro current node occurrence errors valid _ _ selected
    obtain ⟨_, task, found, rejected⟩ := State.rejectedTask?_sound selected
    apply valid.taskFailure occurrence errors
    intro other otherFound
    have same := Option.some.inj (found.symm.trans otherFound)
    subst other
    exact valid task (List.mem_of_find?_eq_some found) errors rejected

/-- Successful settlement never introduces a new retained failure.
Witness: child integration, each contributor decrement/flush, activation, and full drain.
-/
theorem State.CachedErrorsSatisfy.taskSuccess {queue : State}
    {property : Nat → Nat → Prop} (supported : State.CachedErrorsSatisfy queue property)
    (occurrence : Occurrence) (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.CachedErrorsSatisfy property := by
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
      (valid : acc.1.CachedErrorsSatisfy property)
      : (step acc group).1.CachedErrorsSatisfy property := by
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
    have before : withValue.CachedErrorsSatisfy property :=
      supported.putTaskNode _ (supported taskNode (List.mem_of_find?_eq_some found))
    have integrated := before.maybeIntegrateWork result.work (some occurrence)
    have released := fold_preserves _ step taskNode.task.groups stable
      ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {}) integrated
    exact (released.startNewWork _).drainReadyGroups

/-- Stream-item integration and its final drain preserve cached-failure support.
Witness: each item integrates fresh work, prunes, and activates without inventing caches.
-/
theorem State.CachedErrorsSatisfy.streamItems {queue : State}
    {property : Nat → Nat → Prop} (supported : State.CachedErrorsSatisfy queue property)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : (queue.streamItems stream items).1.CachedErrorsSatisfy property := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    (pruned.startNewWork { more with newGroups := nonempty }, groups ++ nonempty,
      streams ++ more.newStreams, values ++ [item.value])
  have stable (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem)
      (valid : acc.1.CachedErrorsSatisfy property)
      : (step acc item).1.CachedErrorsSatisfy property :=
    ((valid.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
  dsimp only [State.streamItems]
  split
  · exact supported
  · exact (fold_preserves _ step items stable (queue, [], [], []) supported).drainReadyGroups

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
