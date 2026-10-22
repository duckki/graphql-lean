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
  · split
    · exact supported
    · split
      · split <;> exact supported
      · exact supported

/-- Recursive group registration preserves task-local rejection facts. -/
theorem State.TaskRejectionsSatisfy.addGroups {queue : State} {property}
    (supported : State.TaskRejectionsSatisfy queue property) (groups : List Group)
    : (queue.addGroups groups).1.TaskRejectionsSatisfy property := by
  exact State.addGroups_preserves (fun current => current.TaskRejectionsSatisfy property) groups
    (fun _ group _ valid => valid.addGroup group) queue supported

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

/-- Cache exposure records the licensed rejection at its own computation occurrence. -/
theorem State.TaskRejectionsSatisfy.cacheTaskFailures {queue : State} {property}
    (valid : queue.TaskRejectionsSatisfy property) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors)
    : (queue.cacheTaskFailures available).TaskRejectionsSatisfy property := by
  induction available generalizing queue with
  | nil => exact valid
  | cons entry rest ih =>
      have tailLicensed : ∀ occurrence errors,
          (occurrence, errors) ∈ rest → property occurrence errors :=
        fun occurrence errors member => licensed _ _ (List.mem_cons_of_mem _ member)
      simp only [State.cacheTaskFailures, List.foldl_cons]
      split
      · exact ih valid tailLicensed
      · rename_i node found
        have updated := valid.putTaskNode { node with rejection := some entry.2 } (by
          intro errors rejected
          cases Option.some.inj rejected
          exact licensed _ _ (taskNode_occurrence found ▸ List.mem_cons_self))
        exact ih updated tailLicensed

/-- A fresh computation exposes only its supplied available rejection, if any. -/
theorem State.TaskRejectionsSatisfy.startTask {queue : State} {property}
    (valid : queue.TaskRejectionsSatisfy property) (occurrence : Occurrence)
    (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors := by
        intro occurrence errors member; cases member)
    : (queue.startTask occurrence available).TaskRejectionsSatisfy property := by
  unfold State.startTask
  split
  · exact valid
  · split
    · exact valid
    · rename_i task found
      intro node member errors rejected
      rcases List.mem_append.mp member with old | new
      · exact valid node old errors rejected
      · cases List.mem_singleton.mp new
        obtain ⟨⟨other, count⟩, inAvailable, selected⟩ :=
          List.exists_of_findSome?_eq_some rejected
        change (if other == occurrence then some count else none) = some errors at selected
        split at selected
        · rename_i equal
          have same : other = occurrence := (occurrence_beq_iff_eq _ _).mp equal
          have taskSame : task.occurrence = occurrence :=
            (occurrence_beq_iff_eq _ _).mp (List.find?_some
              (p := fun candidate : Task => candidate.occurrence == occurrence) found)
          cases Option.some.inj selected
          exact licensed _ _ (taskSame.symm ▸ same ▸ inAvailable)
        · cases selected

/-- Startup retains exact task-local rejection provenance while removing failed groups. -/
theorem State.TaskRejectionsSatisfy.startGroup {queue : State} {property}
    (valid : queue.TaskRejectionsSatisfy property) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors := by
        intro occurrence errors member; cases member)
    : (queue.startGroup ref available).1.TaskRejectionsSatisfy property := by
  have cached := valid.cacheTaskFailures available licensed
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · exact fold_preserves (fun current : State => current.TaskRejectionsSatisfy property)
        (fun current occurrence => current.startTask occurrence available) _
        (fun _ task prior => prior.startTask task available licensed) _ cached
    · exact fun node member => cached node (List.mem_filter.mp member).1

/-- Activation threads licensed availability through group startup and stream starts. -/
theorem State.TaskRejectionsSatisfy.startNewWork {queue : State} {property}
    (supported : queue.TaskRejectionsSatisfy property) (more : NewWork)
    (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors := by
        intro occurrence errors member; cases member)
    : (queue.startNewWork more available).1.TaskRejectionsSatisfy property := by
  have groups (refs : NodeRefs)
      (acc : State × List GroupFailureEvent) (valid : acc.1.TaskRejectionsSatisfy property)
      : (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.TaskRejectionsSatisfy property := by
    induction refs generalizing acc with
    | nil => exact valid
    | cons ref rest ih => exact ih _ (valid.startGroup ref available licensed)
  have streams (refs : NodeRefs) (current : State) (valid : current.TaskRejectionsSatisfy property)
      : (refs.foldl State.startStream current).TaskRejectionsSatisfy property := by
    induction refs generalizing current with
    | nil => exact valid
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact valid
  unfold State.startNewWork
  exact streams _ _ (groups _ _ supported)

/-- Queue creation contains no uncertified task rejection.
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
theorem State.TaskRejectionsSatisfy.drainReadyGroups {queue : State} {property}
    (supported : queue.TaskRejectionsSatisfy property)
    (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors := by
        intro occurrence errors member; cases member)
    : (queue.drainReadyGroups available).1.TaskRejectionsSatisfy property := by
  apply State.drainReadyGroups_preserves (fun current => current.TaskRejectionsSatisfy property)
    (available := available) (valid := supported)
  exact fun _ node prior _ _ _ =>
    (prior.finishGroupSuccess node).startNewWork _ available licensed

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
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors := by
        intro occurrence errors member; cases member)
    : (queue.taskSuccess occurrence result available).1.TaskRejectionsSatisfy
        property := by
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
    exact (released.startNewWork _ available licensed).drainReadyGroups available licensed

/-- Stream-item integration and its final drain preserve exact task-rejection support.
Witness: each item integrates fresh work, prunes, and activates without inventing rejections.
-/
theorem State.TaskRejectionsSatisfy.streamItems {queue : State}
    {property : Occurrence → Nat → Prop}
    (supported : State.TaskRejectionsSatisfy queue property)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors := by
        intro occurrence errors member; cases member)
    : (queue.streamItems stream items available).1.TaskRejectionsSatisfy property := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue × List GroupFailureEvent) (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    let (started, queued) := pruned.startNewWork { more with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ more.newStreams,
      values ++ [item.value], failures ++ queued)
  have stable (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue × List GroupFailureEvent) (item : StreamItem)
      (valid : acc.1.TaskRejectionsSatisfy property)
      : (step acc item).1.TaskRejectionsSatisfy property :=
    ((valid.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available licensed
  dsimp only [State.streamItems]
  split
  · exact supported
  · exact (fold_preserves _ step items stable
      (queue, [], [], [], []) supported).drainReadyGroups available licensed

/-- A host outcome preserves exact task rejection facts under a licensed snapshot. -/
theorem State.TaskRejectionsSatisfy.handleGraphEvent {queue : State} {property}
    (supported : queue.TaskRejectionsSatisfy property) (event : GraphEvent)
    (incoming
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → property occurrence errors)
    (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors := by
        intro occurrence errors member; cases member)
    : (queue.handleGraphEvent event available).1.TaskRejectionsSatisfy property := by
  have cached := supported.cacheTaskFailures available licensed
  cases event with
  | taskSuccess occurrence result =>
      exact cached.taskSuccess occurrence result available licensed
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.TaskRejectionsSatisfy property
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached
  | taskFailure occurrence errors =>
      exact cached.taskFailure occurrence errors (incoming _ _ rfl)
  | streamItems stream items => exact cached.streamItems stream items available licensed
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact cached
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact cached

/-- Actual batches expose only rejections supplied by their own task-failure inputs. -/
theorem State.TaskRejectionsSatisfy.handleGraphEvents {queue : State} {property}
    (supported : queue.TaskRejectionsSatisfy property) (events : List GraphEvent)
    (incoming
      : ∀ occurrence errors,
          GraphEvent.taskFailure occurrence errors ∈ events → property occurrence errors)
    : (queue.handleGraphEvents events).1.TaskRejectionsSatisfy property := by
  let available := GraphEvent.availableFailures events
  have licensed : ∀ occurrence errors,
      (occurrence, errors) ∈ available → property occurrence errors := by
    intro occurrence errors member
    obtain ⟨event, inEvents, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact incoming _ _ inEvents
  have loop (more : List GraphEvent) (included : more.Subset events) (current : State)
      (prior : current.TaskRejectionsSatisfy property)
      : (current.replayGraphEvents more available).TaskRejectionsSatisfy property := by
    induction more generalizing current with
    | nil => exact prior
    | cons event rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
        exact prior.handleGraphEvent event
          (fun occurrence errors same => incoming _ _ (same ▸ included List.mem_cons_self))
          available licensed
  cases running : queue.terminated with
  | true => simpa only [State.handleGraphEvents, running, ↓reduceIte] using supported
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      rw [same]
      exact loop events (List.Subset.refl _) queue supported

/-- Normalized replay preserves exact rejection provenance through actual host batches. -/
theorem State.TaskRejectionsSatisfy.runNormalized {queue : State} {property}
    (supported : queue.TaskRejectionsSatisfy property) (batches : List (List GraphEvent))
    (incoming
      : ∀ occurrence errors,
          GraphEvent.taskFailure occurrence errors ∈ batches.flatten
          → property occurrence errors)
    : (queue.runNormalized batches).1.TaskRejectionsSatisfy property := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue with
  | nil => exact supported
  | cons batch rest ih =>
      apply ih
        (supported.handleGraphEvents batch
          (by
            intro occurrence errors member
            exact incoming _ _ (List.mem_append_left rest.flatten member)))
      intro occurrence errors member
      exact incoming _ _ (List.mem_append_right batch member)

/-- Every actual retained computation rejection has its exact supplied task-failure input. -/
theorem createWorkQueue_runNormalized_taskRejections (input : Work)
    (batches : List (List GraphEvent))
    : ((State.initialize input).runNormalized batches).1.TaskRejectionsSatisfy
        (fun occurrence errors =>
          GraphEvent.taskFailure occurrence errors ∈ batches.flatten) :=
  (createWorkQueue_taskRejections input _).runNormalized batches
    (fun _ _ member => member)

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
      have next : (queue.dispatchGraphEvent event).1.TaskRejectionsSatisfy
          (fun occurrence _ => occurrence ∈ settled ++ event.groupFailures) := by
        cases event with
        | taskSuccess occurrence result => exact prior.taskSuccess occurrence result
        | groupFailure failure =>
            simp only [State.dispatchGraphEvent, State.handleGraphEvent,
              State.cacheTaskFailures, List.foldl_nil]
            unfold State.groupFailure
            split
            · exact prior
            · split <;> exact prior
        | taskFailure occurrence errors =>
            exact prior.taskFailure occurrence errors
              (List.mem_append_right _ List.mem_cons_self)
        | streamItems stream items => exact prior.streamItems stream items
        | streamSuccess stream =>
            simp only [State.dispatchGraphEvent, State.handleGraphEvent,
              State.cacheTaskFailures, List.foldl_nil]
            unfold State.streamSuccess
            split <;> exact prior
        | streamFailure stream errors =>
            simp only [State.dispatchGraphEvent, State.handleGraphEvent,
              State.cacheTaskFailures, List.foldl_nil]
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
