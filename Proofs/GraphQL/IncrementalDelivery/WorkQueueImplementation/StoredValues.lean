import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplay

/-! Stored values retain their exact host-event provenance through queue bookkeeping. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Bookkeeping preserves arbitrary facts about stored occurrence/value pairs
-----------------------------------------------------------------------------------------

/-- Every nonempty stored value satisfies a predicate at its own task occurrence.
The predicate can express payload provenance or occurrence-indexed source evidence. -/
def State.StoredValuesSatisfy (queue : State)
    (property : Occurrence → ExecutionGroupValue → Prop)
    : Prop :=
  ∀ node ∈ queue.taskNodes,
    ∀ value, node.value = some value → property node.task.occurrence value

/-- Weaker value facts remain true for the unchanged task-node map.
Witness: apply the implication to each stored occurrence/value pair. -/
theorem State.StoredValuesSatisfy.mono {queue : State} {before after}
    (stored : queue.StoredValuesSatisfy before)
    (weaken : ∀ occurrence value, before occurrence value → after occurrence value)
    : queue.StoredValuesSatisfy after :=
  fun node member value same => weaken _ _ (stored node member value same)

/-- Group-node updates leave stored task values unchanged.
Witness: the updated record has exactly the original task-node map. -/
theorem State.StoredValuesSatisfy.putGroupNode {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (updated : GroupNode)
    : (queue.putGroupNode updated).StoredValuesSatisfy property :=
  stored

/-- Removing a task preserves provenance for every remaining stored value.
Witness: task cleanup filters the map without changing any surviving record.
-/
theorem State.StoredValuesSatisfy.removeTask {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (occurrence : Occurrence)
    : (queue.removeTask occurrence).StoredValuesSatisfy property :=
  fun node member => stored node (List.mem_filter.mp member).1

/-- Pointwise preservation lifts to an executable left fold.
Witness: induction over the elements without changing their processing order. -/
private theorem fold_preserves {α β : Type} (property : α → Prop) (step : α → β → α)
    (preserved : ∀ state item, property state → property (step state item))
    (items : List β) (state : α) (initial : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact initial
  | cons item rest ih => exact ih _ (preserved state item initial)

/-- Replacing a task node preserves value facts when its new stored value satisfies them.
Witness: every mapped node is either the replacement or an unchanged old node. -/
theorem State.StoredValuesSatisfy.putTaskNode {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (updated : TaskNode)
    (allowed
      : ∀ value, updated.value = some value → property updated.task.occurrence value)
    : (queue.putTaskNode updated).StoredValuesSatisfy property := by
  intro node member value same
  obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp member
  split at equal
  · subst node
    exact allowed value same
  · subst node
    exact stored old oldMember value same

/-- Group registration and parent-link installation do not modify task nodes.
Witness: the exact task-map equation for group integration. -/
theorem State.StoredValuesSatisfy.addGroups {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (groups : List Group)
    : (queue.addGroups groups).1.StoredValuesSatisfy property := by
  intro node member
  rw [State.addGroups_taskNodes] at member
  exact stored node member

/-- Task registration retains old values and can create only an empty new task node.
Witness: the existing old-or-new characterization of executable task integration. -/
theorem State.StoredValuesSatisfy.addTask {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (task : Task)
    : (queue.addTask task).StoredValuesSatisfy property := by
  intro node member value same
  rcases queue.addTask_startedOldOrNew task member with old | new
  · exact stored node old value same
  · subst node
    cases same

/-- Stream integration only appends stream refs to an existing task's child list.
Witness: the updated producer retains its occurrence and stored value exactly. -/
theorem State.StoredValuesSatisfy.addStreams {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.StoredValuesSatisfy property := by
  cases parentTask with
  | none => exact stored
  | some occurrence =>
      simp only [State.addStreams]
      split
      · exact stored
      · rename_i node found
        apply stored.putTaskNode
        exact stored node (List.mem_of_find?_eq_some found)

/-- Child-work integration preserves all old stored-value facts.
Witness: group integration, empty-node task creation, and value-preserving stream links. -/
theorem State.StoredValuesSatisfy.maybeIntegrateWork {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.StoredValuesSatisfy property := by
  have tasks := fold_preserves (fun state => state.StoredValuesSatisfy property) State.addTask
    (fun _ task prior => prior.addTask task) work.tasks _ (stored.addGroups work.groups)
  exact tasks.addStreams work.streams parentTask

/-- Pruning changes only groups, not stored values.
Witness: the exact task-map equation for the pruning loop. -/
theorem State.StoredValuesSatisfy.pruneEmptyGroups {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.StoredValuesSatisfy property := by
  intro node member
  rw [State.pruneEmptyGroups_taskNodes] at member
  exact stored node member

/-- Starting a task either keeps its node or appends a node with no stored value.
Witness: direct cases of the executable start operation. -/
theorem State.StoredValuesSatisfy.startTask {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (occurrence : Occurrence)
    : (queue.startTask occurrence).StoredValuesSatisfy property := by
  unfold State.startTask
  split
  · exact stored
  · split
    · exact stored
    · intro node member value same
      rcases List.mem_append.mp member with old | new
      · exact stored node old value same
      · have equal := List.mem_singleton.mp new
        subst node
        cases same

/-- Starting a group cannot create a resolved value.
Witness: lift empty-node task start through the group's membership fold. -/
theorem State.StoredValuesSatisfy.startGroup {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (ref : NodeRef)
    : (queue.startGroup ref).StoredValuesSatisfy property := by
  unfold State.startGroup
  split
  · exact stored
  · split
    · exact stored
    · exact fold_preserves (fun state => state.StoredValuesSatisfy property) State.startTask
        (fun _ occurrence prior => prior.startTask occurrence) _ _ stored

/-- Stream start changes only the active stream refs.
Witness: neither executable branch modifies task nodes. -/
theorem State.StoredValuesSatisfy.startStream {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (ref : NodeRef)
    : (queue.startStream ref).StoredValuesSatisfy property := by
  unfold State.startStream
  split <;> exact stored

/-- Starting released work preserves stored-value facts.
Witness: compose the group/task and stream activation folds. -/
theorem State.StoredValuesSatisfy.startNewWork {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (work : NewWork)
    : (queue.startNewWork work).StoredValuesSatisfy property := by
  let current :=
    { queue with rootGroups := queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.ref }
  have groups := fold_preserves (fun state => state.StoredValuesSatisfy property)
    State.startGroup (fun _ ref prior => prior.startGroup ref)
    (work.newGroups.map Execution.DeliveryNode.ref) current stored
  exact fold_preserves (fun state => state.StoredValuesSatisfy property) State.startStream
    (fun _ ref prior => prior.startStream ref) _ _ groups

/-- Failure removal only filters existing task nodes.
Witness: every surviving value is retained from the original node map. -/
theorem State.StoredValuesSatisfy.removeGroup {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (ref : NodeRef)
    : (queue.removeGroup ref).StoredValuesSatisfy property :=
  fun node member => stored node (List.mem_filter.mp member).1

/-- Successful group flushing only removes stored nodes.
Witness: the exact flush's residual task-map inclusion, including subsequent pruning. -/
theorem State.StoredValuesSatisfy.finishGroupSuccess {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.StoredValuesSatisfy property := by
  obtain ⟨_, _, _, _, retained, _⟩ := queue.finishGroupSuccess_publications group
  exact fun node member => stored node (retained member)

/-- Recursive draining preserves every stored occurrence/value property.
Witness: successful flushes remove values, activation adds only empty nodes, and failed
closures filter existing nodes. No source or queue-accounting premise is needed.
-/
theorem State.StoredValuesSatisfy.drainReadyGroups {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property)
    : queue.drainReadyGroups.1.StoredValuesSatisfy property := by
  apply State.drainReadyGroups_preserves (fun current => current.StoredValuesSatisfy property)
    (valid := stored)
  · intro current node prior _ _ _ _
    exact (prior.finishGroupSuccess node).startNewWork _
  · intro current node errors prior _ _ _
    exact prior.removeGroup _

-----------------------------------------------------------------------------------------
-- Only a task-success input can install a resolved object value
-----------------------------------------------------------------------------------------

/-- Successful settlement installs its exact supplied value and preserves all other facts.
Witness: value replacement, child integration, the single-pass contributor fold, and
released-work activation/draining. Values may leave the state during this same handler. -/
theorem State.StoredValuesSatisfy.taskSuccess {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (occurrence : Occurrence)
    (result : TaskResult) (allowed : property occurrence result.value)
    : (queue.taskSuccess occurrence result).1.StoredValuesSatisfy property := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using stored
  | some node =>
      have equal := (State.taskNode?_some found).2
      have installed := stored.putTaskNode { node with value := some result.value } (by
        intro value same
        cases same
        simpa only [equal] using allowed)
      have integrated := installed.maybeIntegrateWork result.work (some occurrence)
      have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
          (prior : acc.1.StoredValuesSatisfy property)
          : (successGroupStep acc group).1.StoredValuesSatisfy property := by
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact prior
        · split
          · exact (prior.putGroupNode _).finishGroupSuccess _
          · exact prior
      have processed := fold_preserves (fun acc => acc.1.StoredValuesSatisfy property)
        successGroupStep step node.task.groups (_, [], {}) integrated
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact stored.removeTask occurrence
      exact (processed.startNewWork _).drainReadyGroups

/-- Failed task settlement cannot install a value.
Witness: its owner fold updates failure caches or filters nodes through group removal. -/
theorem State.StoredValuesSatisfy.taskFailure {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.StoredValuesSatisfy property := by
  unfold State.taskFailure
  split
  · exact stored
  · split
    · exact stored.removeTask occurrence
    apply fold_preserves
      (fun acc : State × List WorkQueueEvent => acc.1.StoredValuesSatisfy property)
    · intro acc group prior
      obtain ⟨current, events⟩ := acc
      dsimp only
      split
      · exact prior
      · split
        · exact prior.removeGroup _
        · exact prior
    · exact fun node member => stored node (List.mem_filter.mp member).1

/-- Item arrival integrates and starts child work, but creates no resolved object value.
Witness: the item fold and final drain compose value-preserving integration and release. -/
theorem State.StoredValuesSatisfy.streamItems {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.StoredValuesSatisfy property := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have folded := fold_preserves (fun acc => acc.1.StoredValuesSatisfy property) step
    (fun acc item prior =>
      ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
    items (queue, [], [], []) stored
  unfold State.streamItems
  split
  · exact stored
  · exact folded.drainReadyGroups

/-- All event handlers preserve the property if any newly supplied task value satisfies it.
Witness: task success is the only storing branch; stream closures leave task nodes intact.
-/
theorem State.StoredValuesSatisfy.handleGraphEvent {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (event : GraphEvent)
    (allowed
      : ∀ occurrence result,
          event = .taskSuccess occurrence result → property occurrence result.value)
    : (queue.handleGraphEvent event).1.StoredValuesSatisfy property := by
  cases event with
  | taskSuccess occurrence result =>
      exact stored.taskSuccess occurrence result (allowed _ _ rfl)
  | taskFailure occurrence errors => exact stored.taskFailure occurrence errors
  | streamItems stream items => exact stored.streamItems stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact stored
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact stored

/-- Initial integration and activation store no resolved values.
Witness: the empty task map satisfies every value predicate, preserved through creation. -/
theorem createWorkQueue_storedValues (work : Work) (property)
    : (State.initialize work).StoredValuesSatisfy property := by
  have empty : ({} : State).StoredValuesSatisfy property := by
    intro node member
    cases member
  exact ((empty.maybeIntegrateWork work).pruneEmptyGroups _).startNewWork _

/-- Every stored object value is exactly the payload of an earlier task-success input.
Witness: induction through actual handlers, retaining its task occurrence and host event.
No source validity or scheduler-conformance premise is needed for this provenance fact. -/
theorem createWorkQueue_replay_storedValues (work : Work) (events : List GraphEvent)
    : ((State.initialize work).replayGraphEvents events).StoredValuesSatisfy
        (fun occurrence value =>
          ∃ result, .taskSuccess occurrence result ∈ events ∧ result.value = value) := by
  let property := fun occurrence value => ∃ result,
    GraphEvent.taskSuccess occurrence result ∈ events ∧ result.value = value
  have loop (more : List GraphEvent) (included : more.Subset events) (queue : State)
      (stored : queue.StoredValuesSatisfy property)
      : (queue.replayGraphEvents more).StoredValuesSatisfy property := by
    induction more generalizing queue with
    | nil => exact stored
    | cons event rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem event member))
        apply stored.handleGraphEvent event
        intro occurrence result same
        exact ⟨result, same ▸ included List.mem_cons_self, rfl⟩
  exact loop events (List.Subset.refl _) _ (createWorkQueue_storedValues work property)

-----------------------------------------------------------------------------------------
-- Exact source matching reaches the stored and published data/error payloads
-----------------------------------------------------------------------------------------

/-- Every member of a valid source prefix matches its fixed work descriptor.
Witness: membership in the source derivation's old prefix or its final matching event. -/
theorem ValidGraphEvents.event_matches {work events}
    (valid : ValidGraphEvents work events) {event : GraphEvent} (member : event ∈ events)
    : event.MatchesWork work := by
  induction valid with
  | nil => cases member
  | @append before last validBefore matching fresh ready ih =>
      rcases List.mem_append.mp member with earlier | final
      · exact ih earlier
      · have same := List.mem_singleton.mp final
        subst event
        exact matching

/-- Every stored value after legal replay retains its exact successful work outcome.
Witness: the earlier task-success input and its source matching, including all contributor
descriptors, response data, response path, and execution-error count. -/
theorem createWorkQueue_replay_storedValues_match {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).StoredValuesSatisfy
        (fun occurrence value =>
          ∃ result,
            .taskSuccess occurrence result ∈ events
            ∧ result.value = value
            ∧ (GraphEvent.taskSuccess occurrence result).MatchesWork work) := by
  refine (createWorkQueue_replay_storedValues (Work.fromExecution work) events).mono ?_
  intro occurrence value ⟨result, member, same⟩
  exact ⟨result, member, same, valid.event_matches member⟩

/-- Publishing a stored value preserves any occurrence-indexed source fact about it.
Witness: recover the selected task node from the actual emitted event, then use its
stored-value certificate. No task settlement is invented at publication time. -/
theorem State.StoredValuesSatisfy.published {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) {group trigger values value}
    (emitted : .groupValues trigger values ∈ (queue.finishGroupSuccess group).2.1)
    (member : value ∈ values)
    : ∃ occurrence ∈ group.tasks, property occurrence value := by
  obtain ⟨_, node, registered, belongs, same, _⟩ :=
    State.finishGroupSuccess_value emitted member
  exact ⟨node.task.occurrence, belongs, stored node registered value same⟩

/-- Flushing after legal source replay can publish only an exact earlier success payload.
Witness: replay provenance plus the actual group-flush witness. It is valid even when
the value waited through other events; it does not equate settlement and publication. -/
theorem createWorkQueue_replay_publishedValue {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    {group trigger values value}
    (emitted
      : .groupValues trigger values
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              events).finishGroupSuccess
            group).2.1)
    (member : value ∈ values)
    : ∃ occurrence ∈ group.tasks,
        ∃ result,
          .taskSuccess occurrence result ∈ events
          ∧ result.value = value
          ∧ (GraphEvent.taskSuccess occurrence result).MatchesWork work :=
  (createWorkQueue_replay_storedValues_match valid).published emitted member

-----------------------------------------------------------------------------------------
-- Carry provenance through the actual single-pass success handler's emitted events
-----------------------------------------------------------------------------------------

/-- Every raw object value has an occurrence witnessing the chosen source property.
The queue's raw event omits that occurrence; this is proof evidence, not new wire data. -/
def PublishedValuesSatisfy (property : Occurrence → ExecutionGroupValue → Prop)
    (events : List WorkQueueEvent)
    : Prop :=
  ∀ trigger values,
    .groupValues trigger values ∈ events
    → ∀ value ∈ values, ∃ occurrence, property occurrence value

/-- Concatenation retains the provenance of both raw event sequences.
Witness: an emitted group-value event belongs to one of the two lists. -/
theorem PublishedValuesSatisfy.append {property left right}
    (first : PublishedValuesSatisfy property left)
    (second : PublishedValuesSatisfy property right)
    : PublishedValuesSatisfy property (left ++ right) := by
  intro trigger values emitted value member
  rcases List.mem_append.mp emitted with before | after
  · exact first trigger values before value member
  · exact second trigger values after value member

/-- Flushing preserves every stored source fact in the emitted raw object values.
Witness: the selected stored-node certificate, retaining its original occurrence. -/
theorem State.StoredValuesSatisfy.finishGroupSuccess_outputs {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (group : GroupNode)
    : PublishedValuesSatisfy property (queue.finishGroupSuccess group).2.1 := by
  intro trigger values emitted value member
  obtain ⟨occurrence, _, certificate⟩ := stored.published emitted member
  exact ⟨occurrence, certificate⟩

/-- Object values emitted during recursive draining retain stored source provenance.
Witness: induction on the actual drain budget, composing successful flush output with
later drain output; cached-failure events contain no object values.
-/
theorem State.StoredValuesSatisfy.drainReadyGroups_outputs {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property)
    : PublishedValuesSatisfy property queue.drainReadyGroups.2 := by
  have loop (fuel : Nat) (current : State) (prior : current.StoredValuesSatisfy property)
      : PublishedValuesSatisfy property (State.drainReadyGroups.go fuel current).2 := by
    induction fuel generalizing current with
    | zero => intro trigger values impossible; cases impossible
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · intro trigger values impossible; cases impossible
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              dsimp only
              exact (prior.finishGroupSuccess_outputs node).append
                (ih _ ((prior.finishGroupSuccess node).startNewWork _))
          | some errors =>
              dsimp only
              apply PublishedValuesSatisfy.append
              · intro trigger values impossible
                simp [State.finishGroupFailure] at impossible
              · exact ih _ (prior.removeGroup _)
  exact loop _ queue stored

/-- The success handler's object publications preserve old and newly installed value facts.
Witness: a joint state/output invariant through the contributor fold and final drain.
Earlier flushes can remove shared memberships, but cannot introduce unrelated values. -/
theorem State.StoredValuesSatisfy.taskSuccess_outputs {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (occurrence : Occurrence)
    (result : TaskResult) (allowed : property occurrence result.value)
    : PublishedValuesSatisfy property (queue.taskSuccess occurrence result).2 := by
  cases found : queue.taskNode? occurrence with
  | none =>
      intro trigger values emitted
      simp [State.taskSuccess, found] at emitted
  | some node =>
      have equal := (State.taskNode?_some found).2
      have installed := stored.putTaskNode { node with value := some result.value } (by
        intro value same
        cases same
        simpa only [equal] using allowed)
      have integrated := installed.maybeIntegrateWork result.work (some occurrence)
      let invariant := fun acc : State × List WorkQueueEvent × NewWork =>
        acc.1.StoredValuesSatisfy property ∧ PublishedValuesSatisfy property acc.2.1
      have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
          (prior : invariant acc) : invariant (successGroupStep acc group) := by
        obtain ⟨current, events, released⟩ := acc
        obtain ⟨valuesKnown, emittedKnown⟩ := prior
        dsimp only [successGroupStep]
        split
        · exact ⟨valuesKnown, emittedKnown⟩
        · rename_i owner foundOwner
          split
          · have updated := valuesKnown.putGroupNode { owner with pending := owner.pending - 1 }
            exact ⟨updated.finishGroupSuccess _,
              emittedKnown.append (updated.finishGroupSuccess_outputs _)⟩
          · exact ⟨valuesKnown, emittedKnown⟩
      have processed := fold_preserves invariant successGroupStep step node.task.groups
        (_, [], {}) ⟨integrated, by intro trigger values impossible; cases impossible⟩
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · intro trigger values impossible
        cases impossible
      exact processed.2.append ((processed.1.startNewWork _).drainReadyGroups_outputs)

/-- Actual success-handler publications have exact source payloads from the current prefix.
Witness: prior stored provenance plus the current matching input, transported through
integration and every flush. Earlier settlements may be published by this later event. -/
theorem createWorkQueue_replay_taskSuccess_publishedValues {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events) {occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : PublishedValuesSatisfy
        (fun source value =>
          ∃ supplied,
            .taskSuccess source supplied ∈ events ++ [.taskSuccess occurrence result]
            ∧ supplied.value = value
            ∧ (GraphEvent.taskSuccess source supplied).MatchesWork work)
        (((State.initialize (Work.fromExecution work)).replayGraphEvents
            events).taskSuccess
          occurrence result).2 := by
  let property := fun source value => ∃ supplied,
    GraphEvent.taskSuccess source supplied ∈ events ++ [.taskSuccess occurrence result]
      ∧ supplied.value = value ∧ (GraphEvent.taskSuccess source supplied).MatchesWork work
  have stored := (createWorkQueue_replay_storedValues_match valid).mono (after := property) (by
    intro source value ⟨supplied, member, same, exactSource⟩
    exact ⟨supplied, List.mem_append_left [.taskSuccess occurrence result] member,
      same, exactSource⟩)
  exact stored.taskSuccess_outputs occurrence result
    ⟨result, List.mem_append_right _ List.mem_cons_self, rfl, matching⟩

-----------------------------------------------------------------------------------------
-- Every handler's object output retains a genuine task-success source
-----------------------------------------------------------------------------------------

/-- Task failure emits no object publication, including when it retains a latent error.
Witness: every fold step appends only a group-failure notice or leaves output unchanged.
-/
theorem State.taskFailure_publishedValues (queue : State) (occurrence : Occurrence)
    (errors : Nat) (property : Occurrence → ExecutionGroupValue → Prop)
    : PublishedValuesSatisfy property (queue.taskFailure occurrence errors).2 := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : PublishedValuesSatisfy property acc.2)
      : PublishedValuesSatisfy property (groups.foldl step acc).2 := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        unfold step
        split
        · exact prior
        · split
          · apply prior.append
            intro trigger values impossible
            simp [State.finishGroupFailure] at impossible
          · exact prior
  unfold State.taskFailure
  split
  · intro trigger values impossible; cases impossible
  · split
    · intro trigger values impossible; cases impossible
    exact loop _ (_, []) (by intro trigger values impossible; cases impossible)

/-- A stream handler may drain stored object values, all with their earlier provenance.
Witness: item integration installs no object value; the final recursive drain can flush
only the preserved stored values. The leading stream-value event is not an object patch.
-/
theorem State.StoredValuesSatisfy.streamItems_outputs {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : PublishedValuesSatisfy property (queue.streamItems stream items).2 := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have folded := fold_preserves (fun acc => acc.1.StoredValuesSatisfy property) step
    (fun acc item prior =>
      ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
    items (queue, [], [], []) stored
  unfold State.streamItems
  split
  · intro trigger values impossible; cases impossible
  · intro trigger values emitted value member
    have later := (List.mem_cons.mp emitted).resolve_left (by intro impossible; cases impossible)
    exact folded.drainReadyGroups_outputs trigger values later value member

/-- Every event preserves the source property on emitted object values.
Witness: success may install its supplied value, item arrival may drain earlier ones,
and all failure/stream-close controls contain no object payloads.
-/
theorem State.StoredValuesSatisfy.handleGraphEvent_outputs {queue : State} {property}
    (stored : queue.StoredValuesSatisfy property) (event : GraphEvent)
    (allowed
      : ∀ occurrence result,
          event = .taskSuccess occurrence result → property occurrence result.value)
    : PublishedValuesSatisfy property (queue.handleGraphEvent event).2 := by
  cases event with
  | taskSuccess occurrence result =>
      exact stored.taskSuccess_outputs occurrence result (allowed _ _ rfl)
  | taskFailure occurrence errors => exact queue.taskFailure_publishedValues _ _ _
  | streamItems stream items => exact stored.streamItems_outputs stream items
  | streamSuccess stream =>
      intro trigger values emitted
      simp only [State.handleGraphEvent, State.streamSuccess] at emitted
      split at emitted <;> simp at emitted
  | streamFailure stream errors =>
      intro trigger values emitted
      simp only [State.handleGraphEvent, State.streamFailure] at emitted
      split at emitted <;> simp at emitted

/-- Every handler after a legal source prefix emits only exact successful source payloads.
Witness: earlier stored provenance or the current task-success input; recursive draining
does not invent a new settlement. This covers stream-triggered object flushes as well.
-/
theorem createWorkQueue_replay_event_publishedValues {work : Execution.Work}
    {before : List GraphEvent} (valid : ValidGraphEvents work before) (event : GraphEvent)
    (matching : event.MatchesWork work)
    : PublishedValuesSatisfy
        (fun occurrence value =>
          ∃ supplied,
            .taskSuccess occurrence supplied ∈ before ++ [event]
            ∧ supplied.value = value
            ∧ (GraphEvent.taskSuccess occurrence supplied).MatchesWork work)
        (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).handleGraphEvent
          event).2 := by
  let property := fun occurrence value => ∃ supplied,
    GraphEvent.taskSuccess occurrence supplied ∈ before ++ [event]
      ∧ supplied.value = value ∧ (GraphEvent.taskSuccess occurrence supplied).MatchesWork work
  have stored := (createWorkQueue_replay_storedValues_match valid).mono (after := property) (by
    intro occurrence value ⟨supplied, member, same, exactSource⟩
    exact ⟨supplied, List.mem_append_left [event] member, same, exactSource⟩)
  apply stored.handleGraphEvent_outputs event
  intro occurrence result same
  subst event
  exact ⟨result, List.mem_append_right _ List.mem_cons_self, rfl, matching⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
