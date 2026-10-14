import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskHandlerProgress

/-! Complete generated incoming-task progress. An accepted structural child is represented
after actual producer settlement/release/drain or receives an actual abort in that dispatch.
Native acquisition and whole-replay task ownership remain separate obligations.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence TaskAt)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Derive exact acceptance, freshness and catalogue contributors at dispatch
-----------------------------------------------------------------------------------------

/-- The original start checker accepts the next actual alternative-kernel input. -/
theorem generatedReplay_nextAccepted {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : ((State.initialize work).runNormalized inputs).1.queue.acceptsGraphEvent event
      = true := by
  let initial := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  have recursive : initial.batchesStarted (inputs ++ [[event]]) = true := by
    rwa [ReferenceWorkQueue.inputsStarted_eq_batchesStarted] at started
  have accepted := initial.batchesStarted_acceptsBatch (inputs ++ [[event]]) recursive
  have loop (queue : Kernel) (before : List GraphEvent)
      (accepted : queue.acceptsBatch (before ++ [event]) = true)
      : (queue.replayGraphEvents before).acceptsGraphEvent event = true := by
    induction before generalizing queue with
    | nil =>
        simpa only [List.nil_append, ReferenceWorkQueue.State.acceptsBatch,
          Bool.and_true, ReferenceWorkQueue.State.replayGraphEvents, List.foldl_nil] using accepted
    | cons first rest ih =>
        have tail : (queue.handleGraphEvent first).1.acceptsBatch (rest ++ [event]) = true := by
          have both : queue.acceptsGraphEvent first = true
              ∧ (queue.handleGraphEvent first).1.acceptsBatch (rest ++ [event]) = true := by
            simpa only [List.cons_append, ReferenceWorkQueue.State.acceptsBatch,
              Bool.and_eq_true]
              using accepted
          exact both.2
        simpa only [ReferenceWorkQueue.State.replayGraphEvents, List.foldl_cons]
          using ih _ tail
  rw [(generatedReplay_beforeNext generated valid started).1]
  exact loop initial inputs.flatten
    (by simpa only [List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil] using accepted)

/-- An accepted child is not this input's settling computation, nor already settled.
Stream item receipt is not object-task completion.
-/
theorem acceptedChildTask_not_recorded {queue : Kernel} {work event task settled}
    (matching : event.MatchesWork work) (returned : task ∈ acceptedChildTasks queue event)
    (fresh : task.occurrence ∉ settled)
    : task.occurrence ∉ event.recordTaskOutcome settled := by
  have child := acceptedChildTasks_subset queue event returned
  cases event with
  | taskSuccess incoming result =>
      intro member
      rcases List.mem_cons.mp member with same | old
      · exact matching.childTasks_not_success child
          (by simp only [ReferenceWorkQueue.GraphEvent.successes, List.mem_singleton]; exact same)
      · exact fresh old
  | streamItems => exact fresh
  | taskFailure | streamSuccess | streamFailure => cases child

/-- The actual endpoint retains accepted immediate task descriptors in its proof catalogue. -/
theorem acceptedChildTask_after_registered {queue : Kernel} {event task}
    (returned : task ∈ acceptedChildTasks queue event)
    : task ∈ (queue.handleGraphEvent event).1.tasks := by
  cases event with
  | taskSuccess incoming result =>
      cases found : queue.taskNode? incoming with
      | none => simp only [acceptedChildTasks, found, List.not_mem_nil] at returned
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false => simp only [acceptedChildTasks, found, healthy, Bool.false_eq_true,
              ↓reduceIte, List.not_mem_nil] at returned
          | true =>
              simp only [acceptedChildTasks, found, healthy, ↓reduceIte] at returned
              rw [ReferenceWorkQueue.State.handleGraphEvent,
                ReferenceWorkQueue.State.taskSuccess_tasks found healthy]
              exact List.mem_append_right _ returned
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false => simp only [acceptedChildTasks, active, Bool.false_eq_true,
          ↓reduceIte, List.not_mem_nil] at returned
      | true =>
          simp only [acceptedChildTasks, active, ↓reduceIte] at returned
          rw [ReferenceWorkQueue.State.handleGraphEvent, queue.streamItems_tasks stream items active]
          exact List.mem_append_right _ returned
  | taskFailure | streamSuccess | streamFailure => cases returned

/-- Matched permanent task descriptors with the same occurrence have exact equal owners. -/
theorem registeredTask_catalogue {queue : Kernel} {work task}
    (matching : queue.RegisteredTasksMatch work) (member : task ∈ queue.tasks)
    : ∃ canonical,
        queue.task? task.occurrence = some canonical
        ∧ canonical.groups = task.groups := by
  cases found : queue.task? task.occurrence with
  | none =>
      exact False.elim ((List.find?_eq_none.mp found task member)
        ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mpr rfl))
  | some canonical =>
      have same : canonical.occurrence = task.occurrence :=
        (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp
          (List.find?_some (p := fun candidate : Task => candidate.occurrence == task.occurrence) found)
      have canonicalGroups := (matching canonical (List.mem_of_find?_eq_some found)).2
      rw [same] at canonicalGroups
      exact ⟨canonical, rfl, Option.some.inj (canonicalGroups.symm.trans (matching task member).2)⟩

-----------------------------------------------------------------------------------------
-- Fresh incoming owners cannot be excluded as successful publications
-----------------------------------------------------------------------------------------

/-- Every live group in the exact failure view has not published in this dispatch. -/
theorem failurePruningView_live_unpublished {before : Kernel}
    {event events key group}
    (found : (failurePruningView before event events).groupNode? key = some group)
    : key ∉ publicationRoots events := by
  have member := List.mem_of_find?_eq_some found
  unfold failurePruningView at member
  dsimp only at member
  obtain ⟨old, _, selected⟩ := List.mem_filterMap.mp member
  split at selected
  · contradiction
  · rename_i unpublished
    cases Option.some.inj selected
    intro published
    apply unpublished
    change (publicationRoots events).contains old.group.node.ref = true
    rw [ReferenceWorkQueue.State.groupNode?_ref found]
    exact List.contains_iff_mem.mpr published

/-- A finite live descendant path supplies the target's actual group lookup. -/
theorem liveDescendant_targetFound {queue : Kernel} {root key}
    (path : queue.LiveDescendant root key)
    : ∃ group, queue.groupNode? key = some group := by
  induction path with
  | self found => exact ⟨_, found⟩
  | child _ _ _ ih => exact ih

/-- No owner of a fresh incoming task is one of this handler's successful carriers.
Retention contradicts actual retirement; a failure path contradicts the exact view's
successful-key exclusion. Even absent original owners are covered by carrier provenance.
-/
theorem generatedIncomingTask_unpublished {work inputs event task}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    (returned
      : task
        ∈ acceptedChildTasks ((State.initialize work).runNormalized inputs).1.queue event)
    : ∀ key ∈ task.groups.map DeliveryNode.ref,
        key
        ∉ publicationRoots
            ((((State.initialize work).runNormalized inputs).1.queue).handleGraphEvent
              event).2 := by
  intro key contributes published
  let before := ((State.initialize work).runNormalized inputs).1.queue
  obtain ⟨_, matching, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have accounted := generatedReplay_nextAccounting generated valid started
  have closures := ReferenceWorkQueue.State.handleGraphEvent_closureAccounting accounted.liveGroups
    accounted.taskGroups event matching
  have projection := generatedSnapshot_projection generated valid
    (generatedReplay_beforeNext generated valid started).2.1
  have live := registrationSnapshot_publicationRoots_live before event projection published
  rcases GeneratedIncomingTaskOwnerProgress_holds work inputs event generated valid started task returned
      key contributes live with retained | cut
  · have absent := (closures.closed key (by
      obtain ⟨group, groups, streams, emitted, same⟩ := mem_publicationRoots.mp published
      exact List.mem_flatMap.mpr ⟨_, emitted, same ▸ List.mem_cons_self⟩)).lookup_none
    exact (ReferenceWorkQueue.State.groupNode?_eq_none_iff _ _).mp absent retained
  · obtain ⟨_, _, path⟩ := cut
    obtain ⟨group, found⟩ := liveDescendant_targetFound path
    exact failurePruningView_live_unpublished found published

-----------------------------------------------------------------------------------------
-- Complete incoming-task classification at the actual endpoint, not just registration
-----------------------------------------------------------------------------------------

/-- Every accepted immediate task is represented at the actual endpoint or aborted by
this same dispatch. All registration, unsettled links and failure-cut premises are derived.
-/
theorem generatedAcceptedTask_progress {work inputs event task}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    (returned
      : task
        ∈ acceptedChildTasks ((State.initialize work).runNormalized inputs).1.queue event)
    : let before := ((State.initialize work).runNormalized inputs).1
      let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
      RecordTargetRepresented reduced.state.queue (.task task.occurrence)
      ∨ .abortTask task.occurrence ∈ reduced.effects := by
  let before := ((State.initialize work).runNormalized inputs).1
  let snapshot := registrationSnapshot before.queue event
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have notSettled : task.occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten := by
    intro processed
    exact acceptedChildTask_unsettled matching prior fresh returned
      (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities _ processed)
  have registered := registrationSnapshot_acceptedTask_registered returned
  have pending := acceptedChildTask_not_recorded matching returned notSettled
  by_cases owned :
    ∃ owner ∈ task.groups, ∃ group, snapshot.groupNode? owner.ref = some group
  · exact generatedPreparedTask_progress generated valid started registered pending owned
  · have ownerless : ∀ owner ∈ task.groups, snapshot.groupNode? owner.ref = none := by
      intro owner member
      cases found : snapshot.groupNode? owner.ref with
      | none => rfl
      | some group => exact False.elim (owned ⟨owner, member, group, found⟩)
    have accounted := generatedReplay_nextAccounting generated valid started
    have aborted := registration_rejectedTask_aborted
      ⟨accounted.refs, accounted.liveGroups, accounted.taskGroups, accounted.links⟩
      matching notSettled returned ownerless
    have canonical := generatedReplay_beforeNextState generated valid started
    change before = { queue := before.queue } at canonical
    dsimp only
    apply Or.inr
    change .abortTask task.occurrence ∈ (({ state := before } : GraphBatchResult).handleGraphEvent event).effects
    rw [canonical]
    exact aborted

/-- Structural incoming-task counterpart of the already proved adopted-source progress. -/
def GeneratedAdoptedTaskProgress : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ producer address owners payload,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        .adopt producer ∈ graphEffects before.queue event
        → TaskAt work (.executionGroup address) owners (some producer) payload
        → RecordTargetRepresented reduced.state.queue (.task (.executionGroup address))
          ∨ .abortTask (.executionGroup address) ∈ reduced.effects

/-- Generated matching work supplies the actual child chunk; the full handler theorem
constructs endpoint representation or disposal without caller-supplied invariants.
-/
theorem GeneratedAdoptedTaskProgress_holds : GeneratedAdoptedTaskProgress := by
  intro work inputs event generated valid started producer address owners payload
  dsimp only
  intro adopted known
  obtain ⟨_, matching, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨task, returned, same⟩ := adoptedTask_returned matching adopted known
  exact same ▸ generatedAcceptedTask_progress generated valid started returned

-----------------------------------------------------------------------------------------
-- Connect actual incoming producer leases without inferring native acquisition
-----------------------------------------------------------------------------------------

/-- Only actual acquired/listed task leases of accepted producers need structural identity.
This native abstraction-map obligation mentions immutable work and producer identity,
not desired endpoint representation, abort effects, or resource-inventory completeness.
-/
def ProducerTasksMatchWork (work : Work) (resources : ResourceState)
    (inventories : ProducerInventories) (effects : List HostEffect)
    : Prop :=
  ∀ producer occurrence,
    .adopt producer ∈ effects
    → .task occurrence ∈ inventories producer
    → resources (.task occurrence) = .owned (.producer producer)
    → ∃ address owners payload,
        occurrence = .executionGroup address
        ∧ TaskAt work occurrence owners (some producer) payload

/-- A transferred task still owned by the queue after dispatch has an actual endpoint
record. The only native premise maps an independently acquired task to structural work;
registration, retention and same-dispatch disposal are supplied by the generated proof.
Existing queue-owned tasks require their separate pending/completion-history invariant.
-/
def GeneratedDispatchIncomingTaskRepresentation : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories),
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        ProducerTasksMatchWork work resources inventories
          (graphEffects before.queue event)
        → ∀ producer occurrence,
            .adopt producer ∈ graphEffects before.queue event
            → .task occurrence ∈ inventories producer
            → resources (.task occurrence) = .owned (.producer producer)
            → (resources.observeDispatch inventories before event).1 (.task occurrence)
              = .owned .queue
            → RecordTargetRepresented reduced.state.queue (.task occurrence)

/-- Actual dispatch cleanup excludes the abort alternative for a still-queue-owned lease.
The same resource state, inventory, input and handler endpoint occur throughout.
-/
theorem GeneratedDispatchIncomingTaskRepresentation_holds
    : GeneratedDispatchIncomingTaskRepresentation := by
  intro work inputs event generated valid started resources inventories
  dsimp only
  intro identities producer occurrence adopted listed acquired owned
  obtain ⟨address, owners, payload, same, known⟩ := identities producer occurrence adopted listed acquired
  rcases GeneratedAdoptedTaskProgress_holds work inputs event generated valid started producer address owners payload
      adopted (same ▸ known) with kept | aborted
  · exact same.symm ▸ kept
  · obtain ⟨_, absent⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.task occurrence) owned
    exact False.elim (absent (List.mem_filterMap.mpr
      ⟨.abortTask occurrence, same.symm ▸ aborted, rfl⟩))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
