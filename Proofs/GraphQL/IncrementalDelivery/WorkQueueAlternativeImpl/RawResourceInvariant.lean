import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceInitialization

/-! Resource progress inside an arbitrary-width FIFO batch. An open raw prefix is the
same actual generated normalized state; after roots become empty no further adoption is
possible, even before the batch wrapper clears records. Neither case assumes resource safety.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
private abbrev Kernel := ReferenceWorkQueue.State

private abbrev initial (work : Work) :=
  ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)

-----------------------------------------------------------------------------------------
-- Relate an open raw source prefix to the existing generated handler witnesses
-----------------------------------------------------------------------------------------

/-- Batch flag insertion is absent exactly when its raw endpoint still has roots. -/
theorem referenceBatch_openRoots (queue : Kernel) (events : List GraphEvent)
    (running : queue.terminated = false)
    (openRoots
      : ((queue.replayGraphEvents events).rootGroups.isEmpty
          && (queue.replayGraphEvents events).rootStreams.isEmpty)
        ≠ true)
    : (queue.handleGraphEvents events).1 = queue.replayGraphEvents events := by
  unfold ReferenceWorkQueue.State.handleGraphEvents
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  cases folded
        : events.foldl
            (fun acc event =>
              (
                (acc.1.handleGraphEvent event).1,
                acc.2 ++ (acc.1.handleGraphEvent event).2
              ))
            (queue, []) with
  | mk current output =>
      have same := queue.foldGraphEvents_state [] events
      rw [folded] at same
      simp only at same
      subst current
      simp only [openRoots, Bool.false_eq_true, ↓reduceIte]

private def rawPrefixBatches (events : List GraphEvent) :=
  if events = [] then [] else [events]

private theorem rawPrefix_flatten (events : List GraphEvent)
    : (rawPrefixBatches events).flatten = events := by
  cases events <;> simp [rawPrefixBatches]

private theorem rawReplay_running (work : Work) (events : List GraphEvent)
    : ((initial work).replayGraphEvents events).terminated = false := by
  rw [← ReferenceWorkQueue.State.rawEventReplay_state, ReferenceWorkQueue.State.rawEventReplay_terminated]
  exact ReferenceWorkQueue.createWorkQueue_terminated _

private theorem rawPrefix_state (work : Work) (events : List GraphEvent)
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work events)
    (accepted : (initial work).acceptsBatch events = true)
    (openRoots
      : (((initial work).replayGraphEvents events).rootGroups.isEmpty
          && ((initial work).replayGraphEvents events).rootStreams.isEmpty)
        ≠ true)
    : ((State.initialize work).runNormalized (rawPrefixBatches events)).1
      = { queue := (initial work).replayGraphEvents events } := by
  cases events with
  | nil =>
      change State.initialize work = { queue := initial work }
      rw [State.initialize_fromReference]
      simp only [State.fromReference,
        ReferenceWorkQueue.createWorkQueue_terminated, Bool.false_eq_true, ↓reduceIte]
  | cons first rest =>
      simp only [rawPrefixBatches, List.cons_ne_nil, ↓reduceIte]
      have started : ReferenceWorkQueue.inputsStarted work [first :: rest] = true := by
        simpa only [ReferenceWorkQueue.inputsStarted_eq_batchesStarted,
          ReferenceWorkQueue.State.batchesStarted,
          ReferenceWorkQueue.createWorkQueue_terminated, Bool.not_false,
          List.isEmpty_cons, Bool.true_and, Bool.and_true]
          using accepted
      rw [State.runNormalized_initialize work [first :: rest] generated
        (by simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using valid) started]
      dsimp only
      rw [ReferenceWorkQueue.State.runNormalized_stateFold]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [referenceBatch_openRoots _ _ (ReferenceWorkQueue.createWorkQueue_terminated _) openRoots]
      simp only [State.fromReference, rawReplay_running, Bool.false_eq_true, ↓reduceIte]

private theorem rawPrefix_startedNext {work events event}
    (accepted : (initial work).acceptsBatch (events ++ [event]) = true)
    (openRoots
      : (((initial work).replayGraphEvents events).rootGroups.isEmpty
          && ((initial work).replayGraphEvents events).rootStreams.isEmpty)
        ≠ true)
    : ReferenceWorkQueue.inputsStarted work (rawPrefixBatches events ++ [[event]])
      = true := by
  have prior := ReferenceWorkQueue.State.acceptsBatch_prefix accepted
  have next := ReferenceWorkQueue.State.acceptsBatch_atPrefix (initial work) events event []
    (by simpa using accepted)
  cases events with
  | nil =>
      simpa [rawPrefixBatches, ReferenceWorkQueue.inputsStarted_eq_batchesStarted,
        ReferenceWorkQueue.State.batchesStarted, ReferenceWorkQueue.createWorkQueue_terminated,
        ReferenceWorkQueue.State.acceptsBatch] using accepted
  | cons first rest =>
      simp only [rawPrefixBatches, List.cons_ne_nil, ↓reduceIte, List.cons_append, List.nil_append,
        ReferenceWorkQueue.inputsStarted_eq_batchesStarted, ReferenceWorkQueue.State.batchesStarted,
        ReferenceWorkQueue.createWorkQueue_terminated, Bool.not_false, List.isEmpty_cons, Bool.true_and, Bool.and_true]
      rw [referenceBatch_openRoots _ _ (ReferenceWorkQueue.createWorkQueue_terminated _) openRoots]
      simp only [rawReplay_running, Bool.not_false, ReferenceWorkQueue.State.acceptsBatch, next, Bool.and_true]
      simpa only [ReferenceWorkQueue.State.acceptsBatch] using prior

-----------------------------------------------------------------------------------------
-- Empty roots cannot adopt another producer before terminal batch erasure
-----------------------------------------------------------------------------------------

/-- No actual adoption label is emitted when all graph roots are gone. Immutable task
registration and live-contributor coverage exclude a healthy owner for any started task.
-/
theorem graphEffects_emptyRoots_noAdopt {queue : Kernel}
    (registered : queue.StartedTasksRegistered) (covered : queue.LiveContributorsCovered)
    (empty : (queue.rootGroups.isEmpty && queue.rootStreams.isEmpty) = true)
    (event : GraphEvent) (producer : WorkQueueSemantics.Occurrence)
    : .adopt producer ∉ graphEffects queue event := by
  obtain ⟨groupsEmpty, streamsEmpty⟩ := Bool.and_eq_true_iff.mp empty
  have noHealthy : ∀ node, queue.taskNode? node.task.occurrence = some node
      → queue.taskHasHealthyOwner node.task = false := by
    intro node found
    apply Bool.eq_false_iff.mpr
    intro healthy
    obtain ⟨key, contributes, live⟩ := ReferenceWorkQueue.taskHasHealthyOwner_present healthy
    have lookup : ∃ group, queue.groupNode? key = some group := by
      cases tested : queue.groupNode? key with
      | some group => exact ⟨group, rfl⟩
      | none => exact False.elim ((queue.groupNode?_eq_none_iff key).mp tested live)
    obtain ⟨root, active, _⟩ := covered node.task
      (registered node (List.mem_of_find?_eq_some found)) key contributes lookup
    rw [List.isEmpty_iff.mp groupsEmpty] at active
    cases active
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simp [graphEffects, found]
      | some node =>
          have same := (ReferenceWorkQueue.State.taskNode?_some found).2
          have unhealthy := noHealthy node (same.symm ▸ found)
          simp [graphEffects, found, unhealthy]
  | streamItems stream items => simp [graphEffects, List.isEmpty_iff.mp streamsEmpty]
  | taskFailure | streamSuccess => simp [graphEffects]
  | streamFailure stream errors => simp [graphEffects, List.isEmpty_iff.mp streamsEmpty]

/-- A dispatch with no adoption cannot create queue ownership from a missing/foreign lease. -/
theorem ResourceState.observeDispatch_noAdopt_noOwned (resources : ResourceState)
    (inventories : ProducerInventories) (before : State) (event : GraphEvent)
    (noOwned : ∀ target, resources target ≠ .owned .queue)
    (noAdopt : ∀ producer, .adopt producer ∉ graphEffects before.queue event)
    : ∀ target,
        (resources.observeDispatch inventories before event).1 target
        ≠ .owned .queue := by
  intro target owned
  obtain ⟨adopted, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ target owned
  rcases ResourceState.observeAdoptions_queueOwned_origin _ _ _ target adopted with earlier | transferred
  · exact noOwned target (resources.observeNormalCompletion_owned_origin _ _ _ .queue earlier)
  · obtain ⟨producer, emitted, _, _⟩ := transferred
    exact noAdopt producer emitted

-----------------------------------------------------------------------------------------
-- Transfer the all-handler invariant to every accepted raw FIFO prefix
-----------------------------------------------------------------------------------------

/-- All dispatch resource observations and delta effects depend on the kernel queue only. -/
theorem ResourceState.observeDispatch_sameQueue (resources : ResourceState)
    (inventories : ProducerInventories) (before after : State) (event : GraphEvent)
    (same : before.queue = after.queue)
    (sameStopped : before.stopped = after.stopped)
    : resources.observeDispatch inventories before event
      = resources.observeDispatch inventories after event := by
  cases before
  cases after
  cases same
  cases sameStopped
  rfl

/-- An actual raw FIFO input preserves pending task/source records under the original
source and executable-start premises. Open prefixes reuse the normalized witnesses; empty
prefixes have no owned lease and cannot adopt, all derived from generated record topology.
-/
theorem generatedRaw_resourceInvariant {work events event resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (events ++ [event]))
    (accepted : (initial work).acceptsBatch (events ++ [event]) = true)
    (represented
      : QueueResourcesRepresented ((initial work).replayGraphEvents events)
          (ReferenceWorkQueue.GraphEvent.taskSettlements events) resources)
    (taskIdentity
      : ProducerTasksMatchWork work resources inventories
          (graphEffects ((initial work).replayGraphEvents events) event))
    (sourceIdentity
      : ProducerSourcesMatchWork work resources inventories
          (graphEffects ((initial work).replayGraphEvents events) event))
    : QueueResourcesRepresented
        (((initial work).replayGraphEvents events).handleGraphEvent event).1
        (event.recordTaskOutcome (ReferenceWorkQueue.GraphEvent.taskSettlements events))
        (resources.observeDispatch inventories
          { queue := (initial work).replayGraphEvents events } event).1 := by
  let queue := (initial work).replayGraphEvents events
  by_cases empty : (queue.rootGroups.isEmpty && queue.rootStreams.isEmpty) = true
  · obtain ⟨prior, _, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
    have earlier := ReferenceWorkQueue.State.acceptsBatch_prefix accepted
    have ledger := (ReferenceWorkQueue.createWorkQueue_pendingAccounting work).replayGraphEvents
      (before := []) generated events prior earlier
    have covered := generated.replayGraphEvents_liveContributorsCovered events prior earlier
    have owners := generated.replayGraphEvents_bufferedOwnersPresent events prior earlier
    have noOwned := represented.emptyRoots_no_owned ledger.sound ledger.started covered owners empty
    have after := resources.observeDispatch_noAdopt_noOwned inventories { queue } event noOwned
      (graphEffects_emptyRoots_noAdopt ledger.started covered empty event)
    exact ⟨fun occurrence owned => False.elim (after _ owned), fun key owned => False.elim (after _ owned)⟩
  · have exactState := rawPrefix_state work events generated
      (valid.prefix ⟨[event], rfl⟩) (ReferenceWorkQueue.State.acceptsBatch_prefix accepted) empty
    have started := rawPrefix_startedNext accepted empty
    have result := GeneratedDispatchResourcesRepresented_holds work (rawPrefixBatches events) event
      generated (by simpa only [rawPrefix_flatten] using valid) started resources inventories
    rw [exactState, rawPrefix_flatten] at result
    have endpoint : (({ state := { queue := (initial work).replayGraphEvents events } }
        : GraphBatchResult).handleGraphEvent event).state.queue
        = (((initial work).replayGraphEvents events).handleGraphEvent event).1 :=
      congrArg Prod.fst (referencePrefix_handleGraphEvent generated events event valid
        (ReferenceWorkQueue.State.acceptsBatch_prefix accepted))
    dsimp only at result
    rw [endpoint] at result
    exact result represented taskIdentity sourceIdentity

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
