import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IncomingTaskProgress

/-! Generated handlers preserve or abort an owned prepared task genuinely
unsettled in the actual input history. Completed buffered tasks are outside this domain;
no stronger source law or desired endpoint/resource condition is assumed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Registration and the endpoint have the same permanent task descriptors
-----------------------------------------------------------------------------------------

/-- Settlement, release and draining change memberships, not the prepared task catalogue. -/
theorem handleGraphEvent_tasks_eq_snapshot (queue : Kernel) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.tasks
      = (registrationSnapshot queue event).tasks := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none =>
          simp only [ReferenceWorkQueue.State.handleGraphEvent,
            ReferenceWorkQueue.State.cacheTaskFailures,
            List.foldl_nil,
              ReferenceWorkQueue.State.taskSuccess, registrationSnapshot, found]
      | some node =>
          rw [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil,
            ReferenceWorkQueue.State.taskSuccess_tasks found]
          simp only [registrationSnapshot, found,
            State.maybeIntegrateWork_tasks, ReferenceWorkQueue.State.putTaskNode]
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simp only [ReferenceWorkQueue.State.handleGraphEvent,
            ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil,
            ReferenceWorkQueue.State.streamItems, registrationSnapshot, active, Bool.not_false,
            Bool.false_eq_true, ↓reduceIte]
      | true =>
          rw [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, queue.streamItems_tasks stream items active,
            registrationSnapshot_itemFold queue stream items active, streamRegistrationFold_tasks]
  | taskFailure occurrence errors => exact queue.taskFailure_tasks occurrence errors
  | groupFailure failure =>
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
        registrationSnapshot, ReferenceWorkQueue.State.groupFailure]
      split
      · rfl
      · split <;> rfl
  | streamSuccess stream =>
      cases active : queue.rootStreams.contains stream.ref <;>
        simp only [ReferenceWorkQueue.State.handleGraphEvent,
          ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
          ReferenceWorkQueue.State.streamSuccess, active, Bool.false_eq_true, ↓reduceIte,
          registrationSnapshot]
  | streamFailure stream errors =>
      cases active : queue.rootStreams.contains stream.ref <;>
        simp only [ReferenceWorkQueue.State.handleGraphEvent,
          ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
          ReferenceWorkQueue.State.streamFailure, active, Bool.false_eq_true, ↓reduceIte,
          registrationSnapshot]

-----------------------------------------------------------------------------------------
-- Genuine unsettledness excludes successful transfer for every handler
-----------------------------------------------------------------------------------------

/-- No contributor of a prepared task unsettled after this input has published.
The settlement predicate uses the same source prefix/event as the actual handler.
-/
theorem generatedUnsettledTask_unpublished {work inputs event task}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    (registered
      : task
        ∈ (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
            event).tasks)
    (pending
      : task.occurrence
        ∉ event.recordTaskOutcome
            (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten))
    : ∀ key ∈ task.groups.map DeliveryNode.ref,
        key
        ∉ publicationRoots
            ((((State.initialize work).runNormalized inputs).1.queue).handleGraphEvent
              event).2.1 := by
  intro key contributes published
  let before := ((State.initialize work).runNormalized inputs).1.queue
  have ordinary : ∀ failure, event ≠ .groupFailure failure := by
    intro failure same
    subst event
    simp only [ReferenceWorkQueue.State.handleGraphEvent,
      ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
      ReferenceWorkQueue.State.groupFailure] at published
    split at published
    · cases published
    · split at published <;> simp [publicationRoots] at published
  have accounted := generatedReplay_nextAccounting generated valid started
  have closures := ReferenceWorkQueue.State.handleGraphEvent_removalAccounting
    accounted.liveGroups event [] ordinary
  have projection := generatedSnapshot_projection generated valid
    (generatedReplay_beforeNext generated valid started).2.1
  have live := registrationSnapshot_publicationRoots_live before event projection published
  rcases GeneratedUnsettledTaskOwnerProgress_holds work inputs event generated valid started
    task registered pending
      key contributes live with retained | cut
  · have absent := (closures.closed key (by
      obtain ⟨group, groups, streams, emitted, same⟩ := mem_publicationRoots.mp published
      exact List.mem_flatMap.mpr ⟨_, List.mem_append_left _ emitted, same ▸
        List.mem_cons_self⟩)).lookup_none
    exact (ReferenceWorkQueue.State.groupNode?_eq_none_iff _ _).mp absent retained
  · obtain ⟨_, _, path⟩ := cut
    obtain ⟨_, found⟩ := liveDescendant_targetFound path
    exact failurePruningView_live_unpublished found published

-----------------------------------------------------------------------------------------
-- Prepared task classification with explicit same-run unsettledness
-----------------------------------------------------------------------------------------

/-- All-handler prepared-task classification. A concrete initial owner and unsettled
input-history identity define its domain, not desired cleanup or endpoint coverage.
-/
def GeneratedPreparedUnsettledTaskProgress : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (task : Task),
        let before := ((State.initialize work).runNormalized inputs).1
        let snapshot := registrationSnapshot before.queue event
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        task ∈ snapshot.tasks
        → task.occurrence
          ∉ event.recordTaskOutcome
              (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten)
        → (∃ owner ∈ task.groups, ∃ group, snapshot.groupNode? owner.ref = some group)
        → RecordTargetRepresented reduced.state.queue (.task task.occurrence)
          ∨ .abortTask task.occurrence ∈ reduced.effects

/-- The original pending/decrement proofs also cover internal notification dispatch. -/
theorem GeneratedPreparedUnsettledTaskProgress_holds
    : GeneratedPreparedUnsettledTaskProgress := by
  intro work inputs event generated valid started task
  dsimp only
  intro registered pending owned
  exact generatedPreparedTask_progress generated valid started registered pending owned

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
