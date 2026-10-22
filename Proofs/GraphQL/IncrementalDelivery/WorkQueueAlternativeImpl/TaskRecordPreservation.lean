import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.UnsettledTaskProgress

/-! Existing unfinished computation leases retain real records or receive an actual abort.
The domain uses the same observed task-completion history, not completed buffer contents.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Accepted registration retains old descriptors and unfinished live owners
-----------------------------------------------------------------------------------------

/-- Registration only appends permanent task descriptors, across all input kinds. -/
theorem registrationSnapshot_oldTasks (queue : Kernel) (event : GraphEvent)
    : queue.tasks.Subset (registrationSnapshot queue event).tasks := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none =>
          simpa only [registrationSnapshot, found]
            using (show queue.tasks.Subset queue.tasks from fun _ member => member)
      | some node =>
          simp only [registrationSnapshot, found,
            State.maybeIntegrateWork_tasks, ReferenceWorkQueue.State.putTaskNode]
          exact fun _ member => List.mem_append_left _ member
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [registrationSnapshot, active, Bool.false_eq_true,
            ↓reduceIte] using (show queue.tasks.Subset queue.tasks from fun _ member => member)
      | true =>
          rw [registrationSnapshot_itemFold queue stream items active, streamRegistrationFold_tasks]
          exact List.subset_append_left _ _
  | taskFailure | streamSuccess | streamFailure => exact fun _ member => member

/-- An old unsettled task blocks item empty-shell pruning even without a task node.
The exact registration fold carries the original link/registry invariants and one owner key.
-/
theorem registrationSnapshot_unsettledOwner {queue : Kernel} {work settled task key}
    (accounted : queue.PendingAccounting work settled) (registered : task ∈ queue.tasks)
    (pending : task.occurrence ∉ settled)
    (contributes : key ∈ task.groups.map DeliveryNode.ref)
    (present : key ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    (event : GraphEvent) (matching : event.MatchesWork work)
    : key
      ∈ (registrationSnapshot queue event).groupNodes.map
          (fun node => node.group.node.ref) := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [registrationSnapshot, found] using present
      | some node =>
          simp only [registrationSnapshot, found]
          exact State.maybeIntegrateWork_includesRefs _ result.work
            (some occurrence) present
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false => simpa only [registrationSnapshot, active, Bool.false_eq_true,
          ↓reduceIte] using present
      | true =>
          rw [registrationSnapshot_itemFold queue stream items active]
          exact streamRegistrationFold_ownerPresent items ({ queue }, [], [], [], [], [])
            ⟨accounted.refs, accounted.liveGroups, accounted.taskGroups, accounted.links⟩
            registered pending contributes present
            (fun item member => matching.streamItem_childTasksCovered member)
  | taskFailure | streamSuccess | streamFailure => exact present

-----------------------------------------------------------------------------------------
-- Existing pending records progress across every generated handler
-----------------------------------------------------------------------------------------

/-- A pre-handler task membership still unsettled after this input is represented at the
actual endpoint or aborted there. Completion history excludes legitimately removed buffers.
-/
def GeneratedRepresentedUnsettledTaskProgress : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ occurrence,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        RecordTargetRepresented before.queue (.task occurrence)
        → occurrence
          ∉ event.recordTaskOutcome
              (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten)
        → RecordTargetRepresented reduced.state.queue (.task occurrence)
          ∨ .abortTask occurrence ∈ reduced.effects

/-- Membership soundness identifies the old descriptor; exact registration retains its
owner; the all-handler prepared-task theorem constructs the endpoint or abort alternative.
-/
theorem GeneratedRepresentedUnsettledTaskProgress_holds
    : GeneratedRepresentedUnsettledTaskProgress := by
  intro work inputs event generated valid started occurrence
  dsimp only
  intro represented pending
  let before := ((State.initialize work).runNormalized inputs).1
  have accounted := generatedReplay_nextAccounting generated valid started
  obtain ⟨_, matching, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  cases represented with
  | @task key occurrence group found linked _unrejected =>
      obtain ⟨task, member, same, contributes⟩ := accounted.sound group
        (List.mem_of_find?_eq_some found) occurrence linked
      have unsettled
          : task.occurrence
            ∉ ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten := by
        intro settled
        apply pending
        rw [← same]
        cases event with
        | taskSuccess | taskFailure => exact List.mem_cons_of_mem _ settled
        | streamItems | streamSuccess | streamFailure => exact settled
      have present := registrationSnapshot_unsettledOwner accounted member unsettled contributes
        (List.mem_map_of_mem (List.mem_of_find?_eq_some found)) event matching
      obtain ⟨owner, ownerMember, ownerKey⟩ := List.mem_map.mp contributes
      have owned : ∃ owner ∈ task.groups, ∃ node,
          (registrationSnapshot before.queue event).groupNode? owner.ref = some node := by
        refine ⟨owner, ownerMember, ?_⟩
        cases lookup : (registrationSnapshot before.queue event).groupNode? owner.ref with
        | some node => exact ⟨node, rfl⟩
        | none =>
            exact False.elim ((ReferenceWorkQueue.State.groupNode?_eq_none_iff _ _).mp lookup
              (ownerKey.symm ▸ present))
      exact same
      ▸ GeneratedPreparedUnsettledTaskProgress_holds work inputs event generated valid
          started task (registrationSnapshot_oldTasks _ _ member) (same.symm ▸ pending)
          owned

-----------------------------------------------------------------------------------------
-- The independent resource observer keeps the same pending completion history
-----------------------------------------------------------------------------------------

/-- Queue-owned computation leases have a current membership and no processed task outcome.
This is a before-state/history invariant, not an endpoint or cleanup-effect assumption.
-/
def TasksPendingRepresented (queue : Kernel) (settled : List Occurrence)
    (resources : ResourceState)
    : Prop :=
  ∀ occurrence,
    resources (.task occurrence) = .owned .queue
    → RecordTargetRepresented queue (.task occurrence) ∧ occurrence ∉ settled

/-- An existing queue lease still owned after dispatch survived normal completion.
Adoption cannot reacquire it under another producer or resurrect a released lease.
-/
theorem ResourceState.observeDispatch_existingQueueOwned_survivesCompletion
    (resources : ResourceState) (inventories : ProducerInventories) (before : State)
    (event : GraphEvent) (target : CleanupTarget)
    (initial : resources target = .owned .queue)
    (owned
      : (resources.observeDispatch inventories before event).1 target = .owned .queue)
    : (resources.observeNormalCompletion before.queue event).1 target
      = .owned .queue := by
  obtain ⟨adopted, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ target owned
  rcases ResourceState.observeAdoptions_queueOwned_origin _ _ _ target adopted with earlier | transferred
  · exact earlier
  · obtain ⟨producer, _, _, lease⟩ := transferred
    have original := resources.observeNormalCompletion_owned_origin _ _ target (.producer producer) lease
    rw [initial] at original
    cases original

/-- A task still owned after normal completion cannot be this input's settled identity.
Together with prior unsettledness this updates the same history invariant for all inputs.
-/
theorem ResourceState.observeNormalCompletion_taskUnsettled (resources : ResourceState)
    (before : Kernel) (event : GraphEvent) (occurrence : Occurrence)
    (settled : List Occurrence) (pending : occurrence ∉ settled)
    (owned
      : (resources.observeNormalCompletion before event).1 (.task occurrence)
        = .owned .queue)
    : occurrence ∉ event.recordTaskOutcome settled := by
  cases event with
  | taskSuccess incoming result =>
      intro member
      rcases List.mem_cons.mp member with same | earlier
      · subst incoming
        exact resources.finishQueueTarget_not_owned (.task occurrence) owned
      · exact pending earlier
  | taskFailure failed errors =>
      intro member
      rcases List.mem_cons.mp member with same | earlier
      · subst failed
        exact resources.finishQueueTarget_not_owned (.task occurrence) owned
      · exact pending earlier
  | streamItems | streamSuccess | streamFailure => exact pending

/-- Still-owned existing pending leases retain records; completion/cancellation alternatives
are excluded by the actual observer, not assumed as successful ownership preservation.
-/
def GeneratedDispatchExistingTaskRepresentation : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories) occurrence,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        RecordTargetRepresented before.queue (.task occurrence)
        → occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten
        → resources (.task occurrence) = .owned .queue
        → (resources.observeDispatch inventories before event).1 (.task occurrence)
          = .owned .queue
        → RecordTargetRepresented reduced.state.queue (.task occurrence)

/-- Generated old-record progress and licensed completion/cleanup compose at one dispatch. -/
theorem GeneratedDispatchExistingTaskRepresentation_holds
    : GeneratedDispatchExistingTaskRepresentation := by
  intro work inputs event generated valid started resources inventories occurrence
  dsimp only
  intro represented pending initial owned
  let before := ((State.initialize work).runNormalized inputs).1
  have completed := resources.observeDispatch_existingQueueOwned_survivesCompletion inventories before event
    (.task occurrence) initial owned
  have unfinished := resources.observeNormalCompletion_taskUnsettled before.queue event occurrence _ pending completed
  rcases GeneratedRepresentedUnsettledTaskProgress_holds work inputs event generated valid started
      occurrence represented unfinished with kept | aborted
  · exact kept
  · obtain ⟨_, absent⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.task occurrence) owned
    exact False.elim (absent (List.mem_filterMap.mpr ⟨.abortTask occurrence, aborted, rfl⟩))

-----------------------------------------------------------------------------------------
-- Construct the dispatch-wide task invariant for old and newly adopted leases
-----------------------------------------------------------------------------------------

/-- Every still-owned task has a real endpoint membership and remains unsettled in the
same input history. Native identity mapping covers incoming leases, not desired coverage.
-/
def GeneratedDispatchTasksPendingRepresented : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories),
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        TasksPendingRepresented before.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) resources
        → ProducerTasksMatchWork work resources inventories
            (graphEffects before.queue event)
        → TasksPendingRepresented reduced.state.queue
            (event.recordTaskOutcome
              (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten))
            (resources.observeDispatch inventories before event).1

/-- Inspect actual ownership origin once, then use old-record or structural incoming-task
construction. This preserves the genuine completion-history invariant without a new law.
-/
theorem GeneratedDispatchTasksPendingRepresented_holds
    : GeneratedDispatchTasksPendingRepresented := by
  intro work inputs event generated valid started resources inventories
  dsimp only
  intro beforeInvariant identities occurrence owned
  let before := ((State.initialize work).runNormalized inputs).1
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨adopted, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.task occurrence) owned
  rcases ResourceState.observeAdoptions_queueOwned_origin _ _ _ (.task occurrence) adopted with earlier | transferred
  · have original := resources.observeNormalCompletion_owned_origin _ _ (.task occurrence) .queue earlier
    obtain ⟨represented, pending⟩ := beforeInvariant occurrence original
    exact ⟨GeneratedDispatchExistingTaskRepresentation_holds work inputs event generated valid started
      resources inventories occurrence represented pending original owned,
      resources.observeNormalCompletion_taskUnsettled before.queue event occurrence _ pending earlier⟩
  · obtain ⟨producer, emitted, listed, acquired⟩ := transferred
    have original := resources.observeNormalCompletion_owned_origin _ _ (.task occurrence) (.producer producer) acquired
    have represented := GeneratedDispatchIncomingTaskRepresentation_holds work inputs event generated valid started
      resources inventories identities producer occurrence emitted listed original owned
    obtain ⟨address, owners, payload, same, known⟩ := identities producer occurrence emitted listed original
    obtain ⟨task, returned, identity⟩ := adoptedTask_returned matching emitted (same ▸ known)
    have childFresh := acceptedChildTask_unsettled matching prior fresh returned
    have unfinished := acceptedChildTask_not_recorded matching returned
      (fun member => childFresh (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities _ member))
    exact ⟨represented, same.symm ▸ identity ▸ unfinished⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
