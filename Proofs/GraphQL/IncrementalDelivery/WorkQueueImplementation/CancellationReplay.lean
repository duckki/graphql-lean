import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupParents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyEligibility

/-! Cancellation provenance from the failures accepted by actual source replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The actual guard supplies exactly the new failure cause, including silent acceptance
-----------------------------------------------------------------------------------------

/-- One graph event adds only its guard-selected failure to cancellation provenance.
Witness: the handler theorem uses the recorded token only in the accepted branch.
No token is required for ignored failures; source inputs themselves are never filtered. -/
theorem State.CancelledRecordsSupported.handleGraphEvent_contribution
    {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (sound : queue.GroupMembershipSound)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (source : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.CancelledRecordsSupported work
        (queue.objectFailureContribution event ++ failed) := by
  have included : failed.Subset (queue.objectFailureContribution event ++ failed) :=
    List.subset_append_right _ _
  apply (supported.weaken included).handleGraphEvent (cached.weaken included) registered
    tasksMatch matching links sound canonical event source
  intro occurrence errors same node found
  subst event
  simp [State.objectFailureContribution, found]

/-- Retained error caches are supported by precisely the same accepted-failure inventory.
Witness: ignored task failures only remove memberships; accepted failures supply their
token to the existing cache-provenance theorem. Other handlers add no failure cache. -/
theorem State.CachedFailuresSupported.handleGraphEvent_contribution {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.CachedFailuresSupported work
        (queue.objectFailureContribution event ++ failed) := by
  cases event with
  | taskSuccess occurrence result => exact supported.taskSuccess occurrence result
  | streamItems stream items => exact supported.streamItems stream items
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.CachedFailuresSupported work failed
      unfold State.streamSuccess
      split <;> exact supported
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.CachedFailuresSupported work failed
      unfold State.streamFailure
      split <;> exact supported
  | groupFailure failure =>
      change (queue.groupFailure failure).1.CachedFailuresSupported work failed
      unfold State.groupFailure
      split
      · exact supported
      · split <;> exact supported
  | taskFailure occurrence errors =>
      cases found : queue.taskNode? occurrence with
      | none =>
          simpa [State.handleGraphEvent, State.taskFailure, State.objectFailureContribution,
            State.cacheTaskFailures,
            found] using supported
      | some node =>
          have enlarged := supported.weaken (List.subset_append_right [occurrence] failed)
          simpa [State.handleGraphEvent, State.objectFailureContribution,
            State.cacheTaskFailures, found]
            using enlarged.taskFailure registered matching occurrence errors (by simp)

/-- Enqueue effects preserve the cancellation support established by the handler. -/
theorem State.CancelledRecordsSupported.dispatchGraphEvent_contribution
    {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (sound : queue.GroupMembershipSound)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (source : event.MatchesWork work)
    : (queue.dispatchGraphEvent event).1.CancelledRecordsSupported work
        (queue.objectFailureContribution event ++ failed) := by
  exact supported.handleGraphEvent_contribution cached registered tasksMatch matching
    links sound canonical event source

/-- Enqueue effects preserve task-local rejection provenance. -/
theorem State.CachedFailuresSupported.dispatchGraphEvent_contribution {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    : (queue.dispatchGraphEvent event).1.CachedFailuresSupported work
        (queue.objectFailureContribution event ++ failed) := by
  exact supported.handleGraphEvent_contribution registered matching event

-----------------------------------------------------------------------------------------
-- Sequential replay preserves support and all metadata used by the handler proof
-----------------------------------------------------------------------------------------

/-- Sequential replay attributes every cached failure to its accepted source inventory.
Witness: cache support and registered-task provenance advance together at each input. -/
theorem State.CachedFailuresSupported.replayGraphEvents_contributions {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (events : List GraphEvent) (sources : ∀ event ∈ events, event.MatchesWork work)
    : (queue.replayGraphEvents events).CachedFailuresSupported work
        (queue.objectFailureContributions events ++ failed) := by
  induction events generalizing queue failed with
  | nil =>
      simpa [State.replayGraphEvents, State.objectFailureContributions] using supported
  | cons event rest ih =>
      have tail := ih (supported.dispatchGraphEvent_contribution registered matching event)
        (registered.handleGraphEvent event)
        (matching.handleGraphEvent event (sources event List.mem_cons_self))
        (fun event member => sources event (List.mem_cons_of_mem _ member))
      simpa [State.replayGraphEvents, State.objectFailureContributions, List.append_assoc]
        using tail

/-- Every cancellation after sequential replay has a cause in its accepted failure ledger.
Witness: joint induction carries cancellation support, cache provenance, task registration,
and canonical group metadata through the actual, unfiltered sequence of source events. -/
theorem State.CancelledRecordsSupported.replayGraphEvents {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (sound : queue.GroupMembershipSound)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (sources : ∀ event ∈ events, event.MatchesWork work)
    : (queue.replayGraphEvents events).CancelledRecordsSupported work
        (queue.objectFailureContributions events ++ failed) := by
  induction events generalizing queue failed with
  | nil =>
      simpa [State.replayGraphEvents, State.objectFailureContributions] using supported
  | cons event rest ih =>
      have source := sources event List.mem_cons_self
      have next := supported.dispatchGraphEvent_contribution cached registered tasksMatch
        matching links sound canonical event source
      have nextCached := cached.dispatchGraphEvent_contribution registered tasksMatch event
      have tail := ih next nextCached (registered.handleGraphEvent event)
        (tasksMatch.handleGraphEvent event source) (matching.handleGraphEvent event source)
        (links.handleGraphEvent event source canonical)
        (sound.handleGraphEvent event)
        (fun event member => sources event (List.mem_cons_of_mem _ member))
      simpa [State.replayGraphEvents, State.objectFailureContributions, List.append_assoc]
        using tail

/-- Generated-work initialization discharges every premise of cancellation replay support.
Witness: empty initial histories, structurally lowered task/group metadata, and the
generated work's canonical dependency assignment. No output admission is assumed. -/
theorem ExecutedWork.replayGraphEvents_cancelledRecordsSupported {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    : State.CancelledRecordsSupported
        ((State.initialize (Work.fromExecution work)).replayGraphEvents events) work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          events) := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial := createWorkQueue_cancelledRecordsSupported (Work.fromExecution work) work []
  have result := initial.replayGraphEvents
    (createWorkQueue_cachedFailuresSupported _ _ _) (createWorkQueue_startedTasksRegistered _)
    (createWorkQueue_fromSpec_registeredTasksMatch _) (createWorkQueue_groupNodesMatchWork _)
    (createWorkQueue_childLinksCanonical _ parents
      (fun _ member => workFromSpec_groups_parentCanonical_root canonical member))
    (createWorkQueue_groupMembershipSound _) canonical events
    (fun _ member => valid.eachMatches member)
  simpa only [List.append_nil] using result

/-- Internal batch provenance uses the complete available source-failure inventory. -/
private structure State.BatchFailureAccounting (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (failed : List Occurrence)
    : Prop where
  cancelled : queue.CancelledRecordsSupported work failed
  cached : queue.CachedFailuresSupported work failed
  registered : queue.StartedTasksRegistered
  tasks : queue.RegisteredTasksMatch work
  groups : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  sound : queue.GroupMembershipSound

private theorem State.BatchFailureAccounting.withTerminated {queue work parents failed}
    (valid : State.BatchFailureAccounting queue work parents failed) (terminal : Bool)
    : ({ queue with terminated := terminal } : State).BatchFailureAccounting work parents
        failed :=
  ⟨
    valid.cancelled,
    valid.cached,
    valid.registered,
    valid.tasks,
    valid.groups,
    valid.links,
    valid.sound
  ⟩

private theorem State.BatchFailureAccounting.handleGraphEvents {queue work parents failed}
    (valid : State.BatchFailureAccounting queue work parents failed)
    (batch : List GraphEvent) (sources : ∀ event ∈ batch, event.MatchesWork work)
    (recorded
      : ∀ occurrence errors,
          GraphEvent.taskFailure occurrence errors ∈ batch → occurrence ∈ failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.handleGraphEvents batch).1.BatchFailureAccounting work parents failed := by
  let available := GraphEvent.availableFailures batch
  have availableRecorded : ∀ occurrence errors,
      (occurrence, errors) ∈ available → occurrence ∈ failed := by
    intro occurrence errors member
    obtain ⟨event, inBatch, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact recorded _ _ inBatch
  let step (acc : State × List Execution.WorkQueueEvent) (event : GraphEvent) :=
    let (next, outputs) := acc.1.dispatchGraphEvent event available
    (next, acc.2 ++ outputs)
  have stable (current : State) (event : GraphEvent) (member : event ∈ batch)
      (prior : current.BatchFailureAccounting work parents failed)
      : (current.dispatchGraphEvent event available).1.BatchFailureAccounting
          work parents failed := by
    have source := sources event member
    have notified : ∀ occurrence errors, event = .taskFailure occurrence errors →
        (occurrence, errors) ∈ available := by
      intro occurrence errors same
      exact List.mem_filterMap.mpr ⟨event, member, by simp [same]⟩
    have handled : (current.handleGraphEvent event available).1.BatchFailureAccounting
        work parents failed := by
      refine ⟨prior.cancelled.handleGraphEvent prior.cached prior.registered prior.tasks
          prior.groups prior.links prior.sound canonical event source ?_ available availableRecorded,
        prior.cached.handleGraphEvent_available prior.registered prior.tasks event source available
          availableRecorded notified,
        prior.registered.handleGraphEvent event available,
        prior.tasks.handleGraphEvent event source available,
        prior.groups.handleGraphEvent event source available,
        prior.links.handleGraphEvent event source canonical available,
        prior.sound.handleGraphEvent event available⟩
      intro occurrence errors same node found
      exact availableRecorded _ _ (notified _ _ same)
    exact ⟨handled.cancelled, handled.cached, handled.registered, handled.tasks,
      handled.groups, handled.links, handled.sound⟩
  have fold (events : List GraphEvent) (included : events.Subset batch)
      (acc : State × List Execution.WorkQueueEvent)
      (prior : acc.1.BatchFailureAccounting work parents failed)
      : (events.foldl step acc).1.BatchFailureAccounting work parents failed := by
    induction events generalizing acc with
    | nil => exact prior
    | cons event rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (stable _ event (included List.mem_cons_self) prior)
  unfold State.handleGraphEvents
  split
  · exact valid
  · let folded := batch.foldl step (queue, [])
    have final : folded.1.BatchFailureAccounting work parents failed :=
      fold batch (List.Subset.refl _) (queue, []) valid
    cases folded with
    | mk current outputs =>
        dsimp only at final ⊢
        split
        · exact final.withTerminated true
        · exact final

/-- Actual host-batch replay attributes every cancellation to an available source failure.
Witness: batch-specific cache exposure and FIFO dispatch preserve one fixed source
inventory, together with source-matched tasks and canonical child edges. This is internal
provenance; it neither licenses causal cuts nor assumes output-history admission.
-/
theorem ExecutedWork.runNormalized_cancelledRecordsSupported {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (_started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.CancelledRecordsSupported
        work (GraphEvent.failureSettlements batches.flatten) := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  let failed := GraphEvent.failureSettlements batches.flatten
  let invariant (current : State) := current.BatchFailureAccounting work parents failed
  have initial : invariant (State.initialize (Work.fromExecution work)) :=
    ⟨createWorkQueue_cancelledRecordsSupported _ _ _, createWorkQueue_cachedFailuresSupported _ _ _,
      createWorkQueue_startedTasksRegistered _, createWorkQueue_fromSpec_registeredTasksMatch _,
      createWorkQueue_groupNodesMatchWork _, createWorkQueue_childLinksCanonical _ parents
        (fun _ member => workFromSpec_groups_parentCanonical_root canonical member), createWorkQueue_groupMembershipSound _⟩
  have batchesPreserve (more : List (List GraphEvent)) (included : more.Subset batches)
      (current : State) (prior : invariant current) : invariant (current.replayBatches more) := by
    induction more generalizing current with
    | nil => exact prior
    | cons batch rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
        apply prior.handleGraphEvents batch
          (fun event member =>
            valid.eachMatches
              (List.mem_flatten.mpr ⟨batch, included List.mem_cons_self, member⟩))
          ?_ canonical
        intro occurrence errors member
        apply List.mem_reverse.mpr
        exact List.mem_flatMap.mpr
          ⟨
            .taskFailure occurrence errors,
            List.mem_flatten.mpr ⟨batch, included List.mem_cons_self, member⟩,
            by simp [GraphEvent.groupFailures]
          ⟩
  rw [State.runNormalized_replayBatches]
  exact (batchesPreserve batches (List.Subset.refl _) _ initial).cancelled

/-- A causally healthy actual contributor is never recorded as cancelled by replay.
Witness: record cancellation support and generated contributor equivalence exclude it.
-/
theorem ExecutedWork.runNormalized_healthy_not_cancelled {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {ref : NodeRef}
    (contributor : ∃ dependencies, NodeHasDependencies work ref .group dependencies)
    (healthy : ¬GroupInvalidated work (GraphEvent.failureSettlements batches.flatten) ref)
    : ref
      ∉ ((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.cancelledGroups := by
  obtain ⟨dependencies, source, producer, known, same⟩ := contributor
  have supported := generated.runNormalized_cancelledRecordsSupported batches valid started
  exact same ▸ supported.contributor_healthy_not_mem generated known (same.symm ▸ healthy)

/-- Retained task rejections after real batch replay have available source contributors. -/
theorem createWorkQueue_runNormalized_cachedFailuresSupported_contributions
    {work : Execution.Work} (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (_started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.CachedFailuresSupported
        work (GraphEvent.failureSettlements batches.flatten) := by
  apply (createWorkQueue_cachedFailuresSupported (Work.fromExecution work) work
          (GraphEvent.failureSettlements batches.flatten)).runNormalized
    (createWorkQueue_startedTasksRegistered _)
    (createWorkQueue_fromSpec_registeredTasksMatch _) batches
    (fun _ member => valid.eachMatches member)
  intro occurrence errors member
  apply List.mem_reverse.mpr
  exact List.mem_flatMap.mpr
    ⟨.taskFailure occurrence errors, member, by simp [GraphEvent.groupFailures]⟩

/-- A healthy live group has no retained rejected computation after actual replay.
Witness: replay-derived rejection support and sound task membership, without a runtime
health guard or an additional source premise.
-/
theorem ExecutedWork.runNormalized_unrejected_of_uninvalidated
    {work : Execution.Work} (_generated : ExecutedWork work)
    (batches : List (List GraphEvent)) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {ref : NodeRef} {node : GroupNode}
    (found
      : ((State.initialize (Work.fromExecution work)).runNormalized batches).1.groupNode?
          ref
        = some node)
    (healthy : ¬GroupInvalidated work (GraphEvent.failureSettlements batches.flatten) ref)
    : ((State.initialize (Work.fromExecution work)).runNormalized batches).1.rejectedTask?
        node
      = none := by
  apply (createWorkQueue_runNormalized_cachedFailuresSupported_contributions batches valid
    started).healthy_rejectedTask_none
    (createWorkQueue_runNormalized_groupMembershipSound _ batches)
    (State.runNormalized_startedTasksRegistered (createWorkQueue_startedTasksRegistered _) batches)
    (createWorkQueue_runNormalized_registeredTasksMatch valid)
    (List.mem_of_find?_eq_some found)
  exact (State.groupNode?_ref found).symm ▸ healthy

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
