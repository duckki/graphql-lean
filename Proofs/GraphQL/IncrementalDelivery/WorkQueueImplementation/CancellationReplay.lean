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
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (source : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.CancelledRecordsSupported work
        (queue.objectFailureContribution event ++ failed) := by
  have included : failed.Subset (queue.objectFailureContribution event ++ failed) :=
    List.subset_append_right _ _
  apply (supported.weaken included).handleGraphEvent (cached.weaken included) registered
    tasksMatch matching links canonical event source
  intro occurrence errors same node found accepted
  subst event
  simp [State.objectFailureContribution, found, accepted]

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
  | taskFailure occurrence errors =>
      cases found : queue.taskNode? occurrence with
      | none =>
          simpa [State.handleGraphEvent, State.taskFailure, State.objectFailureContribution,
            found] using supported
      | some node =>
          cases accepted : queue.taskHasHealthyOwner node.task with
          | false =>
              simpa [State.handleGraphEvent, State.taskFailure, State.objectFailureContribution,
                found, accepted] using supported.removeTask occurrence
          | true =>
              have enlarged := supported.weaken
                (List.subset_append_right [occurrence] failed)
              simpa [State.handleGraphEvent, State.objectFailureContribution, found,
                accepted]
                using enlarged.taskFailure registered matching occurrence errors (by simp)

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
      have tail := ih (supported.handleGraphEvent_contribution registered matching event)
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
      have next := supported.handleGraphEvent_contribution cached registered tasksMatch
        matching links canonical event source
      have nextCached := cached.handleGraphEvent_contribution registered tasksMatch event
      have tail := ih next nextCached (registered.handleGraphEvent event)
        (tasksMatch.handleGraphEvent event source) (matching.handleGraphEvent event source)
        (links.handleGraphEvent event source canonical)
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
      (fun _ member => workFromSpec_groups_parentCanonical
        (Located.root (root := work)) canonical member))
    canonical events (fun _ member => valid.eachMatches member)
  simpa only [List.append_nil] using result

-----------------------------------------------------------------------------------------
-- Batch normalization changes only the termination flag, not cancellation evidence
-----------------------------------------------------------------------------------------

/-- Actual normalized replay retains support from exactly its accepted object failures.
Witness: the existing start-discipline theorem equates batch execution with sequential
replay up to the termination flag; that flag is irrelevant to cancellation provenance. -/
theorem ExecutedWork.runNormalized_cancelledRecordsSupported {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.CancelledRecordsSupported
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten) := by
  have supported := generated.replayGraphEvents_cancelledRecordsSupported batches.flatten valid
  obtain ⟨terminal, same⟩ := (State.initialize (Work.fromExecution work)).runNormalized_stateCore
    batches (by rwa [inputsStarted_eq_batchesStarted] at started)
  rw [same]
  exact supported

/-- A causally healthy actual contributor is never recorded as cancelled by replay.
Witness: record cancellation support and generated contributor equivalence exclude it.
-/
theorem ExecutedWork.runNormalized_healthy_not_cancelled {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {ref : NodeRef}
    (contributor : ∃ dependencies, NodeHasDependencies work ref .group dependencies)
    (healthy
      : ¬GroupInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions
            batches.flatten) ref)
    : ref
      ∉ ((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.cancelledGroups := by
  obtain ⟨dependencies, source, producer, known, same⟩ := contributor
  have supported := generated.runNormalized_cancelledRecordsSupported batches valid started
  exact same ▸ supported.contributor_healthy_not_mem generated known (same.symm ▸ healthy)

/-- Real normalized replay supports caches using accepted failures, not ignored inputs.
Witness: sequential cache provenance and the batch replay's termination-only state change.
-/
theorem createWorkQueue_runNormalized_cachedFailuresSupported_contributions
    {work : Execution.Work} (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.CachedFailuresSupported
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten) := by
  have initial := createWorkQueue_cachedFailuresSupported (Work.fromExecution work) work []
  have supported := initial.replayGraphEvents_contributions
      (createWorkQueue_startedTasksRegistered _)
      (createWorkQueue_fromSpec_registeredTasksMatch _) batches.flatten
      (fun _ member => valid.eachMatches member)
  obtain ⟨terminal, same⟩ := (State.initialize (Work.fromExecution work)).runNormalized_stateCore
    batches (by rwa [inputsStarted_eq_batchesStarted] at started)
  rw [same]
  simpa only [List.append_nil, State.CachedFailuresSupported] using supported

/-- A live causally healthy actual contributor passes the replay's executable guard.
Witness: replay derives cancellation and cache provenance, canonical parents, and fixed
descriptors; the finite-walk completeness theorem then needs no extra queue invariant.
This is guard completeness, not yet the converse guard-soundness theorem. -/
theorem ExecutedWork.runNormalized_groupIsHealthy_of_uninvalidated
    {work : Execution.Work} (generated : ExecutedWork work)
    (batches : List (List GraphEvent)) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {ref : NodeRef} {node : GroupNode}
    (contributor : ∃ dependencies, NodeHasDependencies work ref .group dependencies)
    (found
      : ((State.initialize (Work.fromExecution work)).runNormalized batches).1.groupNode?
          ref
        = some node)
    (healthy
      : ¬GroupInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions
            batches.flatten) ref)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.groupIsHealthy
        ref
      = true := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have parentMetadata :=
    (createWorkQueue_groupParentsCanonical (Work.fromExecution work) parents
      (fun _ member => workFromSpec_groups_parentCanonical
        (Located.root (root := work)) canonical member)).runNormalized batches
      (fun batch batchMember event member =>
        valid.eachMatches (List.mem_flatten.mpr ⟨batch, batchMember, member⟩)) canonical
  apply (createWorkQueue_runNormalized_cachedFailuresSupported_contributions batches valid
    started).groupIsHealthy (generated.runNormalized_cancelledRecordsSupported batches valid
      started) generated ?_ contributor found healthy
  intro live member
  obtain ⟨dependencies, known⟩ := valid.runNormalized_groupNodesMatchWork live member
  refine ⟨dependencies, known, ?_⟩
  rw [canonical live.group.node dependencies known]
  exact parentMetadata live member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
