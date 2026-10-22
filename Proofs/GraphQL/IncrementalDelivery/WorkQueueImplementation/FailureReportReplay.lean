import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulGroupReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay

/-! Actual report origins survive every matched host event and finite raw replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Matched generated failures carry strictly positive error counts
-----------------------------------------------------------------------------------------

/-- A matched failed-task input has a positive generated error count.
Witness: structural source matching identifies the precomputed failing payload; root
execution's positive-failure certificate supplies its count.
-/
theorem ExecutedWork.matchedTaskFailure_positive {work occurrence errors}
    (generated : ExecutedWork work)
    (matching : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : 0 < errors := by
  obtain ⟨owners, producer, path, known⟩ := matching
  exact generated.taskFailure_positive known rfl

/-- Positive failed settlement preserves strictly positive retained failure caches.
Witness: each latent cache adds a positive count, while immediate failure cleanup only
filters existing nodes. No uniqueness or output-admission premise is required.
-/
theorem State.CachedErrorsSatisfy.taskFailure_positive {queue : State}
    (cached : queue.CachedErrorsSatisfy (fun _ errors => 0 < errors))
    (occurrence : Occurrence) (errors : Nat) (positive : 0 < errors)
    : (queue.taskFailure occurrence errors).1.CachedErrorsSatisfy
        (fun _ count => 0 < count) := by
  exact cached.taskFailure occurrence errors (by intros; exact positive)

/-- Every matched event retains strictly positive error caches on generated work.
Witness: failures add their positive generated count; all other handlers preserve caches.
-/
theorem State.CachedErrorsSatisfy.handleGraphEvent_positive {queue : State} {work}
    (cached : queue.CachedErrorsSatisfy (fun _ errors => 0 < errors))
    (generated : ExecutedWork work) (event : GraphEvent)
    (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.CachedErrorsSatisfy
        (fun _ errors => 0 < errors) := by
  cases event with
  | taskSuccess occurrence result => exact cached.taskSuccess occurrence result
  | taskFailure occurrence errors =>
      exact cached.taskFailure_positive occurrence errors
        (generated.matchedTaskFailure_positive matching)
  | streamItems stream items => exact cached.streamItems stream items
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.CachedErrorsSatisfy (fun _ errors => 0 < errors)
      unfold State.streamSuccess
      split <;> exact cached
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.CachedErrorsSatisfy
        (fun _ errors => 0 < errors)
      unfold State.streamFailure
      split <;> exact cached

-----------------------------------------------------------------------------------------
-- Actual accumulated outputs justify every concrete cancellation marker
-----------------------------------------------------------------------------------------

/-- Matched host-event processing preserves actual positive completion origins.
Witness: successful inputs thread output-aware release draining; failed inputs use the
generated positive count; stream closures leave the group cancellation registry unchanged.
-/
theorem State.CancelledRecordsReported.handleGraphEvent {queue : State}
    {work events parents} (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (cached : queue.CachedErrorsSatisfy (fun _ errors => 0 < errors))
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.CancelledRecordsReported work
        (events ++ (queue.handleGraphEvent event).2) := by
  cases event with
  | taskSuccess occurrence result =>
      apply reported.taskSuccess generated cached records links canonical occurrence result
      intro group member
      obtain ⟨dependencies, known⟩ := matching.taskChildGroups_recordAt member
      refine ⟨dependencies, known, ?_⟩
      rw [canonical group.node dependencies known]
      exact matching.taskChildGroups_parentCanonical canonical member
  | taskFailure occurrence errors =>
      exact reported.taskFailure generated records links canonical occurrence errors
        (generated.matchedTaskFailure_positive matching)
  | streamItems stream items =>
      apply reported.streamItems generated cached records links canonical stream items
      intro item itemMember group member
      obtain ⟨dependencies, known⟩ :=
        matching.streamItem_childGroups_recordAt itemMember member
      refine ⟨dependencies, known, ?_⟩
      rw [canonical group.node dependencies known]
      exact matching.streamItem_childGroups_parentCanonical canonical itemMember member
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.CancelledRecordsReported work
        (events ++ (queue.streamSuccess stream).2)
      unfold State.streamSuccess
      split <;> exact reported.append _
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.CancelledRecordsReported work
        (events ++ (queue.streamFailure stream errors).2)
      unfold State.streamFailure
      split <;> exact reported.append _

/-- Finite matched raw replay retains actual report origins for every cancellation marker.
Witness: induction threads emitted outputs together with positive caches and canonical
metadata. The conclusion does not assume output admission or terminal reporting.
-/
theorem State.CancelledRecordsReported.rawEventReplay {queue : State}
    {work events parents} (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (cached : queue.CachedErrorsSatisfy (fun _ errors => 0 < errors))
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (inputs : List GraphEvent) (matching : ∀ event ∈ inputs, event.MatchesWork work)
    : (queue.rawEventReplay inputs).1.CancelledRecordsReported work
        (events ++ (queue.rawEventReplay inputs).2) := by
  induction inputs generalizing queue events with
  | nil => simpa [State.rawEventReplay] using reported
  | cons event rest ih =>
      have source := matching event List.mem_cons_self
      rw [State.rawEventReplay_cons]
      have next := ih (reported.handleGraphEvent generated cached records links canonical
        event source) (cached.handleGraphEvent_positive generated event source)
        (records.handleGraphEvent event source)
        (links.handleGraphEvent event source canonical)
        (fun later member => matching later (List.mem_cons_of_mem _ member))
      simpa only [List.append_assoc] using next

/-- Generated initial replay derives cancellation report provenance from scratch.
Witness: empty initial markers and caches, generated parent records, and matched replay.
No executable-start, terminal, or output-history premise is needed.
-/
theorem ExecutedWork.rawEventReplay_cancelledRecordsReported {work : Execution.Work}
    (generated : ExecutedWork work) (inputs : List GraphEvent)
    (matching : ∀ event ∈ inputs, event.MatchesWork work)
    : let queue := State.initialize (Work.fromExecution work)
      (queue.rawEventReplay inputs).1.CancelledRecordsReported work
        (queue.rawEventReplay inputs).2 := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial := createWorkQueue_cancelledRecordsReported (Work.fromExecution work) work []
  simpa only [List.nil_append] using initial.rawEventReplay generated
    (createWorkQueue_cachedErrors _ _)
    (createWorkQueue_groupNodesMatchWork work)
    (createWorkQueue_childLinksCanonical _ parents
      (fun _ member => workFromSpec_groups_parentCanonical (Located.root (root := work))
        canonical member)) canonical inputs matching

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
