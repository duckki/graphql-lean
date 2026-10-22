import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingFailureFrames
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

/-- Every cached failure supplied by a matched batch has a positive generated count.
Witness: availableFailures contains exactly the task-failure inputs, whose precomputed
source payloads carry strictly positive errors.
-/
theorem ExecutedWork.availableFailures_positive {work : Execution.Work}
    (generated : ExecutedWork work) (inputs : List GraphEvent)
    (matching : ∀ event ∈ inputs, event.MatchesWork work)
    : ∀ occurrence errors,
        (occurrence, errors) ∈ GraphEvent.availableFailures inputs → 0 < errors := by
  intro occurrence errors member
  obtain ⟨event, included, same⟩ := List.mem_filterMap.mp member
  cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  exact generated.matchedTaskFailure_positive (matching _ included)

/-- Matched host processing preserves task-local positivity under a licensed snapshot.
Witness: computation rejection provenance is independent of contributing owners.
-/
theorem State.TaskRejectionsSatisfy.handleGraphEvent_positive {queue : State} {work}
    (cached : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (generated : ExecutedWork work) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors := by
      intro occurrence errors member; cases member)
    : (queue.handleGraphEvent event available).1.TaskRejectionsSatisfy
        (fun _ errors => 0 < errors) :=
  cached.handleGraphEvent event
    (fun _ _ same => generated.matchedTaskFailure_positive (same ▸ matching)) available
    licensed

-----------------------------------------------------------------------------------------
-- Every handler explains cancellation using both completion channels
-----------------------------------------------------------------------------------------

/-- Matched host processing retains a positive report for each cancellation marker.
Witness: cache exposure retains old explanations, and successful handlers include their
queued startup controls. Failed inputs use their exact positive generated source count.
-/
theorem State.CancelledRecordsReported.handleGraphEvent {queue : State}
    {work events parents} (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (cached : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors := by
      intro occurrence errors member; cases member)
    : (queue.handleGraphEvent event available).1.CancelledRecordsReported work
        (events
          ++ (queue.handleGraphEvent event available).2.1
          ++ (queue.handleGraphEvent event available).2.2.map
              (fun failure => .groupFailure failure.group failure.errors)) := by
  have prior := reported.of_sameCancelled (queue.cacheTaskFailures_cancelledGroups available)
  have counts := cached.cacheTaskFailures available licensed
  have known := records.cacheTaskFailures available
  have edges := links.cacheTaskFailures available
  unfold State.handleGraphEvent
  cases event with
  | taskSuccess occurrence result =>
      apply prior.taskSuccess generated counts known edges canonical occurrence result
        (available := available) (licensed := licensed)
      intro group member
      obtain ⟨dependencies, located⟩ := matching.taskChildGroups_recordAt member
      refine ⟨dependencies, located, ?_⟩
      rw [canonical group.node dependencies located]
      exact matching.taskChildGroups_parentCanonical canonical member
  | taskFailure occurrence errors =>
      simpa only [List.map_nil, List.append_nil]
        using prior.taskFailure generated known edges canonical occurrence errors
          (generated.matchedTaskFailure_positive matching)
  | streamItems stream items =>
      apply prior.streamItems generated counts known edges canonical stream items
        (available := available) (licensed := licensed)
      intro item itemMember group member
      obtain ⟨dependencies, located⟩ := matching.streamItem_childGroups_recordAt itemMember member
      refine ⟨dependencies, located, ?_⟩
      rw [canonical group.node dependencies located]
      exact matching.streamItem_childGroups_parentCanonical canonical itemMember member
  | streamSuccess stream =>
      simp only [State.streamSuccess, List.map_nil, List.append_nil]
      split <;> intro node dependencies located member <;>
        exact (prior node dependencies located member).append _
  | streamFailure stream errors =>
      simp only [State.streamFailure, List.map_nil, List.append_nil]
      split <;> intro node dependencies located member <;>
        exact (prior node dependencies located member).append _

  | groupFailure failure =>
      simp only [State.groupFailure, List.map_nil, List.append_nil]
      split
      · simpa only [List.append_nil] using prior
      · split <;> intro node dependencies located member <;>
          exact (prior node dependencies located member).append _

/-- Completion inventory represented by the actual waiting internal controls. -/
def State.pendingFailureOutputs (queue : State) : List WorkQueueEvent :=
  queue.groupFailureEvents.map (fun failure => .groupFailure failure.group failure.errors)

/-- Cancellation explanations may already be emitted or still waiting in the FIFO.
This proof inventory does not claim an unconsumed control has appeared on the wire. -/
def State.FifoCancelledRecordsReported (queue : State) (work : Execution.Work)
    (events : List WorkQueueEvent)
    : Prop :=
  queue.CancelledRecordsReported work (events ++ queue.pendingFailureOutputs)

/-- Once the pending FIFO is empty, every cancellation explanation is actual output. -/
theorem State.FifoCancelledRecordsReported.completed {queue : State} {work events}
    (reported : queue.FifoCancelledRecordsReported work events)
    (empty : queue.groupFailureEvents = [])
    : queue.CancelledRecordsReported work events := by
  simpa only [State.FifoCancelledRecordsReported, State.pendingFailureOutputs, empty,
    List.map_nil, List.append_nil]
    using reported

/-- Forwarding a queued head preserves its report in output or the remaining FIFO. -/
theorem State.groupFailure_pendingOutputs (queue : State) (failure : GroupFailureEvent)
    : queue.pendingFailureOutputs.Subset
        ((queue.groupFailure failure).2
          ++ (queue.groupFailure failure).1.pendingFailureOutputs) := by
  unfold State.groupFailure
  split
  · exact List.Subset.refl _
  · rename_i first rest head
    split
    · simp only [State.pendingFailureOutputs, head, List.map_cons]
      exact List.Subset.refl _
    · exact List.Subset.refl _

/-- Dispatch retains every cancellation explanation at its actual notification position. -/
theorem State.FifoCancelledRecordsReported.dispatchGraphEvent {queue : State}
    {work events parents} (reported : queue.FifoCancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (cached : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors := by
      intro occurrence errors member; cases member)
    : (queue.dispatchGraphEvent event available).1.FifoCancelledRecordsReported work
        (events ++ (queue.dispatchGraphEvent event available).2) := by
  by_cases control : ∃ failure, event = .groupFailure failure
  · obtain ⟨failure, rfl⟩ := control
    have prior := reported.of_sameCancelled (queue.cacheTaskFailures_cancelledGroups available)
    have inventory := (queue.cacheTaskFailures available).groupFailure_pendingOutputs failure
    have same : (queue.cacheTaskFailures available).pendingFailureOutputs = queue.pendingFailureOutputs := by
      simp only [State.pendingFailureOutputs, State.cacheTaskFailures_groupFailureEvents]
    rw [same] at inventory
    unfold State.dispatchGraphEvent State.handleGraphEvent State.enqueueGroupFailures
    dsimp only
    simp only [List.append_nil]
    change ((queue.cacheTaskFailures available).groupFailure failure).1.CancelledRecordsReported work _
    apply (prior.of_sameCancelled (by
      unfold State.groupFailure
      split
      · rfl
      · split <;> rfl)).mono
    intro output member
    rcases List.mem_append.mp member with earlier | waiting
    · exact List.mem_append_left _ (List.mem_append_left _ earlier)
    · rcases List.mem_append.mp (inventory waiting) with emitted | pending
      · exact List.mem_append_left _ (List.mem_append_right _ emitted)
      · exact List.mem_append_right _ pending
  · have current := reported.handleGraphEvent generated cached records links canonical
      event matching available licensed
    have pending := queue.handleGraphEvent_groupFailureEvents_eq event available
      (by intro failure same; exact control ⟨failure, same⟩)
    change (queue.handleGraphEvent event available).1.CancelledRecordsReported work _ at current
    apply current.mono
    intro output member
    change output ∈ events ++ (queue.dispatchGraphEvent event available).2
      ++ ((queue.handleGraphEvent event available).1.groupFailureEvents
        ++ (queue.handleGraphEvent event available).2.2).map
          (fun failure => WorkQueueEvent.groupFailure failure.group failure.errors)
    rw [pending, List.map_append]
    simp only [State.pendingFailureOutputs, List.mem_append] at member ⊢
    rcases member with ((old | waiting) | immediate) | fresh
    · exact .inl (.inl old)
    · exact .inr (.inl waiting)
    · exact .inl (.inr immediate)
    · exact .inr (.inr fresh)

/-- Fixed-snapshot replay preserves actual output and pending completion inventories. -/
theorem State.FifoCancelledRecordsReported.rawEventReplay {queue : State}
    {work events parents} (reported : queue.FifoCancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (cached : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (inputs : List GraphEvent) (matching : ∀ event ∈ inputs, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors)
    : (queue.rawEventReplay inputs available).1.FifoCancelledRecordsReported work
        (events ++ (queue.rawEventReplay inputs available).2) := by
  induction inputs generalizing queue events with
  | nil =>
      simpa only [State.rawEventReplay, List.foldl_nil, List.append_nil] using reported
  | cons event rest ih =>
      have matched := matching event List.mem_cons_self
      have current := reported.dispatchGraphEvent generated cached records links canonical
        event matched available licensed
      have nextCached : (queue.dispatchGraphEvent event available).1.TaskRejectionsSatisfy
          (fun _ errors => 0 < errors) :=
        cached.handleGraphEvent_positive generated event matched available licensed
      have nextRecords : (queue.dispatchGraphEvent event available).1.GroupNodesMatchWork work :=
        records.handleGraphEvent event matched available
      have nextLinks : (queue.dispatchGraphEvent event available).1.ChildLinksCanonical parents :=
        links.handleGraphEvent event matched canonical available
      have later := ih current nextCached nextRecords nextLinks
        (fun next member => matching next (List.mem_cons_of_mem _ member))
      simpa only [State.rawEventReplay_cons, List.append_assoc] using later

/-- Batch boundaries retain waiting explanations until their controls are consumed. -/
theorem State.FifoCancelledRecordsReported.handleGraphEvents {queue : State}
    {work events parents} (reported : queue.FifoCancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (cached : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (inputs : List GraphEvent) (matching : ∀ event ∈ inputs, event.MatchesWork work)
    : (queue.handleGraphEvents inputs).1.FifoCancelledRecordsReported work
        (events ++ (queue.handleGraphEvents inputs).2) := by
  have raw := reported.rawEventReplay generated cached records links canonical inputs matching
    (GraphEvent.availableFailures inputs) (generated.availableFailures_positive inputs matching)
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · simpa only [List.append_nil] using reported
  · dsimp only
    split
    · apply raw.mono
      intro output member
      simp only [List.mem_append] at member ⊢
      rcases member with (old | immediate) | waiting
      · exact .inl (.inl old)
      · exact .inl (.inr (.inl immediate))
      · exact .inr waiting
    · exact raw

/-- Actual generated initialization and dispatch derive emitted-or-pending reports. -/
theorem ExecutedWork.handleGraphEvents_cancelledRecordsReported {work : Execution.Work}
    (generated : ExecutedWork work) (inputs : List GraphEvent)
    (matching : ∀ event ∈ inputs, event.MatchesWork work)
    : let queue := State.initialize (Work.fromExecution work)
      (queue.handleGraphEvents inputs).1.FifoCancelledRecordsReported work
        (queue.handleGraphEvents inputs).2 := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial : (State.initialize (Work.fromExecution work)).FifoCancelledRecordsReported work [] :=
    createWorkQueue_cancelledRecordsReported (Work.fromExecution work) work _
  simpa only [List.nil_append] using initial.handleGraphEvents generated
    (createWorkQueue_taskRejections _ _)
    (createWorkQueue_groupNodesMatchWork work)
    (createWorkQueue_childLinksCanonical _ parents
      (fun _ member => workFromSpec_groups_parentCanonical_root canonical member))
    canonical inputs matching

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
