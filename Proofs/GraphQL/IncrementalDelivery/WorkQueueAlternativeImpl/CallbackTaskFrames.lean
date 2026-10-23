import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.InterleavedCallbackRecords
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RetiredCallbackProjection

/-! Source-derived task metadata at raw callback boundaries. These frames admit buffered
notifications after retirement; no executable acceptance or publication law is assumed.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence)

/-- Structural source facts sufficient to track already enqueued task notifications. -/
structure State.CallbackTaskFrame (queue : State) (work : Execution.Work)
    (before : List GraphEvent)
    : Prop where
  sound : queue.GroupMembershipSound
  started : queue.StartedTasksRegistered
  matching : queue.RegisteredTasksMatch work
  producers : TaskProducersSucceeded work queue.tasks before
  ordered : ProducerOrder work (queue.tasks.map Task.occurrence)
  keys : queue.TaskNodeKeysUnique

/-- More consumed source inputs preserve producer support for the same task registry. -/
theorem State.CallbackTaskFrame.extend {queue work before}
    (frame : State.CallbackTaskFrame queue work before) (events : List GraphEvent)
    : queue.CallbackTaskFrame work (before ++ events) := by
  refine ⟨frame.sound, frame.started, frame.matching, ?_, frame.ordered, frame.keys⟩
  intro task member producer known
  rw [List.flatMap_append]
  exact List.mem_append_left _ (frame.producers task member producer known)

/-- Matching raw dispatch preserves task structure and source producer order. -/
theorem State.CallbackTaskFrame.handleGraphEvent {queue work before event}
    (frame : State.CallbackTaskFrame queue work before)
    (valid : ValidGraphEvents work before) (matching : event.MatchesWork work)
    (fresh : event.Fresh before) (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.CallbackTaskFrame work
        (before ++ [event]) := by
  have source := State.handleGraphEvent_producerOrder frame.producers frame.ordered
    valid matching fresh available
  exact ⟨frame.sound.handleGraphEvent event available,
    frame.started.handleGraphEvent event available,
    frame.matching.handleGraphEvent event matching available, source.1, source.2,
    frame.keys.handleGraphEvent event available⟩

/-- Realizing pending-notice enqueue effects leaves task metadata unchanged. -/
theorem State.CallbackTaskFrame.dispatchGraphEvent {queue work before event}
    (frame : State.CallbackTaskFrame queue work before)
    (valid : ValidGraphEvents work before) (matching : event.MatchesWork work)
    (fresh : event.Fresh before) (available : List (Occurrence × Nat))
    : (queue.dispatchGraphEvent event available).1.CallbackTaskFrame work
        (before ++ [event]) := by
  have next := frame.handleGraphEvent valid matching fresh available
  exact ⟨next.sound, next.started, next.matching, next.producers, next.ordered, next.keys⟩

/-- A fixed-snapshot FIFO fold preserves metadata without a consumption-time live guard. -/
theorem State.CallbackTaskFrame.replayGraphEvents {queue work before}
    (frame : State.CallbackTaskFrame queue work before) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    : (queue.replayGraphEvents events available).CallbackTaskFrame work
        (before ++ events) := by
  induction events generalizing queue before with
  | nil =>
      simpa only [State.replayGraphEvents, List.foldl_nil, List.append_nil] using frame
  | cons event rest ih =>
      have first : (before ++ [event]).IsPrefix (before ++ event :: rest) := ⟨rest, by simp⟩
      obtain ⟨prior, matching, fresh⟩ := validGraphEvents_last (valid.prefix first)
      have next := frame.dispatchGraphEvent prior matching fresh available
      simpa only [State.replayGraphEvents, List.foldl_cons, List.append_assoc,
        List.singleton_append]
        using ih next
          (by simpa only [List.append_assoc, List.singleton_append] using valid)

/-- The terminal flag changes no task metadata or producer history. -/
theorem State.CallbackTaskFrame.withTerminated {queue work before}
    (frame : State.CallbackTaskFrame queue work before) (terminated : Bool)
    : ({ queue with terminated } : State).CallbackTaskFrame work before :=
  ⟨frame.sound, frame.started, frame.matching, frame.producers, frame.ordered, frame.keys⟩

/-- Actual batch completion preserves metadata, including ignored post-terminal callbacks. -/
theorem State.CallbackTaskFrame.handleGraphEvents {queue work before}
    (frame : State.CallbackTaskFrame queue work before) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    : (queue.handleGraphEvents events).1.CallbackTaskFrame work (before ++ events) := by
  cases ended : queue.terminated with
  | true =>
      rw [queue.handleGraphEvents_after_termination events ended]
      exact frame.extend events
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events ended
      rw [same]
      exact (frame.replayGraphEvents events valid (GraphEvent.availableFailures events))
        |>.withTerminated terminal

/-- Initial task accounting and root producer provenance construct the structural frame. -/
theorem createWorkQueue_callbackTaskFrame (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).CallbackTaskFrame work [] := by
  have producers := createWorkQueue_producerOrder work
  exact ⟨createWorkQueue_groupMembershipSound _, createWorkQueue_startedTasksRegistered _,
    createWorkQueue_fromSpec_registeredTasksMatch work, producers.1, producers.2,
    createWorkQueue_taskNodeKeysUnique _⟩

/-- Track an enqueued task through a whole later batch even if its notification is stale. -/
theorem State.CallbackTaskFrame.startedTask_afterBatch {queue work before occurrence}
    (frame : State.CallbackTaskFrame queue work before)
    (disposition : queue.StartedTaskDisposition occurrence)
    (registered : occurrence ∈ queue.tasks.map Task.occurrence)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : (queue.handleGraphEvents events).1.StartedTaskDisposition occurrence
      ∧ occurrence ∈ (queue.handleGraphEvents events).1.tasks.map Task.occurrence := by
  cases ended : queue.terminated with
  | true =>
      rw [queue.handleGraphEvents_after_termination events ended]
      exact ⟨disposition, registered⟩
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events ended
      rw [same]
      have initial : queue.StartedTaskFrame work occurrence :=
        ⟨disposition, frame.sound, frame.started, frame.matching⟩
      have next := initial.replayGraphEvents registered frame.producers frame.ordered
        events valid (GraphEvent.availableFailures events)
      refine ⟨?_, ?_⟩
      · rcases next.disposition with found | absent
        · exact .inl found
        · exact .inr absent
      · have registry := queue.replayGraphEvents_tasks_subset events
          (GraphEvent.availableFailures events)
        obtain ⟨task, member, identity⟩ := List.mem_map.mp registered
        exact List.mem_map.mpr ⟨task, registry member, identity⟩

/-- Fixed producer provenance and fresh source inputs exclude re-registering any task
already catalogued at this batch boundary, including a globally retired computation.
-/
theorem State.CallbackTaskFrame.registered_not_child {queue work before occurrence}
    (frame : State.CallbackTaskFrame queue work before)
    (registered : occurrence ∈ queue.tasks.map Task.occurrence)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    {event task} (member : event ∈ events) (incoming : task ∈ event.childTasks)
    : occurrence ≠ task.occurrence := by
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
  have upto : ValidGraphEvents work ((before ++ earlier) ++ [event]) :=
    valid.prefix ⟨later, by simp only [List.append_assoc, List.singleton_append, split]⟩
  obtain ⟨prior, matching, fresh⟩ := validGraphEvents_last upto
  intro same
  exact matching.childTask_not_registered (frame.extend earlier).producers fresh incoming
    (same ▸ registered)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
