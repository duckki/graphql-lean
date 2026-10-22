import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamItemRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots

/-! Every announced stream remains active until a concrete success or failure completion. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful and failed stream closures are the only operations that remove stream roots
-----------------------------------------------------------------------------------------

/-- Stream refs completed by a raw output event, excluding group completions. -/
def rawStreamClosureRefs : WorkQueueEvent → NodeRefs
  | .streamSuccess stream | .streamFailure stream _ => [stream.ref]
  | _ => []

/-- Initial and carried stream refs remain active or have an emitted stream completion.
The parameters describe concrete refs and a replay segment, without scheduler admission.
-/
def StreamNoticeCompletion (initial : NodeRefs) (result : State × List WorkQueueEvent)
    : Prop :=
  ∀ ref ∈ initial ++ result.2.flatMap rawStreamNoticeRefs,
    ref ∈ result.1.rootStreams ∨ ref ∈ result.2.flatMap rawStreamClosureRefs

/-- Task failure emits no stream notices, including through latent error-cache updates.
Witness: every owner step either emits a group failure or no output at all.
-/
theorem State.taskFailure_streamNoticeRefs (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).2.flatMap rawStreamNoticeRefs = [] := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      : (groups.foldl (failureGroupStep errors) acc).2.flatMap rawStreamNoticeRefs
        = acc.2.flatMap rawStreamNoticeRefs := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih]
        obtain ⟨current, outputs⟩ := acc
        unfold failureGroupStep
        dsimp only
        split
        · rfl
        · split
          · simp only [State.finishGroupFailure, List.flatMap_append,
              List.flatMap_singleton, rawStreamNoticeRefs, List.append_nil]
          · rfl
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found]
  | some incoming =>
      rw [queue.taskFailure_eq occurrence errors incoming found]
      exact loop _ _

/-- Every handler retains announced stream roots or emits their actual completion.
Witness: task/item success covers all new stream notices, task failure preserves roots,
and each stream-close branch removes only its explicitly completed ref.
-/
theorem State.handleGraphEvent_streamNoticeCompletion (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : StreamNoticeCompletion queue.rootStreams
        (
          (queue.handleGraphEvent event available).1,
          (queue.handleGraphEvent event available).2.1
        ) := by
  let current := queue.cacheTaskFailures available
  have roots : current.rootStreams = queue.rootStreams := by
    have frame := congrArg State.rootStreams (queue.cacheTaskFailures_frame available)
    exact frame
  rw [← roots]
  unfold State.handleGraphEvent
  cases event with
  | taskSuccess occurrence result =>
      intro ref member
      exact .inl (current.taskSuccess_streamRoots_cover occurrence result available member)
  | taskFailure occurrence errors =>
      intro ref member
      simp only [State.taskFailure_streamNoticeRefs,
        List.append_nil] at member
      exact .inl (by rwa [State.taskFailure_rootStreams])
  | streamItems stream items =>
      intro ref member
      exact .inl (current.streamItems_streamRoots_cover stream items available member)
  | streamSuccess stream =>
      simp only [State.streamSuccess]
      split
      · intro ref member
        have old : ref ∈ current.rootStreams := by simpa [rawStreamNoticeRefs] using member
        by_cases same : ref = stream.ref
        · exact .inr (by simp [rawStreamClosureRefs, same])
        · exact .inl (List.mem_filter.mpr ⟨old, by simpa using same⟩)
      · intro ref member; exact .inl (by simpa using member)
  | streamFailure stream errors =>
      simp only [State.streamFailure]
      split
      · intro ref member
        have old : ref ∈ current.rootStreams := by simpa [rawStreamNoticeRefs] using member
        by_cases same : ref = stream.ref
        · exact .inr (by simp [rawStreamClosureRefs, same])
        · exact .inl (List.mem_filter.mpr ⟨old, by simpa using same⟩)
      · intro ref member; exact .inl (by simpa using member)

  | groupFailure failure =>
      simp only [State.groupFailure]
      split
      · intro ref member; exact .inl (by simpa using member)
      · split <;> intro ref member <;> exact .inl (by simpa [rawStreamNoticeRefs] using member)

/-- Realized enqueue effects preserve the stream completion certificate. -/
theorem State.dispatchGraphEvent_streamNoticeCompletion (queue : State)
    (event : GraphEvent) (available : List (Occurrence × Nat) := [])
    : StreamNoticeCompletion queue.rootStreams
        (queue.dispatchGraphEvent event available) :=
  queue.handleGraphEvent_streamNoticeCompletion event available

-----------------------------------------------------------------------------------------
-- Concrete tracking composes across arbitrary source replay
-----------------------------------------------------------------------------------------

/-- Stream notice tracking composes without a freshness or generation assumption.
Witness: retained roots feed the next segment, while every earlier completion persists.
-/
theorem StreamNoticeCompletion.append {initial first second}
    (left : StreamNoticeCompletion initial first)
    (right : StreamNoticeCompletion first.1.rootStreams second)
    : StreamNoticeCompletion initial (second.1, first.2 ++ second.2) := by
  intro ref member
  have later (member : ref ∈ first.1.rootStreams ++ second.2.flatMap rawStreamNoticeRefs) :=
    (right ref member).imp_right (List.mem_append_right (first.2.flatMap rawStreamClosureRefs))
  simp only [List.flatMap_append] at member ⊢
  rcases List.mem_append.mp member with old | noticed
  · rcases left ref (List.mem_append_left _ old) with active | closed
    · exact later (List.mem_append_left _ active)
    · exact .inr (List.mem_append_left _ closed)
  · rcases List.mem_append.mp noticed with earlier | next
    · rcases left ref (List.mem_append_right _ earlier) with active | closed
      · exact later (List.mem_append_left _ active)
      · exact .inr (List.mem_append_left _ closed)
    · exact later (List.mem_append_right _ next)

/-- Every actual raw stream notice stays active until a corresponding emitted completion.
Witness: compose the actual handler results in order. Unlike protected group cleanup,
this concrete invariant requires no generated-work or matching-source premise.
-/
theorem State.rawEventReplay_streamNoticeCompletion (queue : State)
    (events : List GraphEvent) (available : List (Occurrence × Nat) := [])
    : StreamNoticeCompletion queue.rootStreams
        (queue.rawEventReplay events available) := by
  induction events generalizing queue with
  | nil => intro ref member; exact .inl (by simpa [State.rawEventReplay] using member)
  | cons event rest ih =>
      rw [State.rawEventReplay_cons queue event rest available]
      exact (queue.dispatchGraphEvent_streamNoticeCompletion event available).append (ih _)

/-- Additional controls without stream notices preserve exact stream completion tracking. -/
theorem StreamNoticeCompletion.append_noticeFree {initial result}
    (tracked : StreamNoticeCompletion initial result) (controls : List WorkQueueEvent)
    (noNotices : controls.flatMap rawStreamNoticeRefs = [])
    : StreamNoticeCompletion initial (result.1, result.2 ++ controls) := by
  have right : StreamNoticeCompletion result.1.rootStreams (result.1, controls) := by
    intro ref member
    exact .inl (by simpa only [noNotices, List.append_nil] using member)
  exact tracked.append right

/-- Actual FIFO replay and termination retain the exact stream completion certificate. -/
theorem State.handleGraphEvents_streamNoticeCompletion (queue : State)
    (events : List GraphEvent)
    : StreamNoticeCompletion queue.rootStreams (queue.handleGraphEvents events) := by
  have prior := queue.rawEventReplay_streamNoticeCompletion events
    (GraphEvent.availableFailures events)
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · intro ref member; exact .inl (by simpa using member)
  · dsimp only
    split
    · exact prior.append_noticeFree [.workQueueTermination] rfl
    · exact prior

/-- Stream completion tracking composes over the actual raw batch output and state. -/
theorem State.rawBatches_streamNoticeCompletion (queue : State)
    (batches : List (List GraphEvent))
    : StreamNoticeCompletion queue.rootStreams (queue.rawBatches batches) := by
  induction batches generalizing queue with
  | nil => intro ref member; exact .inl (by simpa [State.rawBatches] using member)
  | cons batch rest ih =>
      exact (queue.handleGraphEvents_streamNoticeCompletion batch).append (ih _)

/-- At termination every initial or carried stream notice has an emitted stream completion.
Witness: initialization activates every notice, exact raw tracking retains it until closure,
and the started replay's terminal root set is empty. Empty streams require no special case.
-/
theorem createWorkQueue_terminalStreamCompleted {work inputs ref}
    (_started : inputsStarted work inputs = true)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (announced
      : ref
        ∈ (State.initialize (Work.fromExecution work)).initialStreams.map
            Execution.DeliveryNode.ref
          ++ ((State.initialize (Work.fromExecution work)).rawBatches inputs).2.flatMap
              rawStreamNoticeRefs)
    : ref
      ∈ ((State.initialize (Work.fromExecution work)).rawBatches inputs).2.flatMap
          rawStreamClosureRefs := by
  have noticed : ref ∈ (State.initialize (Work.fromExecution work)).rootStreams
      ++ ((State.initialize (Work.fromExecution work)).rawBatches inputs).2.flatMap
        rawStreamNoticeRefs := by
    rcases List.mem_append.mp announced with initial | carried
    · exact List.mem_append_left _ (createWorkQueue_initialStreams_active _ initial)
    · exact List.mem_append_right _ carried
  have tracked := State.rawBatches_streamNoticeCompletion
    (State.initialize (Work.fromExecution work)) inputs ref noticed
  have empty := (createWorkQueue_replayBatches_terminalRoots ended).2
  exact tracked.resolve_left (by rw [State.rawBatches_state, empty]; simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
