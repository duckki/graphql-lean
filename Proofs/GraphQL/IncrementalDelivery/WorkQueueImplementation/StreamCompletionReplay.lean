import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamItemRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots

/-! Every announced stream remains active until a concrete success or failure completion. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful and failed stream closures are the only operations that remove stream roots
-----------------------------------------------------------------------------------------

/-- Stream keys completed by a raw output event, excluding group completions. -/
def rawStreamClosureKeys : WorkQueueEvent → Keys
  | .streamSuccess stream | .streamFailure stream _ => [stream.key]
  | _ => []

/-- Initial and carried stream keys remain active or have an emitted stream completion.
The parameters describe concrete keys and a replay segment, without scheduler admission.
-/
def StreamNoticeCompletion (initial : Keys) (result : State × List WorkQueueEvent)
    : Prop :=
  ∀ key ∈ initial ++ result.2.flatMap rawStreamNoticeKeys,
    key ∈ result.1.rootStreams ∨ key ∈ result.2.flatMap rawStreamClosureKeys

/-- Task failure emits no stream notices, including through latent error-cache updates.
Witness: every owner step either emits a group failure or no output at all.
-/
theorem State.taskFailure_streamNoticeKeys (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).2.flatMap rawStreamNoticeKeys = [] := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      : (groups.foldl (failureGroupStep errors) acc).2.flatMap rawStreamNoticeKeys
        = acc.2.flatMap rawStreamNoticeKeys := by
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
              List.flatMap_singleton, rawStreamNoticeKeys, List.append_nil]
          · rfl
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found]
  | some incoming =>
      rw [queue.taskFailure_eq occurrence errors incoming found]
      split
      · rfl
      · exact loop _ _

/-- Every handler retains announced stream roots or emits their actual completion.
Witness: task/item success covers all new stream notices, task failure preserves roots,
and each stream-close branch removes only its explicitly completed key.
-/
theorem State.handleGraphEvent_streamNoticeCompletion (queue : State) (event : GraphEvent)
    : StreamNoticeCompletion queue.rootStreams (queue.handleGraphEvent event) := by
  cases event with
  | taskSuccess occurrence result =>
      intro key member
      exact .inl (queue.taskSuccess_streamRoots_cover occurrence result member)
  | taskFailure occurrence errors =>
      intro key member
      simp only [State.handleGraphEvent, State.taskFailure_streamNoticeKeys,
        List.append_nil] at member
      exact .inl (by rwa [State.handleGraphEvent, State.taskFailure_rootStreams])
  | streamItems stream items =>
      intro key member
      exact .inl (queue.streamItems_streamRoots_cover stream items member)
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split
      · intro key member
        have old : key ∈ queue.rootStreams := by simpa [rawStreamNoticeKeys] using member
        by_cases same : key = stream.key
        · exact .inr (by simp [rawStreamClosureKeys, same])
        · exact .inl (List.mem_filter.mpr ⟨old, by simpa using same⟩)
      · intro key member; exact .inl (by simpa using member)
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split
      · intro key member
        have old : key ∈ queue.rootStreams := by simpa [rawStreamNoticeKeys] using member
        by_cases same : key = stream.key
        · exact .inr (by simp [rawStreamClosureKeys, same])
        · exact .inl (List.mem_filter.mpr ⟨old, by simpa using same⟩)
      · intro key member; exact .inl (by simpa using member)

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
  intro key member
  have later (member : key ∈ first.1.rootStreams ++ second.2.flatMap rawStreamNoticeKeys) :=
    (right key member).imp_right (List.mem_append_right (first.2.flatMap rawStreamClosureKeys))
  simp only [List.flatMap_append] at member ⊢
  rcases List.mem_append.mp member with old | noticed
  · rcases left key (List.mem_append_left _ old) with active | closed
    · exact later (List.mem_append_left _ active)
    · exact .inr (List.mem_append_left _ closed)
  · rcases List.mem_append.mp noticed with earlier | next
    · rcases left key (List.mem_append_right _ earlier) with active | closed
      · exact later (List.mem_append_left _ active)
      · exact .inr (List.mem_append_left _ closed)
    · exact later (List.mem_append_right _ next)

/-- Every actual raw stream notice stays active until a corresponding emitted completion.
Witness: compose the actual handler results in order. Unlike protected group cleanup,
this concrete invariant requires no generated-work or matching-source premise.
-/
theorem State.rawEventReplay_streamNoticeCompletion (queue : State)
    (events : List GraphEvent)
    : StreamNoticeCompletion queue.rootStreams (queue.rawEventReplay events) := by
  induction events generalizing queue with
  | nil => intro key member; exact .inl (by simpa [State.rawEventReplay] using member)
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      exact (queue.handleGraphEvent_streamNoticeCompletion event).append (ih _)

/-- At termination every initial or carried stream notice has an emitted stream completion.
Witness: initialization activates every notice, exact raw tracking retains it until closure,
and the started replay's terminal root set is empty. Empty streams require no special case.
-/
theorem createWorkQueue_terminalStreamCompleted {work inputs key}
    (started : inputsStarted work inputs = true)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (announced
      : key
        ∈ (State.initialize (Work.fromExecution work)).initialStreams.map
            Execution.DeliveryNode.key
          ++ ((State.initialize (Work.fromExecution work)).rawEventReplay
                inputs.flatten).2.flatMap
              rawStreamNoticeKeys)
    : key
      ∈ ((State.initialize (Work.fromExecution work)).rawEventReplay
          inputs.flatten).2.flatMap
          rawStreamClosureKeys := by
  have noticed : key ∈ (State.initialize (Work.fromExecution work)).rootStreams
      ++ ((State.initialize (Work.fromExecution work)).rawEventReplay inputs.flatten).2.flatMap
        rawStreamNoticeKeys := by
    rcases List.mem_append.mp announced with initial | carried
    · exact List.mem_append_left _ (createWorkQueue_initialStreams_active _ initial)
    · exact List.mem_append_right _ carried
  have tracked := State.rawEventReplay_streamNoticeCompletion
    (State.initialize (Work.fromExecution work)) inputs.flatten key noticed
  have empty := (createWorkQueue_replayGraphEvents_terminalRoots started ended).2
  rw [State.rawEventReplay_state] at tracked
  exact tracked.resolve_left (by rw [empty]; simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
