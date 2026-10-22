import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingCounts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupFrames

/-! Computation-cache exposure preserves host start eligibility. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem State.putTaskNode_taskOccurrences (queue : State) (updated : TaskNode)
    : (queue.putTaskNode updated).taskNodes.map (fun node => node.task.occurrence)
      = queue.taskNodes.map (fun node => node.task.occurrence) := by
  simp only [State.putTaskNode, List.map_map]
  apply List.map_congr_left
  intro node member
  dsimp only [Function.comp_apply]
  split
  · rename_i same
    exact ((occurrence_beq_iff_eq _ _).mp same).symm
  · rfl

/-- Exposing rejection outcomes preserves the list of started computation identities. -/
theorem State.cacheTaskFailures_taskOccurrences (queue : State)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).taskNodes.map (fun node => node.task.occurrence)
      = queue.taskNodes.map (fun node => node.task.occurrence) := by
  induction available generalizing queue with
  | nil => rfl
  | cons entry rest ih =>
      simp only [State.cacheTaskFailures, List.foldl_cons]
      split
      · exact ih queue
      · exact (ih _).trans (queue.putTaskNode_taskOccurrences _)

/-- Cache exposure neither starts computations nor changes active stream roots. -/
theorem State.cacheTaskFailures_acceptsGraphEvent (queue : State)
    (available : List (Occurrence × Nat)) (event : GraphEvent)
    : (queue.cacheTaskFailures available).acceptsGraphEvent event
      = queue.acceptsGraphEvent event := by
  have task (occurrence : Occurrence)
      : ((queue.cacheTaskFailures available).taskNode? occurrence).isSome
        = (queue.taskNode? occurrence).isSome := by
    have same := congrArg
      (fun tasks : List Occurrence => tasks.any (fun task => task == occurrence))
      (queue.cacheTaskFailures_taskOccurrences available)
    simpa only [List.any_map, Function.comp_def, State.taskNode?, List.isSome_find?] using same
  have streams : (queue.cacheTaskFailures available).rootStreams = queue.rootStreams := by
    have frame := congrArg State.rootStreams (queue.cacheTaskFailures_frame available)
    exact frame
  have notices
      : (queue.cacheTaskFailures available).groupFailureEvents
        = queue.groupFailureEvents := by
    have frame := congrArg State.groupFailureEvents (queue.cacheTaskFailures_frame available)
    exact frame
  cases event with
  | groupFailure failure => simp only [State.acceptsGraphEvent, notices]
  | taskSuccess occurrence _ | taskFailure occurrence _ => exact task occurrence
  | streamItems stream _ | streamSuccess stream | streamFailure stream _ =>
      simp only [State.acceptsGraphEvent, streams]

/-- Immediate output can only come from a currently executable callback. A stale task or
stream callback returns no immediate event; cache exposure alone emits no output.
This implication is independent of source admission and batch-entry eligibility.
-/
theorem State.handleGraphEvent_accepts_of_emitted {queue : State} {event : GraphEvent}
    {output : Execution.WorkQueueEvent} (available : List (Occurrence × Nat))
    (emitted : output ∈ (queue.handleGraphEvent event available).2.1)
    : queue.acceptsGraphEvent event = true := by
  let current := queue.cacheTaskFailures available
  have eligible : current.acceptsGraphEvent event = true := by
    cases event with
    | taskSuccess occurrence result =>
        cases found : current.taskNode? occurrence with
        | none =>
            change output ∈ (current.taskSuccess occurrence result available).2.1 at emitted
            simp only [State.taskSuccess, found, List.not_mem_nil] at emitted
        | some node => simp only [State.acceptsGraphEvent, found, Option.isSome_some]
    | taskFailure occurrence errors =>
        cases found : current.taskNode? occurrence with
        | none =>
            change output ∈ (current.taskFailure occurrence errors).2 at emitted
            simp only [State.taskFailure, found, List.not_mem_nil] at emitted
        | some node => simp only [State.acceptsGraphEvent, found, Option.isSome_some]
    | groupFailure failure =>
        change output ∈ (current.groupFailure failure).2 at emitted
        unfold State.groupFailure at emitted
        split at emitted
        · cases emitted
        · rename_i first rest queued
          split at emitted
          · rename_i matched
            simpa only [State.acceptsGraphEvent, queued, List.head?_cons, Option.any_some]
              using matched
          · cases emitted
    | streamItems stream items =>
        by_cases active : current.rootStreams.contains stream.ref = true
        · exact active
        · have absent := Bool.eq_false_iff.mpr active
          change output ∈ (current.streamItems stream items available).2.1 at emitted
          simp only [State.streamItems, absent, Bool.not_false, ite_true,
            List.not_mem_nil] at emitted
    | streamSuccess stream =>
        by_cases active : current.rootStreams.contains stream.ref = true
        · exact active
        · have absent := Bool.eq_false_iff.mpr active
          change output ∈ (current.streamSuccess stream).2 at emitted
          simp only [State.streamSuccess, absent, Bool.false_eq_true, ite_false,
            List.not_mem_nil] at emitted
    | streamFailure stream errors =>
        by_cases active : current.rootStreams.contains stream.ref = true
        · exact active
        · have absent := Bool.eq_false_iff.mpr active
          change output ∈ (current.streamFailure stream errors).2 at emitted
          simp only [State.streamFailure, absent, Bool.false_eq_true, ite_false,
            List.not_mem_nil] at emitted
  rwa [State.cacheTaskFailures_acceptsGraphEvent] at eligible

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
