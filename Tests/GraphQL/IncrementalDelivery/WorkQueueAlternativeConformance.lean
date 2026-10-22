import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.Conformance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceObservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.QueryCorrectness
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Exact public targets, source observations, and actual-query bridge checks. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkQueueAlternativeConformance
open AlternativeWorkQueue

example : AlternativeWorkQueue.createWorkQueueForScheduleConforms :=
  createWorkQueueForScheduleConforms_holds

example : AlternativeWorkQueue.replayMatchesReference := replayMatchesReference_holds

example : AlternativeWorkQueue.createWorkQueueForScheduleMatchesReference :=
  createWorkQueueForScheduleMatchesReference_holds

example : AlternativeWorkQueue.responseReplayMatchesReference :=
  responseReplayMatchesReference_holds

example (work : Work) (schedule : EventSource (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (valid : schedule.ValidFor work)
    : (createWorkQueueForSchedule work schedule).Conforms work :=
  createWorkQueueForScheduleConforms_holds work schedule generated
    ((Execution.Work.isEmpty_eq_false work).mpr nonempty) valid

example (work : Work) (schedule : EventSource (List GraphEvent))
    (empty : schedule.admissible [])
    : (createWorkQueueForSchedule work schedule).Initialized :=
  createWorkQueueForSchedule_initialized work schedule empty

example (work : Work) (schedule : EventSource (List GraphEvent))
    (closed
      : ∀ before after,
          before.IsPrefix after → schedule.admissible after → schedule.admissible before)
    : (createWorkQueueForSchedule work schedule).PrefixClosed :=
  createWorkQueueForSchedule_prefixClosed work schedule closed

example (work : Work) (inputs : List (List GraphEvent))
    (target : List (List Execution.WorkQueueEvent))
    (earlier : target.IsPrefix ((State.initialize work).runNormalized inputs).2)
    : ∃ before,
        before.IsPrefix inputs
        ∧ ((State.initialize work).runNormalized before).2 = target :=
  State.runNormalized_initialize_prefix_reachable work inputs target earlier

example (state : State) (inputs : List (List GraphEvent)) (closed : state.stopped = true)
    : state.runNormalized inputs = (state, []) :=
  state.runNormalized_after_stop inputs closed

example (state : State) (before after : List (List GraphEvent))
    (done : (state.runNormalized before).1.queue.terminated = true)
    : state.runNormalized (before ++ after) = state.runNormalized before :=
  state.runNormalized_termination_stable before after done

example (sources : Work → EventSource (List GraphEvent)) (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef) (variables : Execution.VariableValues)
    (operation : Operation) (fuel : Nat) (root : Execution.ResolverValue ObjectRef)
    (inputs : List (List GraphEvent)) (complete : Bool)
    (applies : Execution.rootSourceAppliesBool schema operation root = true)
    : let completed := queryCompletion schema resolvers variables operation fuel root
      let work := completed.work
      let response := Execution.selectionSetResultToResponse completed.result
      let (initial, cursor) := ResponseStreamCursor.buildResponse response work
      let (updates, finalCursor, _) := cursor.run inputs
      let factory := fun work => createWorkQueueForSchedule work (sources work)
      work.size ≠ 0 → (sources work).ValidFor work → (sources work).admissible inputs
      → (complete = true → finalCursor.queue.queue.terminated = true)
      → queryWorkQueueConforms factory schema resolvers variables operation fuel root
        ∧ queryObservation factory schema resolvers variables operation fuel root
            (.incremental initial updates) complete :=
  ResponseStreamCursor.queryObservation sources schema resolvers variables operation fuel
    root inputs complete applies

-- A cancelled finite stream ignores late input, but still has incomplete semantic work.
private def stream : Execution.DeliveryNode := { ref := 0, path := [] }

private def pending : State :=
  State.initialize (.stream stream [({ result := .ok (.scalar "I", 0) }, .empty)])

private def cancelled : State := pending.cancel.1

#guard cancelled.stopped
#guard !cancelled.queue.terminated
#guard
  (cancelled.runNormalized [[.streamSuccess stream], [.streamFailure stream 1]]).2.isEmpty
#guard !(cancelled.runNormalized [[.streamSuccess stream]]).1.queue.terminated

-- Normal completion absorbs extra input without duplicating its terminal output.
private def ended : State × List (List Execution.WorkQueueEvent) :=
  (State.initialize (.stream stream [])).runNormalized [[.streamSuccess stream]]

#guard ended.1.queue.terminated
#guard (ended.1.runNormalized [[.streamSuccess stream], []]).2.isEmpty
#guard ended.1.queue.groupNodes.isEmpty && ended.1.queue.taskNodes.isEmpty

#print axioms createWorkQueueForScheduleConforms_holds
#print axioms replayMatchesReference_holds
#print axioms responseReplayMatchesReference_holds
#print axioms createWorkQueueForSchedule_prefixClosed
#print axioms State.runNormalized_initialize_prefix_reachable
#print axioms State.runNormalized_termination_stable
#print axioms ResponseStreamCursor.queryObservation
#print axioms ResponseStreamCursor.queryOutcome
#print axioms ResponseStreamCursor.queryCorrectness

end GraphQL.IncrementalDelivery.Tests.WorkQueueAlternativeConformance
