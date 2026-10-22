import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordPreservation
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure
import Tests.GraphQL.IncrementalDelivery.Execution

open GraphQL.IncrementalDelivery.Tests

/-! Existing held-source failure disposal and generated empty-source completion. -/

namespace AlternativeSourceRecordPreservationChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence Located NodeAt)
open GraphQL.IncrementalDelivery.Tests (schema resolvers field)

example : GeneratedRepresentedSourceProgress := GeneratedRepresentedSourceProgress_holds

example : GeneratedDispatchExistingSourceRepresentation :=
  GeneratedDispatchExistingSourceRepresentation_holds

-----------------------------------------------------------------------------------------
-- Actual generated task failure disposes an already represented held source
-----------------------------------------------------------------------------------------

private def inputs : List (List GraphEvent) :=
  [[SharedOwnerFailure.parentSuccess], [SharedOwnerFailure.success]]

private abbrev before :=
  ((State.initialize SharedOwnerFailure.work).runNormalized inputs).1

private abbrev reduced :=
  ({ state := before } : GraphBatchResult).handleGraphEvent SharedOwnerFailure.failureG

private def buffered : ReferenceWorkQueue.TaskNode :=
  {
    task :=
      {
        occurrence := SharedOwnerFailure.heldProducer,
        groups := [SharedOwnerFailure.groupG]
      },
    value :=
      some
        {
          deliveryGroups := [SharedOwnerFailure.groupG],
          path := [.field "box"],
          data := [("values", .list [])]
        },
    childStreams := [2]
  }

private theorem represented : RecordTargetRepresented before.queue (.stream 2) :=
  .bufferedStream
    (occurrence := SharedOwnerFailure.heldProducer)
    (node := buffered)
    (by dsimp only [before]; rw [SharedOwnerFailure.work_shape]; cbv)
    rfl
    (by decide)

private theorem classified
    : RecordTargetRepresented reduced.state.queue (.stream 2)
      ∨ normalCompletionTarget? before.queue SharedOwnerFailure.failureG
        = some (.stream 2)
      ∨ .cancelSource 2 ∈ reduced.effects :=
  GeneratedRepresentedSourceProgress_holds SharedOwnerFailure.work inputs
    SharedOwnerFailure.failureG SharedOwnerFailure.executed
    (SharedOwnerFailure.valid_events.prefix ⟨[SharedOwnerFailure.failureH], rfl⟩)
    (by rw [SharedOwnerFailure.work_shape]; cbv) 2 represented

private theorem disposed : .cancelSource 2 ∈ reduced.effects := by
  rcases classified with retained | completed | requested
  · cases retained with
    | activeStream active =>
        dsimp only [reduced, before] at active; rw [SharedOwnerFailure.work_shape] at active; cbv at active; cases active
    | @bufferedStream occurrence node key found stored held =>
        have empty : reduced.state.queue.taskNodes.all (fun node => node.childStreams.isEmpty) = true := by
          dsimp only [reduced, before]
          rw [SharedOwnerFailure.work_shape]
          cbv
        have noStreams := List.all_eq_true.mp empty node (List.mem_of_find?_eq_some found)
        cases streams : node.childStreams with
        | nil => rw [streams] at held; cases held
        | cons head rest => simp [streams] at noStreams
  · cases completed
  · exact requested

private def acquired : ResourceState :=
  ResourceState.empty.set (.stream 2) (.owned .queue)

example
    : (acquired.observeDispatch (fun _ => []) before SharedOwnerFailure.failureG).1
        (.stream 2)
      = .cleanupRequested .queue := by
  apply ResourceState.requestQueueCleanup_owned
  · exact List.mem_filterMap.mpr ⟨.cancelSource 2, disposed, rfl⟩
  · cbv

-----------------------------------------------------------------------------------------
-- Generated exhaustion normally completes the active empty boundary
-----------------------------------------------------------------------------------------

private def source : Execution.DeliveryNode := ⟨0, [.field "empty"], none⟩

private def work : Execution.Work :=
  .combine (.combine (.combine .empty (.stream source [])) .empty)
    (.declareGroups [] .empty)

private def event : GraphEvent := .streamSuccess source
private abbrev initial := State.initialize work
private abbrev ended := ({ state := initial } : GraphBatchResult).handleGraphEvent event

private theorem generated : ReferenceWorkQueue.ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [field "empty" [] [.stream (.boolean true) none (.int 0)]], ?_⟩
  cbv

private theorem located : Located work [0, 0, 1] (.stream source []) none [] := by cbv

private theorem valid : ReferenceWorkQueue.ValidGraphEvents work [event] := by
  refine .append .nil ⟨[], none, ?_⟩
    (by simp [event, ReferenceWorkQueue.GraphEvent.Fresh,
      ReferenceWorkQueue.GraphEvent.identities])
    ?_
  · exact ⟨[0, 0, 1], [], located⟩
  · refine ⟨[0, 0, 1], [], none, [], located, ?_, rfl⟩
    intro producer impossible
    cases impossible

private theorem completion
    : RecordTargetRepresented ended.state.queue (.stream 0)
      ∨ normalCompletionTarget? initial.queue event = some (.stream 0)
      ∨ .cancelSource 0 ∈ ended.effects :=
  GeneratedRepresentedSourceProgress_holds work [] event generated valid
    (by cbv)
    0
    (.activeStream (by cbv; exact .head _))

private def sourceLease : ResourceState :=
  ResourceState.empty.set (.stream 0) (.owned .queue)

example : normalCompletionTarget? initial.queue event = some (.stream 0) := by cbv
example : ended.state.queue.rootStreams = [] := by cbv
example : ended.effects = [] := by cbv

example
    : (sourceLease.observeDispatch (fun _ => [.stream 0]) initial event).1 (.stream 0)
      = .released := by cbv

example
    : (sourceLease.observeDispatch (fun _ => [.stream 0]) initial event).1 (.stream 0)
      ≠ .owned .queue :=
  sourceLease.observeDispatch_completedSource_not_owned _ initial event 0 (by cbv)

#print axioms GeneratedRepresentedSourceProgress_holds
#print axioms GeneratedDispatchExistingSourceRepresentation_holds
#print axioms disposed
#print axioms completion

end AlternativeSourceRecordPreservationChecks
