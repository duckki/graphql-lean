import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordProgress
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

/-! Universal generated targets and a raw repeated-success counterexample. -/

namespace AlternativeSourceRecordProgressChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

-- The original prepared-source target is constructed from actual reductions, not a cut.
example : GeneratedPreparedSourceProgress := GeneratedPreparedSourceProgress_holds

example : GeneratedDispatchSourceRepresentation :=
  GeneratedDispatchSourceRepresentation_holds

-----------------------------------------------------------------------------------------
-- A generated task result adopts a source that remains held before its owner completes
-----------------------------------------------------------------------------------------

private def inputs : List (List GraphEvent) := [[SharedOwnerFailure.parentSuccess]]

private theorem valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        (inputs.flatten ++ [SharedOwnerFailure.success]) :=
  SharedOwnerFailure.valid_events.prefix
    ⟨[SharedOwnerFailure.failureG, SharedOwnerFailure.failureH], rfl⟩

private theorem started
    : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work
        (inputs ++ [[SharedOwnerFailure.success]])
      = true := by
  rw [SharedOwnerFailure.work_shape]
  cbv

private def buffered : ReferenceWorkQueue.TaskNode :=
  {
    task :=
      {
        occurrence := SharedOwnerFailure.heldProducer,
        groups := [SharedOwnerFailure.groupG]
      }
    value :=
      some
        {
          deliveryGroups := [SharedOwnerFailure.groupG]
          path := [.field "box"]
          data := [("values", .list [])]
        }
    childStreams := [2]
  }

private theorem adopted_source_progress
    : let before := ((State.initialize SharedOwnerFailure.work).runNormalized inputs).1
      let reduced :=
        ({ state := before } : GraphBatchResult).handleGraphEvent
          SharedOwnerFailure.success
      RecordTargetRepresented reduced.state.queue (.stream 2)
      ∨ .cancelSource 2 ∈ reduced.effects :=
  GeneratedPreparedSourceProgress_holds SharedOwnerFailure.work inputs
    SharedOwnerFailure.success SharedOwnerFailure.executed valid started trivial
    SharedOwnerFailure.heldProducer buffered 2 (by cbv) rfl (by decide)

-----------------------------------------------------------------------------------------
-- Raw dispatch cannot replace generated provenance and input freshness
-----------------------------------------------------------------------------------------

private def occurrence : WorkQueueSemantics.Occurrence := .executionGroup []
private def value : Execution.ExecutionGroupValue := { path := [], data := [] }

private def node : ReferenceWorkQueue.TaskNode :=
  { task := { occurrence, groups := [] }, value := some value, childStreams := [7] }

private def before : State := { queue := { taskNodes := [node] } }
private def event : GraphEvent := .taskSuccess occurrence { value, work := {} }
private abbrev reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event

-- Raw ownerless success retains its buffered source after the presence check.
-- Generated-work ownership guarantees are tested separately above.
example : (registrationSnapshot before.queue event).taskNode? occurrence = some node := by
  cbv

example : reduced.effects = [.adopt occurrence] := by cbv
example : reduced.state.queue.taskNodes = [node] := by cbv

private theorem represented : RecordTargetRepresented reduced.state.queue (.stream 7) :=
  .bufferedStream (occurrence := occurrence) (node := node) (by cbv) rfl (by decide)

example
    : RecordTargetRepresented reduced.state.queue (.stream 7)
      ∨ .cancelSource 7 ∈ reduced.effects :=
  Or.inl represented

#print axioms State.taskSuccess_readyProjection
#print axioms referencePrefix_taskSuccess_readyProjection
#print axioms referencePrefix_taskSuccess_sources
#print axioms successFold_heldSource
#print axioms generatedPrepared_sourceClassified
#print axioms GeneratedStoredReleaseDisposal_holds
#print axioms adopted_source_progress
#print axioms GeneratedPreparedSourceProgress_holds
#print axioms GeneratedDispatchSourceRepresentation_holds
#print axioms represented

end AlternativeSourceRecordProgressChecks
