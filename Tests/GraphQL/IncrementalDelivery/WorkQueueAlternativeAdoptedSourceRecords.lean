import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AdoptedSourceRecords
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

/-! The real structural mapping is essential: legal adoption alone cannot create a record. -/

namespace AlternativeAdoptedSourceRecordChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedAdoptedSourceProgress := GeneratedAdoptedSourceProgress_holds
example : GeneratedDispatchSourcesRepresented := GeneratedDispatchSourcesRepresented_holds

-----------------------------------------------------------------------------------------
-- An independently acquired but wrongly mapped source refutes legality-only preservation
-----------------------------------------------------------------------------------------

private abbrev producer := SharedOwnerFailure.heldProducer
private def inputs : List (List GraphEvent) := [[SharedOwnerFailure.parentSuccess]]

private abbrev before :=
  ((State.initialize SharedOwnerFailure.work).runNormalized inputs).1

private abbrev reduced :=
  ({ state := before } : GraphBatchResult).handleGraphEvent SharedOwnerFailure.success

private def acquired : ResourceState :=
  ResourceState.empty.set (.stream 9) (.owned (.producer producer))

private def inventories : ProducerInventories := fun _ => [.stream 9]

private abbrev observed :=
  acquired.observeDispatch inventories before SharedOwnerFailure.success

private theorem previouslyRepresented : SourcesRepresented before.queue acquired := by
  intro key owned
  by_cases same : key = 9
  · simp [acquired, ResourceState.set, same] at owned
  · simp [acquired, ResourceState.set, ResourceState.empty, same] at owned

private theorem handoff
    : ResourceReplay ResourceState.empty
        ([.acquire (.stream 9) (.producer producer)] ++ observed.2) observed.1 :=
  (ResourceReplay.cons (.acquire _ _ _ rfl) (.nil _)).append
    (acquired.observeDispatch_replay inventories before SharedOwnerFailure.success)

example : observed.1 (.stream 9) = .owned .queue := by
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

private theorem unrepresented
    : ¬RecordTargetRepresented reduced.state.queue (.stream 9) := by
  intro represented
  cases represented with
  | activeStream active =>
      dsimp only [reduced, before] at active
      rw [SharedOwnerFailure.work_shape] at active
      cbv at active
      cases active
  | @bufferedStream occurrence node key found stored held =>
      have excludes : reduced.state.queue.taskNodes.all
          (fun node => !node.childStreams.contains 9) = true := by
        dsimp only [reduced, before]
        rw [SharedOwnerFailure.work_shape]
        cbv
      have absent := List.all_eq_true.mp excludes node (List.mem_of_find?_eq_some found)
      rw [List.contains_iff_mem.mpr held] at absent
      cases absent

example : ¬SourcesRepresented reduced.state.queue observed.1 := by
  intro represented
  apply unrepresented (represented 9 _)
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

-- This counterexample has the same generated/source/start domain; its invented native
-- correspondence, not the queue's source law, is wrong.
example
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        (inputs.flatten ++ [SharedOwnerFailure.success]) :=
  SharedOwnerFailure.valid_events.prefix
    ⟨[SharedOwnerFailure.failureG, SharedOwnerFailure.failureH], rfl⟩

example
    : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work
        (inputs ++ [[SharedOwnerFailure.success]])
      = true := by
  rw [SharedOwnerFailure.work_shape]
  cbv

#print axioms GeneratedAdoptedSourceProgress_holds
#print axioms GeneratedDispatchSourcesRepresented_holds
#print axioms previouslyRepresented
#print axioms handoff
#print axioms unrepresented

end AlternativeAdoptedSourceRecordChecks
