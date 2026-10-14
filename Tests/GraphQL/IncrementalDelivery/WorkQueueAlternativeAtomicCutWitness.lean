import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutRecordingHistory
import Tests.GraphQL.IncrementalDelivery.Execution

/-! One constructed witness for actual actions: the first nullable error survives the
fatal cut, and only the untouched third action's slot may be omitted. No native history
or desired error count is supplied to the constructor.
-/

namespace AlternativeAtomicCutWitnessChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement.ScheduledErrors

private def fields : CollectedFieldsMap :=
  [
    ("nullable", [{ fieldName := "fail", arguments := [], selectionSet := [] }]),
    ("fatal", [{ fieldName := "required", arguments := [], selectionSet := [] }]),
    ("cancelled", [{ fieldName := "required", arguments := [], selectionSet := [] }])
  ]

private def actions :=
  fieldActions Tests.schema Tests.resolvers [] 4 "Query" (.object "Query" 0) fields [] []
    []

private def plan := completionPlan ((observeActions actions).run 0).1 0
private def cut := (observeUntilFatal actions).run 0

example : countedErrors (eager plan) = 3 := by cbv
example : cut.1.1.length = 2 := by cbv
example : cut.1.2.length = 1 := by cbv

-- This used to require a manually supplied recording history. The constructor now
-- derives all inventories, observation and supply evidence from the actual action cut.
example
    : ∃ recording,
        RecordingHistory plan recording
        ∧ recording.scope.pending = []
        ∧ recording.available = []
        ∧ recording.recorded = [(0, 0), (1, 0)]
        ∧ recording.omitted = [(2, 0)]
        ∧ recording.scope.actions = [.start 0, .settle 0, .start 1, .settle 1, .cancel 2]
        ∧ recording.observe plan = some (.error 2)
        ∧ recording.recorded.length + recording.omitted.length = 3
        ∧ (recording.recorded ++ recording.omitted).Nodup
        ∧ SupplyExtension 0 cut.2 ((observeActions actions).run 0).2 := by
  obtain ⟨recording, history, complete, accounted, recorded, omitted, trace, observed,
    balanced, unique, supply⟩ := atomicCutWitness_holds _ actions 0 0
      (fieldActions_monotone _ _ _ _ _ _ _ _ _ _ _ (by simp))
  refine ⟨recording, history, complete, accounted, ?_, ?_, ?_, ?_, ?_, unique, supply⟩
  · rw [recorded]
    cbv
  · rw [omitted]
    cbv
  · rw [trace]
    cbv
  · exact observed.trans (by cbv)
  · exact balanced.trans (by cbv)

-- The same history cannot explain a native payload retaining only the fatal error.
example
    : ∃ recording,
        RecordingHistory plan recording
        ∧ recording.observe plan = some (.error 2)
        ∧ recording.observe plan ≠ some (.error 1) := by
  obtain ⟨recording, history, _, _, _, _, _, observed⟩ :=
    (observeUntilFatal_cut actions 0).recording_observation 0
  have report : recording.observe plan = some (.error 2) := observed.trans (by cbv)
  exact ⟨recording, history, report, by rw [report]; intro same; cases same⟩

example : AtomicCutWitness := atomicCutWitness_holds

#print axioms ActionCut.recording_history
#print axioms ActionCut.recording_observation
#print axioms atomicCutWitness_holds

end AlternativeAtomicCutWitnessChecks
