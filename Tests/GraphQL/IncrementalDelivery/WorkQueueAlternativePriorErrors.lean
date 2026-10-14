import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingCutHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecordedErrors
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A completed nullable failure followed by a fatal failure. Both public actions run;
there is no cancelled error to explain reporting only one at the fatal task boundary.
The recording witness uses their constructed outcomes, not an arbitrary error total.
-/

namespace AlternativePriorErrorChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement.ScheduledErrors

private def fields : CollectedFieldsMap :=
  [
    ("nullable", [{ fieldName := "fail", arguments := [], selectionSet := [] }]),
    ("required", [{ fieldName := "required", arguments := [], selectionSet := [] }])
  ]

private def actions :=
  fieldActions Tests.schema Tests.resolvers [] 4 "Query" (.object "Query" 0) fields [] []
    []

private def plan := completionPlan ((observeActions actions).run 0).1 0

private def nullable : Sibling (List (GraphQL.Name × ResponseValue)) :=
  ⟨0, .ok ([("nullable", .null)], 1)⟩

private def fatal : Sibling (List (GraphQL.Name × ResponseValue)) := ⟨1, .error 1⟩

example : plan = [nullable, fatal] := by cbv
example : (cutActions List.append [] actions |>.run 0).1.result = .error 2 := by cbv
example : (observeUntilFatal actions |>.run 0).1.2 = [] := by cbv

example
    : ((executeExecutionGroup Tests.schema Tests.resolvers [] 4 "Query"
          (.object "Query" 0) fields [] [] []).run
        0).1.result
      = .error 2 := by cbv

private def initial : Recording (List (GraphQL.Name × ResponseValue)) :=
  { scope := { pending := plan }, available := errorSlots plan }

private def nullableStarted := initial.scopeStep (initial.scope.start 0) (.start 0)
private def nullableRecorded := nullableStarted.record [] (0, 0) [(1, 0)]

private def nullableSettled :=
  nullableRecorded.scopeStep (nullableRecorded.scope.settle [] nullable [fatal])
    (.settle 0)

private def fatalStarted :=
  nullableSettled.scopeStep (nullableSettled.scope.start 1) (.start 1)

private def fatalRecorded := fatalStarted.record [] (1, 0) []

private def completed :=
  fatalRecorded.scopeStep (fatalRecorded.scope.settle [] fatal []) (.settle 1)

private theorem nullable_started : RecordingHistory plan nullableStarted :=
  .start .initial nullable
    (by
      change nullable ∈ plan
      rw [show plan = [nullable, fatal] by cbv]
      exact List.mem_cons_self)
    rfl
    (by simp)

private theorem nullable_recorded : RecordingHistory plan nullableRecorded :=
  .record nullable_started [] [(1, 0)] (0, 0) (by cbv) (by decide) (by decide)

private theorem nullable_settled : RecordingHistory plan nullableSettled :=
  .settle nullable_recorded [] [fatal] nullable
    (by cbv)
    (by decide)
    (by
      intro slot member
      have same : slot = (0, 0) := by
        simpa [nullable, Sibling.errorSlots, countedErrors] using member
      subst slot
      decide)

private theorem fatal_started : RecordingHistory plan fatalStarted :=
  .start nullable_settled fatal (List.mem_singleton_self fatal) rfl (by decide)

private theorem fatal_recorded : RecordingHistory plan fatalRecorded :=
  .record fatal_started [] [] (1, 0) rfl (by decide) (by decide)

private theorem both_recorded : RecordingHistory plan completed :=
  .settle fatal_recorded [] [] fatal rfl
    (by decide)
    (by
      intro slot member
      have same : slot = (1, 0) := by
        simpa [fatal, Sibling.errorSlots, countedErrors] using member
      subst slot
      decide)

example : completed.recorded = [(0, 0), (1, 0)] := rfl
example : completed.scope.cancelled = [] := rfl
example : completed.omitted = [] := rfl
example : completed.observe plan = some (.error 2) := rfl
example : completed.observe plan ≠ some (.error 1) := by intro same; cases same

example
    : completed.recorded.length + completed.available.length + completed.omitted.length
      = countedErrors (eager plan) :=
  both_recorded.error_accounting

-- Origin slots are distinct because the actual action plan's position IDs are distinct.
example : (completed.available ++ completed.recorded ++ completed.omitted).Nodup :=
  both_recorded.slots_unique (completionPlan_unique _ _)

#print axioms both_recorded
#print axioms RecordingHistory.error_accounting
#print axioms RecordingHistory.recorded_trace
#print axioms RecordingHistory.complete_observation

end AlternativePriorErrorChecks
