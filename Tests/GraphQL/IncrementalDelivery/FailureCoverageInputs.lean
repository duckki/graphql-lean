import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CursorObservation
import Tests.GraphQL.IncrementalDelivery.Execution

/-! The client-coverage argument boundary excludes a checked raw-input counterexample. -/

namespace GraphQL.IncrementalDelivery.Tests.FailureCoverageInputs
open GraphQL.IncrementalDelivery.Execution ReferenceWorkQueue
set_option maxRecDepth 10000

/-- Count checks use prepared bindings and are inactive only for an explicitly false if.
These regressions exercise the narrow premise, not full directive validation.
-/
private def streamOperation (count : InputValue) (condition : InputValue := .boolean true)
    (definitions : List VariableDefinition := [])
    : Operation :=
  {
    variableDefinitions := definitions
    selectionSet := [field "values" [] [.stream condition none count]]
  }

#guard (streamOperation (.int 0)).incrementalArgumentsValid []
#guard (streamOperation (.int 3)).incrementalArgumentsValid []
#guard ¬(streamOperation (.int (-1))).incrementalArgumentsValid []
#guard ¬(streamOperation .null).incrementalArgumentsValid []
#guard ¬(streamOperation (.float "1.0")).incrementalArgumentsValid []
#guard ¬(streamOperation (.string "1")).incrementalArgumentsValid []
#guard (streamOperation (.int (-1)) (.boolean false)).incrementalArgumentsValid []
#guard (streamOperation (.variable "count")).incrementalArgumentsValid []
#guard (streamOperation (.variable "count")).incrementalArgumentsValid [("count", .int 2)]
#guard ¬(streamOperation (.variable "count")).incrementalArgumentsValid [("count", .null)]
#guard
  ¬(streamOperation (.variable "count")).incrementalArgumentsValid [("count", .int (-1))]
#guard ¬(streamOperation (.int (-1)) (.variable "enabled")).incrementalArgumentsValid []
#guard
  (streamOperation (.int (-1)) (.variable "enabled")).incrementalArgumentsValid
    [("enabled", .boolean false)]

private def countDefault : Operation :=
  streamOperation (.variable "count") (.boolean true)
    [{ name := "count", typeRef := .named "Int", defaultValue := some (.int (-1)) }]

#guard ¬countDefault.incrementalArgumentsValid []
#guard countDefault.incrementalArgumentsValid [("count", .int 0)]

private def disabledDefault : Operation :=
  streamOperation (.int (-1)) (.variable "enabled")
    [{
      name := "enabled",
      typeRef := .named "Boolean",
      defaultValue := some (.boolean false)
    }]

#guard disabledDefault.incrementalArgumentsValid []
#guard ¬disabledDefault.incrementalArgumentsValid [("enabled", .boolean true)]

private def operation : Operation :=
  {
    selectionSet := [defer [field "values" [] [.stream (.boolean true) none (.int (-1))]]]
  }

private def completed :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      operation.selectionSet).run
    0).1

private def inputs : List (List GraphEvent) :=
  [[.taskSuccess (.executionGroup [1, 0])
      {
        value :=
          {
            path := []
            data := [("values", .null)]
            errors := 1
            deliveryGroups := [{ ref := 0, path := [] }]
          }
      }]]

private def result : ExecutionObservation :=
  let (initial, updates, _) := replayIncrementalResponse completed inputs
  .incremental initial updates

private def schedule := EventSource.ofList inputs

private theorem task_known
    : WorkQueueSemantics.TaskAt completed.work (.executionGroup [1, 0]) [0] none
        (.object [] (.ok ([("values", .null)], 1))) := by
  refine ⟨[{ node := { ref := 0, path := [] }, ancestors := [] }], [],
    { result := .ok ([("values", .null)], 1) }, .combine .empty .empty, [], ?_, rfl, rfl⟩
  cbv

private theorem inputs_valid : ValidGraphEvents completed.work inputs.flatten := by
  apply ValidGraphEvents.append .nil
  · exact ⟨[0], none, task_known, by cbv, by cbv⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨[0], none, _, task_known, fun _ impossible => by cases impossible⟩

private theorem schedule_valid : schedule.ValidFor completed.work := by
  apply EventSource.ValidFor.of_asynchronous
  refine ⟨rfl, List.nil_prefix, fun _ _ prior admitted => prior.trans admitted, ?_⟩
  intro batches admitted
  refine ⟨inputs_valid.prefix ?_, ?_⟩
  · obtain ⟨tail, same⟩ := admitted
    exact ⟨tail.flatten, by rw [← List.flatten_append, ← same]⟩
  · have same := List.prefix_iff_eq_take.mp admitted
    have bound : batches.length ≤ 1 := admitted.length_le
    have lengths : batches.length = 0 ∨ batches.length = 1 := by omega
    rcases lengths with length | length <;> rw [same, length] <;> cbv

/-- The counterexample is an admitted complete replay of actual execution-generated work.
Witness: the fixed successful task outcome, valid started source, and terminating runner.
Its nullable field error is carried by the data patch, not the completion notice.
-/
theorem observation_matches
    : queryScheduleMatches schema resolvers [] operation 30
        (.object "Query" 0) schedule result true := by
  refine ⟨by cbv, by cbv, schedule_valid, inputs, List.prefix_refl _, ?_⟩
  refine ⟨?_, rfl⟩
  intro _
  change (replayIncrementalResponse completed inputs).2.2 = true
  cbv

/-- Erased execution has a list item that neither delivers nor has a completion scope.
Witness: exact slice decoding gives only values:null, while scope decoding gives [].
Ordinary execution without @stream returns all three list items.
-/
theorem positions_not_addressed
    : ¬result.AddressesResponsePositions false
        (GraphQL.Execution.executeQueryWithFuel schema resolvers []
          operation.eraseIncrementalDirectives 30 (.object "Query" 0)).data := by
  rintro ⟨slices, scopes, delivered, decoded, covered⟩
  have exactSlices : slices = [[], [[.field "values"]]] := by
    have calculated : result.decodeSlices false = some [[], [[.field "values"]]] := by cbv
    exact Option.some.inj (delivered.symm.trans calculated)
  have exactScopes : scopes = [] := by
    have calculated : result.collectFailureScopes = some [] := by cbv
    exact Option.some.inj (decoded.symm.trans calculated)
  obtain good | failed := covered [.field "values", .index 0]
    (by cbv; exact List.mem_cons_self)
  · rw [exactSlices] at good
    simp at good
  · rw [exactScopes] at failed
    simp at failed

/-- Dropping the new argument premise admits a conforming counterexample to coverage.
Witness: implementation correctness supplies query-local queue conformance and a complete
actual query outcome with zero initial errors, yet the decoded response misses a basic path.
This does not weaken queue accounting: an invalid incremental argument disappears under
directive erasure and causes an ordinary nullable field error in the incremental patch.
-/
theorem coverage_requires_input_boundary
    : queryWorkQueueConforms (createWorkQueueForSchedule · schedule) schema resolvers []
        operation 30 (.object "Query" 0)
      ∧ queryOutcome (createWorkQueueForSchedule · schedule) schema resolvers [] operation
          30 (.object "Query" 0) result
      ∧ result.initialErrors = 0
      ∧ ¬operation.incrementalArgumentsValid []
      ∧ ¬result.AddressesResponsePositions false
          (GraphQL.Execution.executeQueryWithFuel schema resolvers []
            operation.eraseIncrementalDirectives 30 (.object "Query" 0)).data := by
  have bridge := implementationCorrect_holds schema operation resolvers [] 30
    (.object "Query" 0) schedule result true observation_matches
  exact ⟨bridge.1, bridge.2, by cbv, by cbv, positions_not_addressed⟩

end GraphQL.IncrementalDelivery.Tests.FailureCoverageInputs
