import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamEventAdmission
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Actual exhausted streams obey successful completion admission without item patches. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerEmptyCompletion
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- An initially announced empty stream still has an admitted completion
-----------------------------------------------------------------------------------------

namespace Root

private def node : DeliveryNode := { ref := 0, path := [.field "empty"] }
private def selections : List Selection := [field "empty" [] [.stream]]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def inputs : List (List GraphEvent) := [[.streamSuccess node]]

/-- Empty streaming work is retained by actual query execution.
Witness: the executor's exact work projection, not a raw synthetic stream tree.
-/
private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- The already exhausted source can close immediately with a fresh identity.
Witness: its located empty list satisfies the exact cursor and start checks.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have located : Located work [0, 0, 1] (.stream node []) none [] := by cbv
  refine ⟨.append .nil ⟨[], none, ⟨_, _, located⟩⟩ ?_ ?_, by cbv⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, _, located,
      (by intro source impossible; cases impossible), rfl⟩

/-- The initial empty stream has an admitted success with no value atom.
Witness: the shared general construction produces exactly its completion, retaining
the same batching and licensed failure witness as successful stream admission.
-/
theorem completion_admitted
    : ∃ w : ConformancePlan.Witness,
        w.events = [.streamSuccess node]
        ∧ ConformancePlan.BatchShape work inputs w
        ∧ FailureWitness work (ConformancePlan.initialRefs work)
            w.matching w.events w.failures
        ∧ ConformancePlan.StreamSuccessAdmission work w := by
  obtain ⟨w, history, shape, announced, uncancelled, _, successful⟩ :=
    ConformancePlan.streamAndFailureAdmission_certificates generated source_valid.1 source_valid.2
  refine ⟨w, ?_, shape, ConformancePlan.failureWitness announced uncancelled, successful⟩
  rw [history]
  cbv

end Root

-----------------------------------------------------------------------------------------
-- A successful deferred task releases an empty stream before it closes
-----------------------------------------------------------------------------------------

namespace ObjectProduced

private def selections : List Selection := [defer [field "empty" [] [.stream]]]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def group : DeliveryNode := { ref := 0, path := [] }
private def stream : DeliveryNode := { ref := 1, path := [.field "empty"] }
private def producer : Occurrence := .executionGroup [1, 0]

private def children : Execution.Work :=
  .combine (.combine .empty (.stream stream [])) .empty

private def value : ExecutionGroupValue :=
  { deliveryGroups := [group], path := [], data := [("empty", .list [])] }

private def first : GraphEvent :=
  .taskSuccess producer { value, work := Work.fromExecution children [1, 0, 0] }

private def inputs : List (List GraphEvent) := [[first], [.streamSuccess stream]]

/-- The deferred empty-stream fixture is actual generated work.
Witness: the root executor equation for a deferred streaming field.
-/
private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- Source completion waits for the deferred producer but requires no stream items.
Witness: exact task lowering, child location, prior success, and executable start checks.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have parent : TaskAt work producer [group.ref] none (.object [] (.ok (value.data, 0))) :=
    .executionGroup (groups := [⟨group, []⟩]) (children := children) (owners := []) (by cbv)
  have located : Located work [1, 0, 0, 0, 1]
      (.stream stream []) (some producer) [group.ref] := by cbv
  have prior : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, parent, by cbv, by cbv⟩
      (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, parent, by intro source impossible; cases impossible⟩
  refine ⟨.append prior ⟨[group.ref], some producer, ⟨_, _, located⟩⟩ ?_ ?_, by cbv⟩
  · simp [first, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, _, located,
      (by intro source same; cases same; simp [first, GraphEvent.successes]), rfl⟩

/-- The empty produced stream has an admitted completion after its defer owner retires.
Witness: one canonical witness retains producer publication and child announcement;
successful stream admission derives health and empty accounting at the final boundary.
-/
theorem completion_admitted
    : ∃ w : ConformancePlan.Witness,
        w.events
          = [
            .groupValues group
              [{
                path := [],
                data := value.data,
                errors := 0,
                deliveryGroups := value.deliveryGroups
              }],
            .groupSuccess group [] [stream],
            .streamSuccess stream
          ]
        ∧ ConformancePlan.BatchShape work inputs w
        ∧ FailureWitness work (ConformancePlan.initialRefs work)
            w.matching w.events w.failures
        ∧ ConformancePlan.StreamSuccessAdmission work w := by
  obtain ⟨w, history, shape, announced, uncancelled, _, successful⟩ :=
    ConformancePlan.streamAndFailureAdmission_certificates generated source_valid.1 source_valid.2
  refine ⟨w, ?_, shape, ConformancePlan.failureWitness announced uncancelled, successful⟩
  rw [history]
  cbv

end ObjectProduced
end GraphQL.IncrementalDelivery.Tests.WorkSchedulerEmptyCompletion
