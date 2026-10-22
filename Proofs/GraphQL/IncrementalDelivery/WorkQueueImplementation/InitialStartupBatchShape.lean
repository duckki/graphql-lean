import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformanceBatchShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupSourceFrames

/-! Startup-aware actual output retains exact batching and one optional terminal suffix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial activation leaves termination to the first supplied batch, including failure startup. -/
theorem State.initializeWithStartup_terminated (work : Work) (startup : InitialStartup)
    : (State.initialize work startup).terminated = false := by
  unfold State.initialize
  dsimp only [State.enqueueGroupFailures]
  rw [State.startNewWork_terminated _ _ startup.failures, State.pruneEmptyGroups_terminated,
    State.maybeIntegrateWork_terminated]

/-- The startup-aware factory's admitted output regroups into its exact atomic history.
Only the terminal suffix is removed in the nonterminal projection; all initial aggregate
reports remain in the history. This proves output shape without assuming event admission.
-/
theorem startup_source_batchShape {work startup} {source : EventSource (List GraphEvent)}
    (valid : source.ValidFor work startup) {inputs}
    (admitted : source.admissible inputs)
    : let initial := State.initialize (Work.fromExecution work) startup
      WorkBatching
        (initial.nonterminalAtoms inputs
          ++ if (initial.runNormalized inputs).1.terminated then
                [.workQueueTermination]
              else
                [])
        (initial.runNormalized inputs).2 := by
  have checked := valid.admittedProperties admitted
  exact State.runNormalized_batchShape _ inputs (State.initializeWithStartup_terminated _ startup)
    checked.1.nonemptyItems

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
