import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GuardHealthCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformanceFailureHistory

/-! Defer-only generated replay has a licensed failure inventory on its exact history. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Defer-only work cannot contribute a stream failure cut to any output history.
Witness: a cut's payload descriptor would locate an item task and hence a stream node.
Neither output admission nor failure licensing is assumed to exclude these cuts.
-/
theorem StreamFailureCuts.eq_nil_of_defer {work events failures}
    (cuts : StreamFailureCuts work events failures) (shape : Correctness.DeferOnly work)
    : failures = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry member
  obtain ⟨stream, errors, producer, _, known⟩ := cuts.2 entry member
  obtain ⟨dependencies, descriptor⟩ := (itemTask_owner_nodeAt known).2
  cases shape _ _ _ _ descriptor

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Three construction leaves now share one explicit defer-only witness
-----------------------------------------------------------------------------------------

/-- The exact defer-only replay satisfies batching, announcements, and prior-cancellation
exclusion on one witness. Witness: the announced mixed inventory has no stream cuts;
general guard reflection licenses its unchanged ordered object cuts. This does not yet
prove publication/control admission or terminal work accounting.
-/
theorem defer_failureCertificates {work : Execution.Work}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    {inputs : List (List GraphEvent)} (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true) (matching : PublicationMatching)
    : let queue := initialQueue work
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let failures :=
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
      let w : Witness := { events := queue.nonterminalAtoms inputs, matching, failures }
      BatchShape work inputs w
      ∧ AnnouncedFailures work w
      ∧ UncancelledFailures work w := by
  obtain ⟨streams, cuts, announced⟩ :=
    announcedFailures_with_cuts_exists generated valid started matching
  have empty := cuts.eq_nil_of_defer shape
  subst streams
  simp only [mergeFailureCuts, List.merge_right] at announced
  exact ⟨batchShape_holds valid matching _, announced,
    uncancelledFailures_of_defer generated shape valid started rfl⟩

/-- Every accepted defer-only failure is licensed at its actual unbatched output cut.
Witness: compose the same-witness announcement and cancellation certificates. Ignored
source failures stay omitted, and equal-cut predecessors remain visible in order.
This theorem covers arbitrary matching because defer causality needs no publication law.
-/
theorem failureWitness_of_defer {work : Execution.Work}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    {inputs : List (List GraphEvent)} (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true) (matching : PublicationMatching)
    : let queue := initialQueue work
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let failures :=
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
      FailureWitness work (initialKeys work) matching (queue.nonterminalAtoms inputs)
        failures := by
  have certificates := defer_failureCertificates generated shape valid started matching
  exact failureWitness certificates.2.1 certificates.2.2

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
