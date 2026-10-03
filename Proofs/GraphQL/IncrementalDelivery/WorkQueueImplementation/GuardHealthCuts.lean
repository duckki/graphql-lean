import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DeferGuardHealth

/-! Actual accepted failure cuts inherit the generated replay's proved health boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every actual source prefix supplies the historical guard certificate
-----------------------------------------------------------------------------------------

/-- Every prefix of valid started batches justifies accepting an absent parent.
Witness: restrict the independent source and start laws, then apply joint health replay.
This is derived implementation evidence, not an additional event-source premise.
-/
theorem ExecutedWork.prefix_missingParentHealth {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (received : List GraphEvent) (earlier : received.IsPrefix batches.flatten)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        received).MissingParentAncestorsHealthy
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          received) := by
  have accepted := (State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  have priorValid := valid.prefix earlier
  obtain ⟨after, same⟩ := earlier
  rw [← same] at accepted
  exact (generated.replayGraphEvents_retiredHealth received priorValid
    (State.acceptsBatch_prefix accepted)).2.2

/-- Each accepted object cut has an owner unaffected by earlier record invalidation.
Witness: the cut-to-source-prefix theorem now consumes the proved replay certificate.
Equal-index predecessors and ignored source inputs retain their original order.
-/
theorem ExecutedWork.eligibleObjectFailureCuts_uninvalidatedOwner {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    {before after : FailureCuts} {cut : Nat} {occurrence : Occurrence}
    (split
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
        = before ++ (cut, occurrence) :: after)
    : ∃ owners ref,
        TaskHasOwners work occurrence owners
        ∧ ref ∈ owners
        ∧ ¬GroupRecordInvalidated work (before.map Prod.snd) ref :=
  createWorkQueue_eligibleObjectFailureCuts_uninvalidatedOwner generated valid started
    (generated.prefix_missingParentHealth valid started) split

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- For defer-only work the same certificate excludes every historical failure cause
-----------------------------------------------------------------------------------------

/-- Generated defer-only accepted cuts satisfy the owner-health construction leaf.
Witness: general replay supplies the missing-parent premise of causal guard reflection.
The exact cut equation retains the actual inventory, not a more convenient replacement.
-/
theorem failureCutOwnerHealth_of_defer {work : Execution.Work}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {w : Witness}
    (exactCuts
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures
        = sourceObjectFailureCuts 0
            (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2))
    : FailureCutOwnerHealth work w :=
  failureCutOwnerHealth_of_deferMissingParentHealth generated shape valid started
    (generated.prefix_missingParentHealth valid started) exactCuts

/-- No accepted defer-only failure is already cancelled at its exact ordered cut.
Witness: the proved owner-health leaf and generated defer dependency continuity.
No output-admission, producer-publication, or queue-health premise is assumed.
-/
theorem uncancelledFailures_of_defer {work : Execution.Work}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {w : Witness}
    (exactCuts
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures
        = sourceObjectFailureCuts 0
            (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2))
    : UncancelledFailures work w :=
  uncancelledFailures_of_deferOwnerHealth generated shape
    (failureCutOwnerHealth_of_defer generated shape valid started exactCuts)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
