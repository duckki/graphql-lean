import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DeferGuardHealth

/-! Selected failure cuts retain a contributor unaffected by their earlier selected cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Eventwise prefix health remains separate from informative-cut causality
-----------------------------------------------------------------------------------------

/-- Every accepted eventwise prefix retains its historical missing-parent certificate.
This helper uses the explicitly empty supplied snapshot throughout the same event trace.
-/
theorem ExecutedWork.eventwisePrefix_missingParentHealth {work : Execution.Work}
    (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) events = true)
    (received : List GraphEvent) (earlier : received.IsPrefix events)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        received).MissingParentAncestorsHealthy
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          received) := by
  obtain ⟨after, same⟩ := earlier
  exact (generated.replayGraphEvents_retiredHealth received (valid.prefix ⟨after, same⟩)
          (State.eventsStarted_prefix (after := after) (by rwa [same]))).2.2

/-- Each informative object cut has an owner unaffected by earlier record invalidation.
Witness: informative selection excludes invalidation by its ordered predecessors.
Equal-index predecessors and ignored source inputs retain their original order.
-/
theorem ExecutedWork.informativeObjectFailureCuts_uninvalidatedOwner
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (_started : inputsStarted work batches = true) {before after : FailureCuts}
    {cut : Nat} {occurrence : Occurrence}
    (split
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        informativeObjectFailureCuts work (queue.sourceRunBlocks publisher batches).2.2
        = before ++ (cut, occurrence) :: after)
    : ∃ owners ref,
        TaskHasOwners work occurrence owners
        ∧ ref ∈ owners
        ∧ ¬GroupRecordInvalidated work (before.map Prod.snd) ref := by
  have selected := selectObjectFailureCuts_informative work []
    (availableObjectFailureCuts work 0
      ((State.initialize (Work.fromExecution work)).sourceRunBlocks
          { active := (State.initialize (Work.fromExecution work)).initialGroups
            ++ (State.initialize (Work.fromExecution work)).initialStreams } batches).2.2)
  change InformativeFailureCuts work [] (informativeObjectFailureCuts work _) at selected
  rw [split] at selected
  obtain ⟨owners, ref, ⟨producer, payload, task⟩, owner, healthy⟩ := selected.atCut
  simp only [List.nil_append] at healthy
  have member : (cut, occurrence) ∈ informativeObjectFailureCuts work
      ((State.initialize (Work.fromExecution work)).sourceRunBlocks
          { active := (State.initialize (Work.fromExecution work)).initialGroups
            ++ (State.initialize (Work.fromExecution work)).initialStreams } batches).2.2 := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨_, actualOwners, birth, path, errors, actual, _⟩ :=
    createWorkQueue_informativeObjectFailureCuts_origin generated valid _ member
  obtain ⟨address, rfl⟩ := actual.object_occurrence
  obtain ⟨node, dependencies, descriptor, same⟩ := task.executionGroup_owner owner
  refine ⟨owners, ref, ⟨producer, payload, task⟩, owner, ?_⟩
  intro invalid
  apply healthy
  exact same ▸ (generated.groupRecordInvalidated_iff_groupInvalidated descriptor).mp
    (same.symm ▸ invalid)

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- For defer-only work the same certificate excludes every historical failure cause
-----------------------------------------------------------------------------------------

/-- Generated defer-only accepted cuts satisfy the owner-health construction leaf.
Witness: informative selection and defer-only causal reflection supply the owner directly.
The exact cut equation retains the actual inventory, not a more convenient replacement.
-/
theorem failureCutOwnerHealth_of_defer {work : Execution.Work}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    {batches : List (List GraphEvent)} (_valid : ValidGraphEvents work batches.flatten)
    (_started : inputsStarted work batches = true) {w : Witness}
    (exactCuts
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures
        = informativeObjectFailureCuts work (queue.sourceRunBlocks publisher batches).2.2)
    : FailureCutOwnerHealth work w :=
  failureCutOwnerHealth_of_deferInformativeCuts generated shape exactCuts

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
        = informativeObjectFailureCuts work (queue.sourceRunBlocks publisher batches).2.2)
    : UncancelledFailures work w :=
  uncancelledFailures_of_deferOwnerHealth generated shape
    (failureCutOwnerHealth_of_defer generated shape valid started exactCuts)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
