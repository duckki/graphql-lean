import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalFailureOrigins
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalStreamReporting

/-! Unpublished released object tasks have covering actual failure completions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Permanent registration connects root exhaustion to failure origins
-----------------------------------------------------------------------------------------

/-- Every unpublished registered object task has a covering positive failure completion.
Witness: healthy contributor retirement would publish it on the common matching. Otherwise
each contributor is invalidated, and the actual accepted inventory supplies a terminal
report for one of its owners or full defer ancestors. Generated paths cover the attachment.
No terminal reporting or response coverage law is assumed.
-/
theorem terminal_registeredTask_reported {work inputs task} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (member : task ∈ ((initialQueue work).replayGraphEvents inputs.flatten).tasks)
    (unpublished : ¬Published w.matching w.events task.occurrence)
    {address owners producer payload}
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (identity : task.occurrence = .executionGroup address)
    : FailureReportedFor w.events payload.path := by
  classical
  have matched := (createWorkQueue_replay_regionInventory valid).matching task member
  obtain ⟨_, stored, birth, sameOccurrence, structural⟩ := matched.1
  by_cases healthyOwner :
    ∃ ref ∈ task.groups.map Execution.DeliveryNode.ref,
      ¬GroupInvalidated work
        ((initialQueue work).objectFailureContributions inputs.flatten) ref
  · obtain ⟨ref, contributes, healthy⟩ := healthyOwner
    have retired := generated.terminal_healthyContributor_retired valid started ended
      member contributes healthy
    have recordHealthy := matched.contributor_recordHealthy generated contributes healthy
    have delivered := retiredGroup_contributorPublished generated valid started history ledger
      (sameOccurrence ▸ structural) contributes retired recordHealthy
    exact False.elim (unpublished (sameOccurrence.symm ▸ delivered))
  · have structuralAt := structural
    rw [identity] at structuralAt
    have sameOwners := (TaskAt.unique structuralAt known).1
    obtain ⟨ref, contributes⟩ :=
      List.exists_mem_of_ne_nil owners (generated.taskOwners_nonempty known)
    have invalid : GroupInvalidated work
        ((initialQueue work).objectFailureContributions inputs.flatten) ref := by
      apply Classical.byContradiction
      intro healthy
      exact healthyOwner ⟨ref, sameOwners.symm ▸ contributes, healthy⟩
    obtain ⟨owner, dependencies, descriptor, sameRef⟩ := known.executionGroup_owner contributes
    have report := terminal_invalidatedRecord_reported generated valid started history ended
      (groupRecordAt_of_nodeAt descriptor) (sameRef.symm ▸ invalid.toRecordInvalidated)
    exact generated.groupReport_covers_task explained known descriptor
      (sameRef.symm ▸ contributes) report

-----------------------------------------------------------------------------------------
-- Root and published producers expose the complete released object frontier
-----------------------------------------------------------------------------------------

/-- Every unpublished released execution-group task is covered by an actual report.
Witness: root lowering or a published producer's accepted success registers the task;
registered-task reporting then applies to the same concrete history and publication match.
-/
theorem terminal_availableObjectTaskReporting {work inputs w}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    : AvailableObjectTaskReporting work w := by
  intro address owners producer payload known available unpublished
  have registered : ∃ task ∈ ((initialQueue work).replayGraphEvents inputs.flatten).tasks,
      task.occurrence = .executionGroup address
      ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
    cases producer with
    | none => exact TaskAt.executionGroup_replay_registered known inputs.flatten
    | some parent =>
        cases parent with
        | executionGroup source =>
            exact published_object_child_registered generated valid started history admitted
              ledger known (available _ rfl)
        | item source index =>
            have accepted : (initialQueue work).batchesStarted inputs = true := by
              rwa [← inputsStarted_eq_batchesStarted]
            exact TaskAt.executionGroup_registered_of_itemSuccess known valid
              ((initialQueue work).batchesStarted_acceptsBatch inputs accepted)
              (published_item_success valid started history admitted ledger
                (available _ rfl))
  obtain ⟨task, member, identity, _⟩ := registered
  exact terminal_registeredTask_reported generated valid started history ledger explained
    ended member (identity.symm ▸ unpublished) known identity

/-- Actual terminal replay reports every unpublished task's attachment path.
Witness: registered object reporting, completed stream reporting, and structural producer
inheritance jointly construct the eighth conformance leaf on the unchanged witness.
-/
theorem terminal_cancellationReporting {work inputs w}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    : CancellationReporting work w :=
  cancellationReporting_of_availableObjectTaskReporting generated valid started history
    admitted ledger explained ended
    (terminal_availableObjectTaskReporting generated valid started history admitted ledger
      explained ended)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
