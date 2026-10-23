import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InformativeObjectFailureSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeContributorSources

/-! Selected startup object failures are licensed against their exact mixed predecessors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial selected causes are producer-free root failures. Later causes use permanent registration
in the actual retained source replay. The same uninvalidated owner and successful-item safety exclude
prior cancellation in either case, without an additional runtime cause cache.
-/
theorem startup_informativeObjectFailures_uncancelled {work inputs w streams}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (announced : AnnouncedFailures work w)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work) startup).runNormalized
              inputs).2.flatten.flatMap
            publicationAtoms)
          streams)
    (exactCuts
      : w.failures
        = mergeFailureCuts (startup.informativeObjectFailureCuts work inputs) streams)
    : ∀ before cut address after,
        w.failures = before ++ (cut, .executionGroup address) :: after
        → ¬TaskCancelled work w.matching (w.events.take cut) before
            (.executionGroup address) := by
  let objects := startup.informativeObjectFailureCuts work inputs
  have objectsKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨owners, producer, path, errors, known⟩ :=
      startup.objectReportingCuts_objectOrigin matched generated valid entry
        ((selectObjectFailureCuts_sublist work [] _).subset member)
    exact ⟨owners, producer, path, errors, known⟩
  intro before cut address after split
  have included : before.Subset w.failures := by
    rw [split]
    exact List.subset_append_left _ _
  have failedPayloads : ∀ index occurrence,
      (index, occurrence) ∈ before
      → ∃ owners producer payload,
          TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true :=
    fun index occurrence member =>
      (announced.1.2.2.1 (index, occurrence) (included member)).2.2
  obtain ⟨prior, later, objectSplit, retained⟩ :=
    mixedFailureCuts_objectPrefix objectsKnown cuts (exactCuts.symm.trans split)
  have selectedMember : (cut, .executionGroup address) ∈ objects := by
    rw [objectSplit]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨objectOwners, objectProducer, objectPath, objectErrors, objectTask⟩ :=
    objectsKnown _ selectedMember
  obtain ⟨healthyOwners, owner, ⟨birth, value, ownerTask⟩, contributes, recordHealthy⟩ :=
    mixedFailureCuts_uninvalidatedObjectOwner generated objectsKnown
      (selectObjectFailureCuts_informative work [] _) cuts objectTask (exactCuts.symm.trans split)
  have provenance := startup.informativeObjectFailureCuts_source_subset work inputs cut
    (mem_failedBefore selectedMember (Nat.le_refl _))
  rcases List.mem_append.mp provenance with early | recorded
  · obtain ⟨⟨occurrence, errors⟩, supplied, same⟩ := List.mem_map.mp early
    dsimp only at same
    subst occurrence
    obtain ⟨owners, path, root⟩ := InitialStartup.matched_rootFailure matched supplied
    exact generated.rootTask_uncancelled root
      ⟨healthyOwners, owner, ⟨birth, value, ownerTask⟩, contributes,
        fun invalid => recordHealthy invalid.toRecordInvalidated⟩
  · obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
    have bookkeeping := generated.startup_runNormalized_frame canonical startup matched
      inputs valid started
    obtain ⟨candidate, registeredTask, occurrenceEq⟩ := bookkeeping.failures _ recorded
    obtain ⟨⟨_, payload, producer, _, task⟩, _⟩ :=
      bookkeeping.pending.matching candidate registeredTask
    have task : TaskAt work (.executionGroup address)
        (candidate.groups.map Execution.DeliveryNode.ref) producer payload := occurrenceEq ▸ task
    have owns : owner ∈ candidate.groups.map Execution.DeliveryNode.ref :=
      (ownerTask.unique task).1 ▸ contributes
    obtain ⟨group, dependencies, descriptor, refEq⟩ := task.executionGroup_owner owns
    have ownerHealthy : ¬NodeFailed work w.matching (w.events.take cut) before owner := by
      intro failure
      have exposed := bookkeeping.regions.registered_exposed
        (refEq.symm ▸ bookkeeping.pending.taskGroups candidate registeredTask owner owns)
      have invalid := generated.exposed_groupFailure_invalidated valid descriptor exposed
        failedPayloads (safe.prefix (List.prefix_refl _) cut included) (refEq.symm ▸ failure)
      apply recordHealthy (refEq ▸ invalid.toRecordInvalidated.mono ?_)
      intro token recorded
      obtain ⟨entry, selected, same⟩ := List.mem_map.mp recorded
      exact List.mem_map.mpr ⟨entry, (List.mem_filter.mp selected).1, same⟩
    intro cancelled
    apply ownerHealthy
    apply generated.object_cancelled_owner_failed_of_itemSafety valid failedPayloads
      (safe.prefix (List.prefix_refl _) cut included) task owns _ cancelled
    intro source same
    subst producer
    exact valid.groupSettlement_producerBefore task
      (GraphEvent.failureSettlements_subsetIdentities inputs.flatten recorded)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
