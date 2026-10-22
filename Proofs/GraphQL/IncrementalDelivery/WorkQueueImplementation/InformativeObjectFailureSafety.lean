import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MixedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulItemCertificates

/-! Informative object failure cuts are licensed by source readiness and item safety. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every informative object cut is uncancelled under its exact mixed predecessors.
Witness: selection supplies a record-uninvalidated contributor; source registration
exposes its region. Historical cancellation would invalidate that owner by the independent
item-safety bridge, without an executable health guard or a producer-publication premise.
-/
theorem informativeObjectFailures_uncancelled {work inputs w streams}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (announced : AnnouncedFailures work w)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (cuts
      : StreamFailureCuts work
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streams)
    (exactCuts
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures
        = mergeFailureCuts
            (informativeObjectFailureCuts work
              (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2))
            streams)
    : ∀ before cut address after,
        w.failures = before ++ (cut, .executionGroup address) :: after
        → ¬TaskCancelled work w.matching (w.events.take cut) before
            (.executionGroup address) := by
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := informativeObjectFailureCuts work
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
  have objectsKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨_, owners, producer, path, errors, known, _⟩ :=
      createWorkQueue_informativeObjectFailureCuts_origin generated valid entry member
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
  have rawMember := (informativeObjectFailureCuts_sublist work _).subset selectedMember
  obtain ⟨rawBefore, rawAfter, rawSplit⟩ := List.mem_iff_append.mp rawMember
  obtain ⟨earlier, _, errors, _, node, _, _, _, sourcePrefix, priorValid, _, _, ledger,
    found⟩ := createWorkQueue_eligibleObjectFailureCuts_split valid started rawSplit
  have priorPrefix : (earlier.filterMap Prod.fst).IsPrefix inputs.flatten :=
    (List.prefix_append _ _).trans sourcePrefix
  have accepted := queue.batchesStarted_acceptsBatch inputs
    (by rwa [← inputsStarted_eq_batchesStarted])
  have priorAccepted : queue.acceptsBatch (earlier.filterMap Prod.fst) = true := by
    obtain ⟨suffix, same⟩ := priorPrefix
    rw [← same] at accepted
    exact State.acceptsBatch_prefix accepted
  have bookkeeping := (createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated (earlier.filterMap Prod.fst) priorValid priorAccepted
  obtain ⟨nodeMember, occurrenceEq⟩ := State.taskNode?_some found
  have registeredTask := bookkeeping.started node nodeMember
  obtain ⟨⟨_, payload, producer, _, task⟩, _⟩ :=
    bookkeeping.matching node.task registeredTask
  have task : TaskAt work (.executionGroup address)
      (node.task.groups.map Execution.DeliveryNode.ref) producer payload := occurrenceEq ▸ task
  obtain ⟨objectOwners, objectProducer, objectPath, objectErrors, objectTask⟩ :=
    objectsKnown _ selectedMember
  obtain ⟨healthyOwners, owner, ⟨birth, value, ownerTask⟩, contributes, recordHealthy⟩ :=
    createWorkQueue_mixedFailureCuts_uninvalidatedObjectOwner generated valid started
      (fun received earlierPrefix => (generated.replayGraphEvents_retiredHealth received
        (valid.prefix earlierPrefix) (by
          obtain ⟨suffix, same⟩ := earlierPrefix
          apply State.acceptsBatch_prefix (after := suffix)
          simpa only [← same] using accepted)).2.2)
      cuts objectTask (exactCuts.symm.trans split)
  have owns : owner ∈ node.task.groups.map Execution.DeliveryNode.ref :=
    (ownerTask.unique task).1 ▸ contributes
  obtain ⟨group, dependencies, descriptor, refEq⟩ := task.executionGroup_owner owns
  have ownerHealthy : ¬NodeFailed work w.matching (w.events.take cut) before owner := by
    intro failure
    have exposed := (createWorkQueue_replay_regionInventory priorValid).registered_exposed
      (refEq.symm ▸ bookkeeping.taskGroups node.task registeredTask owner owns)
    have invalid := generated.exposed_groupFailure_invalidated priorValid descriptor exposed
      failedPayloads (safe.prefix priorPrefix cut included) (refEq.symm ▸ failure)
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
  apply valid.groupSettlement_producerBefore task
  apply List.mem_flatMap.mpr
  refine ⟨
    .taskFailure (.executionGroup address) errors,
    ?_,
    by simp [GraphEvent.identities]
  ⟩
  exact sourcePrefix.subset (List.mem_append_right _ List.mem_cons_self)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
