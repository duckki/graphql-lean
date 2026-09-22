import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MixedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulItemCertificates

/-! Accepted object failures are safe at their original ordered mixed failure cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- Every accepted object failure in `w` is uncancelled under its ordered predecessors.
This is the object-task part of `UncancelledFailures`; stream failures remain separate.
-/
def ObjectFailuresSafe (work : Execution.Work) (w : Witness) : Prop :=
  ∀ before cut address after,
    w.failures = before ++ (cut, .executionGroup address) :: after
    → ¬TaskCancelled work w.matching (w.events.take cut) before (.executionGroup address)

-----------------------------------------------------------------------------------------
-- General item safety closes the mixed causal gap in the actual object-settlement guard
-----------------------------------------------------------------------------------------

/-- Successful-item safety licenses the object-task part of the same mixed inventory.
Witness: recover the exact pre-settlement queue and ordered object ledger. Its accepting
owner guard implies historical health using item safety restricted from the common
witness. Cancellation of the settling object would fail that owner, even when its
successful producer is still buffered. No producer-publication premise is introduced.
-/
theorem objectFailuresSafe_of_successfulItems {work inputs w streams}
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
            (sourceObjectFailureCuts 0
              (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2))
            streams)
    : ObjectFailuresSafe work w := by
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
  have objectsKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨_, owners, producer, path, errors, known, _⟩ :=
      createWorkQueue_eligibleObjectFailureCuts_origin generated valid entry member
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
  obtain ⟨earlier, _, errors, _, node, _, _, _, sourcePrefix, priorValid, _, _, ledger,
    found, healthy⟩ := createWorkQueue_eligibleObjectFailureCuts_split valid started objectSplit
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
      (node.task.groups.map Execution.DeliveryNode.key) producer payload := occurrenceEq ▸ task
  obtain ⟨owner, contributes, guard⟩ := State.taskHasHealthyOwner_iff.mp healthy
  have owns : owner.key ∈ node.task.groups.map Execution.DeliveryNode.key :=
    List.mem_map.mpr ⟨owner, contributes, rfl⟩
  obtain ⟨group, dependencies, descriptor, keyEq⟩ := task.executionGroup_owner owns
  have ownerHealthy : ¬NodeFailed work w.matching (w.events.take cut) before owner.key := by
    rw [← keyEq]
    apply generated.replayGraphEvents_groupHealthy_of_itemSafety priorValid priorAccepted
      descriptor
      (keyEq.symm ▸ bookkeeping.taskGroups node.task registeredTask owner.key owns)
      (keyEq.symm ▸ guard) failedPayloads
    · intro occurrence owners producer path result known member
      obtain ⟨entry, selected, same⟩ := List.mem_map.mp member
      have preceding := retained entry (List.mem_filter.mp selected).1
        owners producer path result (same.symm ▸ known)
      rw [← ledger, List.mem_reverse]
      exact List.mem_map.mpr ⟨entry, preceding, same⟩
    · exact safe.prefix priorPrefix cut included
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

-----------------------------------------------------------------------------------------
-- The derived safety uses the canonical witness, not a replacement inventory
-----------------------------------------------------------------------------------------

/-- Actual mixed replay has one witness protecting successful items and accepted objects.
Witness: retain the canonical matching and cut partition from the general item theorem,
then discharge object-failure cancellation on those same ordered predecessor cuts.
This projection does not assert stream-failure licensing, admission, or terminal accounting.
-/
theorem objectFailureCertificates {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ SuccessfulItemsSafe work inputs.flatten w
        ∧ ObjectFailuresSafe work w := by
  obtain ⟨w, history, shape, announced, _, _, _, safe, streams, cuts, exactCuts⟩ :=
    successfulItemCertificates_with_cuts generated valid started
  exact ⟨w, history, shape, announced, safe,
    objectFailuresSafe_of_successfulItems generated valid started announced safe cuts exactCuts⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
