import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformancePlan
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationCausality

/-! Smaller failure-licensing obligations, without assuming output admission. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Producer success is structural; producer publication is not required
-----------------------------------------------------------------------------------------

/-- A reachable child has a successful structural producer, published or not.
Witness: invert reachability and identify the unique producer descriptor.
-/
theorem reachable_producer_succeeds {work occurrence producer}
    (reachable : Reachable work occurrence)
    (known : TaskHasProducer work occurrence (some producer))
    : TaskSucceeds work producer := by
  obtain ⟨owners, payload, task⟩ := known
  cases reachable with
  | root other =>
      obtain ⟨_, _, descriptor⟩ := other
      cases (task.unique descriptor).2.1
  | child other success _ =>
      obtain ⟨_, _, descriptor⟩ := other
      have same := Option.some.inj (task.unique descriptor).2.1
      exact same.symm ▸ success

/-- A fixed successful task cannot occur in a genuine failure inventory at any cut.
Witness: membership supplies a failed descriptor, contradicting payload uniqueness.
-/
theorem taskSucceeds_not_failedBefore {work failures occurrence cut}
    (success : TaskSucceeds work occurrence)
    (failedPayloads
      : ∀ index task,
          (index, task) ∈ failures
          → ∃ owners producer payload,
              TaskAt work task owners producer payload ∧ payload.failure.isSome = true)
    : occurrence ∉ failedBefore failures cut := by
  obtain ⟨owners, producer, payload, known, succeeds⟩ := success
  intro failed
  obtain ⟨entry, kept, same⟩ := List.mem_map.mp failed
  obtain ⟨_, _, other, descriptor, fails⟩ :=
    failedPayloads entry.1 entry.2 (List.mem_filter.mp kept).1
  rw [same] at descriptor
  rw [← (known.unique descriptor).2.2, succeeds] at fails
  cases fails

/-- A reachable task with a healthy owner and uncancelled producer is uncancelled.
Witness: inspect the original cancellation cut directly. Owner cancellation contradicts
health at that cut; producer failure contradicts its fixed success; producer cancellation
contradicts the supplied historical safety. No publication-support premise is needed.
-/
theorem task_uncancelled_of_producerSafety
    {work matching events failures occurrence owners producer payload key}
    (failedPayloads
      : ∀ cut task,
          (cut, task) ∈ failures
          → ∃ owners producer payload,
              TaskAt work task owners producer payload ∧ payload.failure.isSome = true)
    (reachable : Reachable work occurrence)
    (known : TaskAt work occurrence owners producer payload) (owner : key ∈ owners)
    (healthy : ¬NodeFailed work matching events failures key)
    (safe
      : ∀ source,
          producer = some source → ¬TaskCancelled work matching events failures source)
    : ¬TaskCancelled work matching events failures occurrence := by
  rintro ⟨cut, member, reached, cancelled⟩
  cases cancelled with
  | owners other _ _ failed =>
      obtain ⟨_, _, descriptor⟩ := other
      exact healthy ⟨cut, member, reached,
        failed key ((known.unique descriptor).1 ▸ owner)⟩
  | producerFailed other _ failed =>
      exact taskSucceeds_not_failedBefore
        (reachable_producer_succeeds reachable other) failedPayloads failed
  | producerCancelled other _ cancelled =>
      obtain ⟨_, _, descriptor⟩ := other
      exact safe _ (known.unique descriptor).2.1 ⟨cut, member, reached, cancelled⟩

-----------------------------------------------------------------------------------------
-- A failure can settle safely without ever publishing a successful value
-----------------------------------------------------------------------------------------

/-- Removing failure cuts preserves publication support. Witness: any newly claimed
owner failure would also be a failure under the original, larger cut inventory.
-/
theorem PublicationSupport.restrict_failures {work matching events failures earlier}
    (support : PublicationSupport work matching events failures)
    (included : earlier.Subset failures)
    : PublicationSupport work matching events earlier := by
  intro index event selected value
  obtain ⟨owners, producer, payload, key, known, success, owner, healthy, ready⟩ :=
    support index event selected value
  exact ⟨owners, producer, payload, key, known, success, owner,
    fun failure => healthy (failure.mono included), ready⟩

/-- Any task with a healthy owner and an already-published producer is uncancelled
under supported earlier publications. Its own outcome may be a failure. Witness:
transport cancellation to the current snapshot, then exclude owner cancellation,
failed producers, and cancelled producers separately. No event admission is assumed.
-/
theorem PublicationSupport.task_uncancelled
    {work matching events failures occurrence owners producer payload key}
    (support : PublicationSupport work matching events failures)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (known : TaskAt work occurrence owners producer payload) (owner : key ∈ owners)
    (healthy : ¬NodeFailed work matching events failures key)
    (ready : ∀ source, producer = some source → Published matching events source)
    : ¬TaskCancelled work matching events failures occurrence := by
  intro cancelled
  cases support.taskCancelled_snapshot failedPayloads cancelled with
  | owners other _ _ failed =>
      obtain ⟨_, _, descriptor⟩ := other
      have same := (known.unique descriptor).1
      exact healthy (support.snapshot_nodeFailed failedPayloads (failed key (same ▸ owner)))
  | producerFailed other _ failed =>
      obtain ⟨_, _, descriptor⟩ := other
      exact support.failed_unpublished failedPayloads failed
        (ready _ (known.unique descriptor).2.1)
  | producerCancelled other _ cancelled =>
      obtain ⟨_, _, descriptor⟩ := other
      exact cancelled.unpublished (ready _ (known.unique descriptor).2.1)

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Two cut-local safety obligations beneath UncancelledFailures
-----------------------------------------------------------------------------------------

/-- Admitted value atoms already supply the weaker publication-support certificate.
Witness: extract each exact successful payload, healthy contributing owner, and ready
producer; the event-start cut filter does not change earlier historical failures.
No failure licensing or control-event admission is used in this direction.
-/
theorem publicationSupport_of_publicationAdmission {work w}
    (publications : PublicationAdmission work w)
    : PublicationSupport work w.matching w.events w.failures := by
  intro index event selected value
  have allowed := publications index event selected value
  have within := (List.getElem?_eq_some_iff.mp selected).1
  have length : (w.events.take index).length = index := by
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt within)]
  have filtered := nodeFailed_filter (work := work) (matching := w.matching)
    (events := w.events.take index) (failures := w.failures) (Nat.le_refl _)
  cases event with
  | groupValues node values =>
      obtain ⟨owners, producer, ⟨path, data, errors, deliveryGroups⟩, _, known, ready, owner⟩ := allowed
      obtain ⟨supporter, available⟩ := owner.2.1
      refine ⟨owners, producer, .object path (.ok (data, errors)), supporter.key,
        ?_, rfl, available.1.2.1, ?_, ready.2.2.1⟩
      · simpa only [length] using known
      · simpa only [filtered] using available.2
  | streamValues node values groups streams =>
      obtain ⟨owners, producer, ⟨item, errors⟩, _, known, ready, owner, _⟩ := allowed
      obtain ⟨supporter, available⟩ := owner.2.1
      refine ⟨owners, producer, .item node (.ok (item, errors)), supporter.key,
        ?_, rfl, available.1.2.1, ?_, ready.2.2.1⟩
      · simpa only [length] using known
      · simpa only [filtered] using available.2
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases value

/-- Each accepted settlement has a contributing owner that has not failed under its
ordered predecessor cuts. The owner need not still be open or be the licensing owner.
-/
def FailureCutOwnerHealth (work : Execution.Work) (w : Witness) : Prop :=
  ∀ before cut occurrence after,
    w.failures = before ++ (cut, occurrence) :: after
    → ∃ owners key,
        TaskHasOwners work occurrence owners
        ∧ key ∈ owners
        ∧ ¬NodeFailed work w.matching (w.events.take cut) before key

/-- A settling task's producer has not been cancelled by earlier cuts, even if its
successful value is still buffered. Producer success follows separately from the complete
inventory's reachability certificate. Root tasks impose no producer obligation.
-/
def FailureCutProducerSafety (work : Execution.Work) (w : Witness) : Prop :=
  ∀ before cut occurrence after,
    w.failures = before ++ (cut, occurrence) :: after
    → ∀ producer,
        TaskHasProducer work occurrence (some producer)
        → ¬TaskCancelled work w.matching (w.events.take cut) before producer

/-- Owner health and producer safety discharge earlier-cancellation exclusion.
Witness: the complete inventory supplies genuine failures and successful producer chains;
direct cut inversion excludes cancellation without assuming producer publication or
publication support. Equal-index predecessors remain in their original order.
-/
theorem uncancelledFailures_of_cutSafety {work w}
    (inventory : CompleteFailureInventory work w.events w.failures)
    (owners : FailureCutOwnerHealth work w) (producers : FailureCutProducerSafety work w)
    : UncancelledFailures work w := by
  intro before cut occurrence after split
  obtain ⟨ownerKeys, key, ⟨producer, payload, known⟩, owner, healthy⟩ :=
    owners before cut occurrence after split
  have member : (cut, occurrence) ∈ w.failures := by simp [split]
  have reachable := (inventory.2.2.1 _ member).2.1
  refine task_uncancelled_of_producerSafety ?_ reachable known owner healthy ?_
  · intro prior failed member
    have included : (prior, failed) ∈ w.failures := by
      rw [split]
      exact List.mem_append_left _ member
    obtain ⟨_, _, descriptor⟩ := inventory.2.2.1 _ included
    exact descriptor
  · intro source same
    exact producers before cut occurrence after split source ⟨ownerKeys, payload, same ▸ known⟩

/-- Prior announcements and cut-local safety give a licensed failure inventory.
Witness: compose the checked cancellation reduction with the announced-inventory
equivalence. Constructing these cut-local facts from arbitrary replay remains open.
-/
theorem failureWitness_of_cutSafety {work w}
    (announced : AnnouncedFailures work w)
    (owners : FailureCutOwnerHealth work w) (producers : FailureCutProducerSafety work w)
    : FailureWitness work (initialKeys work) w.matching w.events w.failures :=
  failureWitness announced (uncancelledFailures_of_cutSafety announced.1 owners producers)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
