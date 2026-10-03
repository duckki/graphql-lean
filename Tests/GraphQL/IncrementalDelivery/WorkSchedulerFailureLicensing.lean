import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureLicensing

/-! Failed tasks need no value publication; equal-cut predecessors still cancel work. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerFailureLicensing
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def stream : Execution.DeliveryNode := { ref := 0, path := [] }

private def work : Execution.Work :=
  .stream stream [(.error 1, .empty), (.error 2, .empty)]

private def first : Occurrence := .item [] 0
private def second : Occurrence := .item [] 1
private def matching : PublicationMatching := fun _ => first
private def single : Witness := ⟨[], matching, [(0, first)]⟩
private def pair : Witness := ⟨[], matching, [(0, first), (0, second)]⟩

private theorem first_known
    : TaskAt work first [stream.ref] none (.item stream (.error 1)) :=
  .item (by rfl) rfl

private theorem second_known
    : TaskAt work second [stream.ref] none (.item stream (.error 2)) :=
  .item (by rfl) rfl

private theorem singleton_split {before after : FailureCuts} {cut occurrence}
    (split : single.failures = before ++ (cut, occurrence) :: after)
    : before = [] ∧ cut = 0 ∧ occurrence = first ∧ after = [] := by
  have sizes := congrArg List.length split
  simp only [single, List.length_cons, List.length_nil, List.length_append] at sizes
  have empty : before = [] := List.length_eq_zero_iff.mp (by omega)
  subst before
  change [(0, first)] = (cut, occurrence) :: after at split
  simp only [List.cons.injEq, Prod.mk.injEq] at split
  exact ⟨rfl, split.1.1.symm, split.1.2.symm, split.2.symm⟩

/-- The first item failure has an announced owner and a complete zero-output inventory.
Witness: the concrete initial stream notice and its exact fixed failed payload. This
is an isolated cut-licensing fixture, not a claim of complete replay conformance.
-/
theorem single_announced : AnnouncedFailures work single := by
  constructor
  · refine ⟨by simp [single], by simp [single], ?_, ?_, ?_⟩
    · intro entry member
      have same : entry = (0, first) := List.mem_singleton.mp member
      subst entry
      exact ⟨Nat.le_refl _, .root ⟨[stream.ref], _, first_known⟩,
        [stream.ref], none, _, first_known, rfl⟩
    · intro index group errors impossible
      cases impossible
    · intro index node errors impossible
      cases impossible
  · intro entry member
    have same : entry = (0, first) := List.mem_singleton.mp member
    subst entry
    exact ⟨[stream.ref], ⟨none, _, first_known⟩, stream.ref, List.mem_cons_self,
      by decide⟩

/-- No earlier cut threatens the first failing item's owner.
Witness: singleton-list splitting leaves no predecessor failure, even at cut zero.
-/
theorem single_ownerHealthy : FailureCutOwnerHealth work single := by
  intro before cut occurrence after split
  obtain ⟨rfl, rfl, rfl, rfl⟩ := singleton_split split
  refine ⟨[stream.ref], stream.ref, ⟨none, _, first_known⟩, List.mem_cons_self, ?_⟩
  rintro ⟨cut, member, _⟩
  cases member

/-- The root failed item needs no producer publication.
Witness: descriptor uniqueness rules out any nonroot producer for this occurrence.
-/
theorem single_producerSafe : FailureCutProducerSafety work single := by
  intro before cut occurrence after split producer ⟨owners, payload, known⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ := singleton_split split
  have impossible := (known.unique first_known).2.1
  cases impossible

/-- An error-only settlement is licensed without ever publishing its own value.
Witness: compose the two checked cut-local obligations and the announced inventory.
-/
theorem single_licensed
    : FailureWitness work (initialRefs work) single.matching single.events
        single.failures :=
  failureWitness_of_cutSafety single_announced single_ownerHealthy single_producerSafe

/-- A second failure with the same output index sees the first failure, not an empty
past. Witness: the first item cancels the second through their common stream owner.
Distinct occurrences and equal cut positions do not license this extra settlement.
-/
theorem same_cut_second_cancelled : ¬UncancelledFailures work pair := by
  intro safe
  apply safe [(0, first)] 0 second [] rfl
  refine ⟨0, by simp, Nat.le_refl _, ?_⟩
  refine Causality.TaskCancelled.owners ⟨none, _, second_known⟩ ?_ (by simp) ?_
  · rintro ⟨index, event, impossible, _⟩
    cases impossible
  · intro ref member
    have same : ref = stream.ref := List.mem_singleton.mp member
    subst ref
    exact .task ⟨none, _, first_known⟩ List.mem_cons_self (by simp [failedBefore])

/-- The unsafe second settlement is rejected by the owner-health subgoal itself.
Witness: its unique owner has already failed at the earlier equal-index cut.
-/
theorem same_cut_owner_health_rejected : ¬FailureCutOwnerHealth work pair := by
  intro healthy
  obtain ⟨owners, ref, ⟨producer, payload, known⟩, member, safe⟩ :=
    healthy [(0, first)] 0 second [] rfl
  have ownersEq := (known.unique second_known).1
  have same : ref = stream.ref := List.mem_singleton.mp (ownersEq ▸ member)
  subst ref
  exact safe
    (NodeFailed.task first_known List.mem_cons_self (by simp [failedBefore, pair]))

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerFailureLicensing
