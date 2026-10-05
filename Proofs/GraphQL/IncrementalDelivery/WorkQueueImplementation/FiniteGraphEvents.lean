import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegisteredTasks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories

/-! Finite settlement budgets for the host source, independent of queue accounting. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every settlement consumes an execution-derived identity
-----------------------------------------------------------------------------------------

/-- Every settled task/item has a token in the original finite work.
Witness: exact payload matching recovers its structural task occurrence.
-/
theorem GraphEvent.MatchesWork.taskIdentity_token {work event}
    (matching : GraphEvent.MatchesWork work event) {occurrence}
    (member : occurrence ∈ event.identities.1)
    : Sum.inl occurrence ∈ observationTokens [] work := by
  cases event with
  | taskSuccess task result =>
      simp only [GraphEvent.identities, List.mem_singleton] at member
      subst occurrence
      obtain ⟨_, _, known, _, _⟩ := matching
      exact known.observationToken
  | taskFailure task errors =>
      simp only [GraphEvent.identities, List.mem_singleton] at member
      subst occurrence
      obtain ⟨_, _, _, known⟩ := matching
      exact known.observationToken
  | streamItems stream items =>
      obtain ⟨item, included, rfl⟩ := List.mem_map.mp member
      obtain ⟨_, _, known, _⟩ := matching item included
      exact known.observationToken
  | streamSuccess | streamFailure => simp [GraphEvent.identities] at member

/-- Every closed stream has a token in the original finite work.
Witness: success names a known stream; failure names its located stream boundary.
-/
theorem GraphEvent.MatchesWork.streamIdentity_token {work event}
    (matching : GraphEvent.MatchesWork work event) {ref}
    (member : ref ∈ event.identities.2)
    : Sum.inr ref ∈ observationTokens [] work := by
  cases event with
  | taskSuccess | taskFailure | streamItems => simp [GraphEvent.identities] at member
  | streamSuccess stream =>
      simp only [GraphEvent.identities, List.mem_singleton] at member
      subst ref
      obtain ⟨_, _, known⟩ := matching
      exact known.observationToken
  | streamFailure stream errors =>
      simp only [GraphEvent.identities, List.mem_singleton] at member
      subst ref
      obtain ⟨address, items, producer, dependencies, located, _⟩ := matching
      exact (show NodeAt work stream .stream dependencies producer from
        ⟨address, items, located⟩).observationToken

/-- A ready graph event consumes at least one task/item or stream-closure identity.
Witness: all constructors carry one identity except item batches, which Ready makes
nonempty. Empty host batches cannot spend this budget.
-/
theorem GraphEvent.Ready.identities_nonempty {work before event}
    (ready : GraphEvent.Ready work before event)
    : 0 < event.identities.1.length + event.identities.2.length := by
  cases event with
  | taskSuccess | taskFailure | streamSuccess | streamFailure =>
      simp [GraphEvent.identities]
  | streamItems stream items =>
      obtain ⟨_, _, _, _, _, nonempty, _⟩ := ready
      simpa [GraphEvent.identities] using List.length_pos_iff.mpr nonempty

-----------------------------------------------------------------------------------------
-- Source validity bounds the total number of observed settlements
-----------------------------------------------------------------------------------------

/-- The number of received events is bounded by their consumed identities.
Witness: append induction; each ready event adds at least one identity.
-/
theorem ValidGraphEvents.length_le_identities {work events}
    (valid : ValidGraphEvents work events)
    : events.length
      ≤ (events.flatMap (fun event => event.identities.1)).length
        + (events.flatMap (fun event => event.identities.2)).length := by
  induction valid with
  | nil => simp
  | @append before event _ _ _ ready ih =>
      have positive := ready.identities_nonempty
      simp only [List.length_append, List.length_singleton, List.flatMap_append,
        List.flatMap_singleton] at ⊢
      omega

/-- Valid host histories have a fixed finite bound, without any completion assumption.
Witness: fresh task and stream identities are separately duplicate-free subsets of the
finite work-token inventory. The deliberately loose factor two avoids requiring unique
node descriptors or a combined identity representation.
-/
theorem ValidGraphEvents.length_le_budget {work events}
    (valid : ValidGraphEvents work events)
    : events.length ≤ 2 * (observationTokens [] work).length := by
  have unique := valid.identities_nodup
  have taskSubset : ((events.flatMap (fun event => event.identities.1)).map
      (Sum.inl : Occurrence → ObservationToken)).Subset (observationTokens [] work) := by
    intro token member
    obtain ⟨occurrence, included, rfl⟩ := List.mem_map.mp member
    obtain ⟨event, received, identity⟩ := List.mem_flatMap.mp included
    exact (valid.eachMatches received).taskIdentity_token identity
  have streamSubset : ((events.flatMap (fun event => event.identities.2)).map
      (Sum.inr : NodeRef → ObservationToken)).Subset (observationTokens [] work) := by
    intro token member
    obtain ⟨ref, included, rfl⟩ := List.mem_map.mp member
    obtain ⟨event, received, identity⟩ := List.mem_flatMap.mp included
    exact (valid.eachMatches received).streamIdentity_token identity
  have taskUnique : ((events.flatMap (fun event => event.identities.1)).map
      (Sum.inl : Occurrence → ObservationToken)).Nodup :=
    unique.1.map Sum.inl (fun _ _ different same => different (Sum.inl.inj same))
  have streamUnique : ((events.flatMap (fun event => event.identities.2)).map
      (Sum.inr : NodeRef → ObservationToken)).Nodup :=
    unique.2.map Sum.inr (fun _ _ different same => different (Sum.inr.inj same))
  have tasks := taskUnique.length_le_of_subset taskSubset
  have streams := streamUnique.length_le_of_subset streamSubset
  simp only [List.length_map] at tasks streams
  have bound := valid.length_le_identities
  omega

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
