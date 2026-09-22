import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Causality

/-! The former three-judgment rules agree with the causal kernel when no publications
are protected. This is not an equivalence with the publication-aware history contract.
The old presentation is retained only here as a proof witness, not public semantics.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

namespace FailureEquivalence

/-! The former failure presentation, with an explicit producer-unavailability judgment. -/

/-- (Reachable work occurrence) means the task occurrence in work has a successful
producer chain. Successful internal completions need not be individually scheduled.
-/
inductive Reachable (work : Work) : Occurrence → Prop where
  | root {occurrence owners payload} (known : TaskAt work occurrence owners none payload)
    : Reachable work occurrence
  | child {occurrence owners producerOccurrence payload producerOwners ancestor result}
    (known : TaskAt work occurrence owners (some producerOccurrence) payload)
    (producer : TaskAt work producerOccurrence producerOwners ancestor result)
    (success : result.failure = none)
    (reachable : Reachable work producerOccurrence)
    : Reachable work occurrence

mutual
  /-- (NodeFailed work failed key) derives failure of node key in work from supplied
  failed occurrences.
  -/
  inductive NodeFailed (work : Work) (failed : List Occurrence) : Nat → Prop where
    | task {occurrence owners producer payload key}
      (known : TaskAt work occurrence owners producer payload)
      (owner : key ∈ owners) (finished : occurrence ∈ failed)
      : NodeFailed work failed key
    | groupDependency {node dependencies birth key}
      (known : NodeAt work node .group dependencies birth)
      (dependency : key ∈ dependencies) (failure : NodeFailed work failed key)
      : NodeFailed work failed node.key
    | streamDependencies {node dependencies birth}
      (known : NodeAt work node .stream dependencies birth) (nonempty : dependencies ≠ [])
      (failures : ∀ key ∈ dependencies, NodeFailed work failed key)
      : NodeFailed work failed node.key
    | producers {node kind dependencies birth}
      (known : NodeAt work node kind dependencies birth)
      (noRoot
        : ∀ other otherKind otherDependencies,
            NodeAt work other otherKind otherDependencies none → other.key ≠ node.key)
      (unavailable
        : ∀ other otherKind otherDependencies producerOccurrence,
            NodeAt work other otherKind otherDependencies (some producerOccurrence)
            → other.key = node.key
            → ProducerUnavailable work failed producerOccurrence)
      : NodeFailed work failed node.key

  /-- (TaskCancelled work failed occurrence) derives cancellation of the task occurrence
  in work from supplied failed occurrences and their causal consequences.
  -/
  inductive TaskCancelled (work : Work) (failed : List Occurrence)
      : Occurrence → Prop where
    | owners {occurrence owners producer payload}
      (known : TaskAt work occurrence owners producer payload) (nonempty : owners ≠ [])
      (failures : ∀ key ∈ owners, NodeFailed work failed key)
      : TaskCancelled work failed occurrence
    | producer {occurrence owners producerOccurrence payload}
      (known : TaskAt work occurrence owners (some producerOccurrence) payload)
      (unavailable : ProducerUnavailable work failed producerOccurrence)
      : TaskCancelled work failed occurrence

  /-- (ProducerUnavailable work failed occurrence) says this producer occurrence in work
  has failed or been cancelled, relative to the supplied failed occurrences.
  -/
  inductive ProducerUnavailable (work : Work) (failed : List Occurrence)
      : Occurrence → Prop where
    | failure {occurrence} (member : occurrence ∈ failed)
      : ProducerUnavailable work failed occurrence
    | cancelled {occurrence} (reason : TaskCancelled work failed occurrence)
      : ProducerUnavailable work failed occurrence
end

/-- Former node failures satisfy the kernel with no protected publications.
Witness: mutual causal induction, making each publication exclusion trivial.
-/
theorem NodeFailed.toCurrent {work failed key} (h : NodeFailed work failed key)
    : Causality.NodeFailed work failed (fun _ => False) key := by
  induction h
    using NodeFailed.rec
      (motive_2 :=
        fun occurrence _ =>
          Causality.TaskCancelled work failed (fun _ => False) occurrence)
      (motive_3 :=
        fun occurrence _ =>
          occurrence ∈ failed
          ∨ Causality.TaskCancelled work failed (fun _ => False) occurrence) with
  | task known owner member => exact .task ⟨_, _, known⟩ owner member
  | groupDependency known dependency _ ih =>
      exact .groupDependency ⟨_, _, known, rfl⟩ dependency ih
  | streamDependencies known nonempty _ ih =>
      exact .streamDependencies ⟨_, _, known, rfl⟩ nonempty ih
  | producers known noRoot _ ih =>
      refine .producers ⟨_, _, _, _, known, rfl⟩ ?_ (by simp) ?_
      · rintro ⟨other, kind, dependencies, located, same⟩
        exact noRoot other kind dependencies located same
      · rintro producerOccurrence ⟨other, kind, dependencies, located, same⟩ notFailed
        exact (ih other kind dependencies producerOccurrence located same).resolve_left
          notFailed
  | owners known nonempty _ ih => exact .owners ⟨_, _, known⟩ id nonempty ih
  | producer known _ ih =>
      exact ih.elim (.producerFailed ⟨_, _, known⟩ id)
        (.producerCancelled ⟨_, _, known⟩ id)
  | failure member => exact Or.inl member
  | cancelled _ ih => exact Or.inr ih

/-- Former cancellations satisfy the kernel with no protected publications.
Witness: mutual causal induction, making each publication exclusion trivial.
-/
theorem TaskCancelled.toCurrent {work failed occurrence}
    (h : TaskCancelled work failed occurrence)
    : Causality.TaskCancelled work failed (fun _ => False) occurrence := by
  induction h
    using TaskCancelled.rec
      (motive_1 := fun key _ => Causality.NodeFailed work failed (fun _ => False) key)
      (motive_3 :=
        fun occurrence _ =>
          occurrence ∈ failed
          ∨ Causality.TaskCancelled work failed (fun _ => False) occurrence) with
  | task known owner member => exact .task ⟨_, _, known⟩ owner member
  | groupDependency known dependency _ ih =>
      exact .groupDependency ⟨_, _, known, rfl⟩ dependency ih
  | streamDependencies known nonempty _ ih =>
      exact .streamDependencies ⟨_, _, known, rfl⟩ nonempty ih
  | producers known noRoot _ ih =>
      refine .producers ⟨_, _, _, _, known, rfl⟩ ?_ (by simp) ?_
      · rintro ⟨other, kind, dependencies, located, same⟩
        exact noRoot other kind dependencies located same
      · rintro producerOccurrence ⟨other, kind, dependencies, located, same⟩ notFailed
        exact (ih other kind dependencies producerOccurrence located same).resolve_left
          notFailed
  | owners known nonempty _ ih => exact .owners ⟨_, _, known⟩ id nonempty ih
  | producer known _ ih =>
      exact ih.elim (.producerFailed ⟨_, _, known⟩ id)
        (.producerCancelled ⟨_, _, known⟩ id)
  | failure member => exact Or.inl member
  | cancelled _ ih => exact Or.inr ih

/-- Current node failures have former witnesses, by splitting failed/cancelled producers.
-/
theorem nodeFailed_of_current {work failed key}
    (h : Causality.NodeFailed work failed (fun _ => False) key)
    : NodeFailed work failed key := by
  induction h
    using Causality.NodeFailed.rec
      (motive_2 := fun occurrence _ => TaskCancelled work failed occurrence) with
  | task known owner member =>
      obtain ⟨producer, payload, known⟩ := known
      exact .task known owner member
  | groupDependency known dependency _ ih =>
      obtain ⟨node, birth, known, rfl⟩ := known
      exact .groupDependency known dependency ih
  | streamDependencies known nonempty _ ih =>
      obtain ⟨node, birth, known, rfl⟩ := known
      exact .streamDependencies known nonempty ih
  | producers known noRoot _ _ ih =>
      obtain ⟨birth, node, kind, dependencies, known, rfl⟩ := known
      refine NodeFailed.producers known ?_ ?_
      · intro other otherKind otherDependencies located same
        exact noRoot ⟨other, otherKind, otherDependencies, located, same⟩
      · intro other otherKind otherDependencies producerOccurrence located same
        by_cases member : producerOccurrence ∈ failed
        · exact .failure member
        · exact .cancelled
            (ih producerOccurrence
              ⟨other, otherKind, otherDependencies, located, same⟩ member)
  | owners known _ nonempty _ ih =>
      obtain ⟨producer, payload, known⟩ := known
      exact .owners known nonempty ih
  | producerFailed known _ member =>
      obtain ⟨owners, payload, known⟩ := known
      exact .producer known (.failure member)
  | producerCancelled known _ _ ih =>
      obtain ⟨owners, payload, known⟩ := known
      exact .producer known (.cancelled ih)

/-- Current cancellations have former witnesses, by rebuilding producer unavailability. -/
theorem taskCancelled_of_current {work failed occurrence}
    (h : Causality.TaskCancelled work failed (fun _ => False) occurrence)
    : TaskCancelled work failed occurrence := by
  induction h
    using Causality.TaskCancelled.rec
      (motive_1 := fun key _ => NodeFailed work failed key) with
  | task known owner member =>
      obtain ⟨producer, payload, known⟩ := known
      exact .task known owner member
  | groupDependency known dependency _ ih =>
      obtain ⟨node, birth, known, rfl⟩ := known
      exact .groupDependency known dependency ih
  | streamDependencies known nonempty _ ih =>
      obtain ⟨node, birth, known, rfl⟩ := known
      exact .streamDependencies known nonempty ih
  | producers known noRoot _ _ ih =>
      obtain ⟨birth, node, kind, dependencies, known, rfl⟩ := known
      refine NodeFailed.producers known ?_ ?_
      · intro other otherKind otherDependencies located same
        exact noRoot ⟨other, otherKind, otherDependencies, located, same⟩
      · intro other otherKind otherDependencies producerOccurrence located same
        by_cases member : producerOccurrence ∈ failed
        · exact .failure member
        · exact .cancelled
            (ih producerOccurrence
              ⟨other, otherKind, otherDependencies, located, same⟩ member)
  | owners known _ nonempty _ ih =>
      obtain ⟨producer, payload, known⟩ := known
      exact .owners known nonempty ih
  | producerFailed known _ member =>
      obtain ⟨owners, payload, known⟩ := known
      exact .producer known (.failure member)
  | producerCancelled known _ _ ih =>
      obtain ⟨owners, payload, known⟩ := known
      exact .producer known (.cancelled ih)

/-- Former reachability gives the same structural producer chain, by induction. -/
theorem Reachable.toCurrent {work occurrence} (h : Reachable work occurrence)
    : WorkQueueSemantics.Reachable work occurrence := by
  induction h with
  | root known => exact .root ⟨_, _, known⟩
  | child known producer success _ ih =>
      exact .child ⟨_, _, known⟩ ⟨_, _, _, producer, success⟩ ih

/-- Structural reachability unpacks to the former producer-chain derivation. -/
theorem reachable_of_current {work occurrence}
    (h : WorkQueueSemantics.Reachable work occurrence)
    : Reachable work occurrence := by
  induction h with
  | root known =>
      obtain ⟨owners, payload, known⟩ := known
      exact .root known
  | child known success _ ih =>
      obtain ⟨owners, payload, known⟩ := known
      obtain ⟨producerOwners, ancestor, result, producer, success⟩ := success
      exact .child known producer success ih

/-- Reachability is unchanged for all raw work, by the two producer-chain translations. -/
theorem reachable_iff {work occurrence}
    : Reachable work occurrence ↔ WorkQueueSemantics.Reachable work occurrence :=
  ⟨Reachable.toCurrent, reachable_of_current⟩

/-- Node failure agrees for all raw work when no publications are protected.
Witness: the two causal-kernel translations, not a whole-history normalization.
-/
theorem nodeFailed_iff {work failed key}
    : NodeFailed work failed key
      ↔ Causality.NodeFailed work failed (fun _ => False) key :=
  ⟨NodeFailed.toCurrent, nodeFailed_of_current⟩

/-- Cancellation agrees for all raw work when no publications are protected.
Witness: the two causal-kernel translations; no generated-work premise is needed.
-/
theorem taskCancelled_iff {work failed occurrence}
    : TaskCancelled work failed occurrence
      ↔ Causality.TaskCancelled work failed (fun _ => False) occurrence :=
  ⟨TaskCancelled.toCurrent, taskCancelled_of_current⟩

/-- Producer unavailability is exactly failure or cancellation, by constructor inversion.
-/
theorem producerUnavailable_iff {work failed occurrence}
    : ProducerUnavailable work failed occurrence
      ↔ occurrence ∈ failed
        ∨ Causality.TaskCancelled work failed (fun _ => False) occurrence := by
  constructor
  · intro unavailable
    cases unavailable with
    | failure member => exact Or.inl member
    | cancelled h => exact Or.inr h.toCurrent
  · intro unavailable
    exact unavailable.elim ProducerUnavailable.failure
      (fun h => .cancelled (taskCancelled_of_current h))

/-- Function equality permits substituting the simplified node rule in larger predicates.
-/
theorem nodeFailed_eq (work : Work) (failed : List Occurrence)
    : NodeFailed work failed = Causality.NodeFailed work failed (fun _ => False) :=
  funext fun _ => propext nodeFailed_iff

/-- Function equality identifies cancellation only in the no-publication kernel.
Witness: pointwise equivalence; history admission is deliberately not equated.
-/
theorem taskCancelled_eq (work : Work) (failed : List Occurrence)
    : TaskCancelled work failed = Causality.TaskCancelled work failed (fun _ => False) :=
  funext fun _ => propext taskCancelled_iff

end FailureEquivalence
end GraphQL.IncrementalDelivery.WorkQueueSemantics
