import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Causality

/-! Equivalence of the former three-judgment failure rules and the simplified rules.
The old presentation is retained only here as a proof witness, not public semantics.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler
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

/-- Former node-failure evidence satisfies the current rules, by mutual causal induction.
-/
theorem NodeFailed.toCurrent {work failed key} (h : NodeFailed work failed key)
    : WorkScheduler.NodeFailed work failed key := by
  induction h
    using NodeFailed.rec
      (motive_2 := fun occurrence _ => WorkScheduler.TaskCancelled work failed occurrence)
      (motive_3 :=
        fun occurrence _ =>
          occurrence ∈ failed ∨ WorkScheduler.TaskCancelled work failed occurrence) with
  | task known owner member => exact .task known owner member
  | groupDependency known dependency _ ih =>
      exact .groupDependency known dependency ih
  | streamDependencies known nonempty _ ih => exact .streamDependencies known nonempty ih
  | producers known noRoot _ ih =>
      exact .producers known noRoot
        (fun other kind dependencies producerOccurrence located same notFailed =>
          (ih other kind dependencies producerOccurrence located same).resolve_left
            notFailed)
  | owners known nonempty _ ih => exact .owners known nonempty ih
  | producer known _ ih =>
      exact ih.elim (.producerFailed known) (.producerCancelled known)
  | failure member => exact Or.inl member
  | cancelled _ ih => exact Or.inr ih

/-- Former cancellation evidence satisfies the current rules, by mutual causal induction.
-/
theorem TaskCancelled.toCurrent {work failed occurrence}
    (h : TaskCancelled work failed occurrence)
    : WorkScheduler.TaskCancelled work failed occurrence := by
  induction h
    using TaskCancelled.rec
      (motive_1 := fun key _ => WorkScheduler.NodeFailed work failed key)
      (motive_3 :=
        fun occurrence _ =>
          occurrence ∈ failed ∨ WorkScheduler.TaskCancelled work failed occurrence) with
  | task known owner member => exact .task known owner member
  | groupDependency known dependency _ ih =>
      exact .groupDependency known dependency ih
  | streamDependencies known nonempty _ ih => exact .streamDependencies known nonempty ih
  | producers known noRoot _ ih =>
      exact .producers known noRoot
        (fun other kind dependencies producerOccurrence located same notFailed =>
          (ih other kind dependencies producerOccurrence located same).resolve_left
            notFailed)
  | owners known nonempty _ ih => exact .owners known nonempty ih
  | producer known _ ih =>
      exact ih.elim (.producerFailed known) (.producerCancelled known)
  | failure member => exact Or.inl member
  | cancelled _ ih => exact Or.inr ih

/-- Current node failures have former witnesses, by splitting failed/cancelled producers.
-/
theorem nodeFailed_of_current {work failed key}
    (h : WorkScheduler.NodeFailed work failed key)
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
  | producers known noRoot _ ih =>
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
  | owners known nonempty _ ih =>
      obtain ⟨producer, payload, known⟩ := known
      exact .owners known nonempty ih
  | producerFailed known member =>
      obtain ⟨owners, payload, known⟩ := known
      exact .producer known (.failure member)
  | producerCancelled known _ ih =>
      obtain ⟨owners, payload, known⟩ := known
      exact .producer known (.cancelled ih)

/-- Current cancellations have former witnesses, by rebuilding producer unavailability. -/
theorem taskCancelled_of_current {work failed occurrence}
    (h : WorkScheduler.TaskCancelled work failed occurrence)
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
  | producers known noRoot _ ih =>
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
  | owners known nonempty _ ih =>
      obtain ⟨producer, payload, known⟩ := known
      exact .owners known nonempty ih
  | producerFailed known member =>
      obtain ⟨owners, payload, known⟩ := known
      exact .producer known (.failure member)
  | producerCancelled known _ ih =>
      obtain ⟨owners, payload, known⟩ := known
      exact .producer known (.cancelled ih)

/-- Former reachability gives the same structural producer chain, by induction. -/
theorem Reachable.toCurrent {work occurrence} (h : Reachable work occurrence)
    : WorkScheduler.Reachable work occurrence := by
  induction h with
  | root known => exact .root ⟨_, _, known⟩
  | child known producer success _ ih =>
      exact .child ⟨_, _, known⟩ ⟨_, _, _, producer, success⟩ ih

/-- Structural reachability unpacks to the former producer-chain derivation. -/
theorem reachable_of_current {work occurrence}
    (h : WorkScheduler.Reachable work occurrence)
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
    : Reachable work occurrence ↔ WorkScheduler.Reachable work occurrence :=
  ⟨Reachable.toCurrent, reachable_of_current⟩

/-- The node-failure predicates agree for all raw work, by the two witness translations.
-/
theorem nodeFailed_iff {work failed key}
    : NodeFailed work failed key ↔ WorkScheduler.NodeFailed work failed key :=
  ⟨NodeFailed.toCurrent, nodeFailed_of_current⟩

/-- Cancellation agrees for all raw work, without any uniqueness or well-formedness
premise.
-/
theorem taskCancelled_iff {work failed occurrence}
    : TaskCancelled work failed occurrence
      ↔ WorkScheduler.TaskCancelled work failed occurrence :=
  ⟨TaskCancelled.toCurrent, taskCancelled_of_current⟩

/-- Producer unavailability is exactly failure or cancellation, by constructor inversion.
-/
theorem producerUnavailable_iff {work failed occurrence}
    : ProducerUnavailable work failed occurrence
      ↔ occurrence ∈ failed ∨ WorkScheduler.TaskCancelled work failed occurrence := by
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
    : NodeFailed work failed = WorkScheduler.NodeFailed work failed :=
  funext fun _ => propext nodeFailed_iff

/-- Function equality permits substituting the simplified cancellation rule in admission.
-/
theorem taskCancelled_eq (work : Work) (failed : List Occurrence)
    : TaskCancelled work failed = WorkScheduler.TaskCancelled work failed :=
  funext fun _ => propext taskCancelled_iff

end FailureEquivalence
end GraphQL.IncrementalDelivery.WorkScheduler
