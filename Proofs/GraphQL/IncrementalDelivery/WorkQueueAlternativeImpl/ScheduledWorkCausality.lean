import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledWorkRefinement

/-! The causal kernel depends on structural tasks, owners, producers and failure status,
not the precise counted totals. One recursively related Work pair therefore transports
reachability/failure/cancellation at the same actual structural failure/publication cut.
This conditional transport does not construct recursive executor or native histories. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Owner, dependency, producer and success evidence from one related Work pair
-----------------------------------------------------------------------------------------

theorem WorkRefines.task_owners {keys original right occurrence owners}
    (related : WorkRefines keys original right)
    (known : TaskHasOwners original occurrence owners)
    : TaskHasOwners right occurrence (owners.map keys) := by
  obtain ⟨producer, value, known⟩ := known
  obtain ⟨after, actual, _⟩ := related.task known
  exact ⟨_, _, actual⟩

theorem WorkRefines.task_owners_before {keys original right occurrence owners}
    (related : WorkRefines keys original right)
    (known : TaskHasOwners right occurrence owners)
    : ∃ before, TaskHasOwners original occurrence before ∧ before.map keys = owners := by
  obtain ⟨producer, value, known⟩ := known
  obtain ⟨before, outcome, actual, equal, _⟩ := related.task_before known
  exact ⟨before, ⟨_, _, actual⟩, equal⟩

theorem WorkRefines.task_producer {keys original right}
    (related : WorkRefines keys original right) (occurrence : Occurrence)
    (producer : Option Occurrence)
    : TaskHasProducer right occurrence producer
      ↔ TaskHasProducer original occurrence producer := by
  constructor
  · rintro ⟨owners, value, known⟩
    obtain ⟨before, outcome, actual, _, _⟩ := related.task_before known
    exact ⟨_, _, actual⟩
  · rintro ⟨owners, value, known⟩
    obtain ⟨after, actual, _⟩ := related.task known
    exact ⟨_, _, actual⟩

theorem WorkRefines.task_succeeds {keys original right}
    (related : WorkRefines keys original right) (occurrence : Occurrence)
    : TaskSucceeds right occurrence ↔ TaskSucceeds original occurrence := by
  constructor
  · rintro ⟨owners, producer, value, known, succeeds⟩
    obtain ⟨before, outcome, actual, _, payload⟩ := related.task_before known
    exact ⟨_, _, _, actual, payload.failure_status.mp succeeds⟩
  · rintro ⟨owners, producer, value, known, succeeds⟩
    obtain ⟨after, actual, payload⟩ := related.task known
    exact ⟨_, _, _, actual, payload.failure_status.mpr succeeds⟩

theorem WorkRefines.node_dependencies {keys original right key kind dependencies}
    (related : WorkRefines keys original right)
    (known : NodeHasDependencies original key kind dependencies)
    : NodeHasDependencies right (keys key) kind (dependencies.map keys) := by
  obtain ⟨descriptor, producer, known, rfl⟩ := known
  exact ⟨_, _, related.delivery_node known, rfl⟩

theorem WorkRefines.node_dependencies_before {keys original right key kind dependencies}
    (related : WorkRefines keys original right) (injective : Function.Injective keys)
    (known : NodeHasDependencies right (keys key) kind dependencies)
    : ∃ before,
        NodeHasDependencies original key kind before
        ∧ before.map keys = dependencies := by
  obtain ⟨descriptor, producer, known, same⟩ := known
  obtain ⟨before, parents, actual, rfl, mapped⟩ := related.node_before known
  exact ⟨parents, ⟨_, _, actual, injective same⟩, mapped⟩

theorem WorkRefines.node_producer {keys original right}
    (related : WorkRefines keys original right) (injective : Function.Injective keys)
    (key : Nat) (producer : Option Occurrence)
    : NodeHasProducer right (keys key) producer
      ↔ NodeHasProducer original key producer := by
  constructor
  · rintro ⟨descriptor, kind, parents, known, same⟩
    obtain ⟨before, dependencies, actual, rfl, _⟩ := related.node_before known
    exact ⟨_, _, _, actual, injective same⟩
  · rintro ⟨descriptor, kind, parents, known, rfl⟩
    exact ⟨_, _, _, related.delivery_node known, rfl⟩

theorem WorkRefines.reachable {keys original right}
    (related : WorkRefines keys original right) (occurrence : Occurrence)
    : Reachable right occurrence ↔ Reachable original occurrence := by
  constructor
  · intro known
    induction known with
    | root known => exact .root ((related.task_producer ..).mp known)
    | child known succeeds _ ih =>
        exact .child ((related.task_producer ..).mp known)
          ((related.task_succeeds ..).mp succeeds) ih
  · intro known
    induction known with
    | root known => exact .root ((related.task_producer ..).mpr known)
    | child known succeeds _ ih =>
        exact .child ((related.task_producer ..).mpr known)
          ((related.task_succeeds ..).mpr succeeds) ih

-----------------------------------------------------------------------------------------
-- Mutual causal transport keeps the same failed occurrences/publication snapshot
-----------------------------------------------------------------------------------------

theorem WorkRefines.node_failed_forward {keys original right failed published key}
    (related : WorkRefines keys original right) (injective : Function.Injective keys)
    (failure : Causality.NodeFailed original failed published key)
    : Causality.NodeFailed right failed published (keys key) := by
  induction failure
    using Causality.NodeFailed.rec
      (motive_2 :=
        fun occurrence _ =>
          Causality.TaskCancelled right failed published occurrence) with
  | task known owner finished =>
      exact .task (related.task_owners known) (List.mem_map_of_mem owner) finished
  | groupDependency known member _ ih =>
      exact .groupDependency (related.node_dependencies known) (List.mem_map_of_mem member) ih
  | streamDependencies known nonempty _ ih =>
      refine .streamDependencies (related.node_dependencies known) ?_ ?_
      · intro empty
        exact nonempty (List.map_eq_nil_iff.mp empty)
      · intro dependency member
        obtain ⟨before, oldMember, rfl⟩ := List.mem_map.mp member
        exact ih before oldMember
  | producers known noRoot unpublished _ ih =>
      obtain ⟨producer, known⟩ := known
      refine .producers ⟨producer, (related.node_producer injective ..).mpr known⟩ ?_ ?_ ?_
      · intro known
        exact noRoot ((related.node_producer injective ..).mp known)
      · intro producer known
        exact unpublished producer ((related.node_producer injective ..).mp known)
      · intro producer known absent
        exact ih producer ((related.node_producer injective ..).mp known) absent
  | owners known unpublished nonempty _ ih =>
      refine .owners (related.task_owners known) unpublished ?_ ?_
      · intro empty
        exact nonempty (List.map_eq_nil_iff.mp empty)
      · intro key member
        obtain ⟨before, oldMember, rfl⟩ := List.mem_map.mp member
        exact ih before oldMember
  | producerFailed known unpublished member =>
      exact .producerFailed ((related.task_producer ..).mpr known) unpublished member
  | producerCancelled known unpublished _ ih =>
      exact .producerCancelled ((related.task_producer ..).mpr known) unpublished ih

theorem WorkRefines.task_cancelled_forward
    {keys original right failed published occurrence}
    (related : WorkRefines keys original right) (injective : Function.Injective keys)
    (cancelled : Causality.TaskCancelled original failed published occurrence)
    : Causality.TaskCancelled right failed published occurrence := by
  induction cancelled using Causality.TaskCancelled.rec (motive_1 := fun _ _ => True) with
  | task | groupDependency | streamDependencies | producers => trivial
  | owners known unpublished nonempty failures _ =>
      refine .owners (related.task_owners known) unpublished ?_ ?_
      · intro empty
        exact nonempty (List.map_eq_nil_iff.mp empty)
      · intro key member
        obtain ⟨before, oldMember, rfl⟩ := List.mem_map.mp member
        exact related.node_failed_forward injective (failures before oldMember)
  | producerFailed known unpublished member =>
      exact .producerFailed ((related.task_producer ..).mpr known) unpublished member
  | producerCancelled known unpublished _ ih =>
      exact .producerCancelled ((related.task_producer ..).mpr known) unpublished ih

theorem WorkRefines.node_failed_before {keys original right failed published renamed}
    (related : WorkRefines keys original right) (injective : Function.Injective keys)
    (failure : Causality.NodeFailed right failed published renamed)
    : ∀ key, renamed = keys key → Causality.NodeFailed original failed published key := by
  induction failure
    using Causality.NodeFailed.rec
      (motive_2 :=
        fun occurrence _ =>
          Causality.TaskCancelled original failed published occurrence) with
  | task known owner finished =>
      intro key same
      obtain ⟨before, actual, rfl⟩ := related.task_owners_before known
      obtain ⟨oldKey, member, equal⟩ := List.mem_map.mp owner
      have sameKey : oldKey = key := injective (equal.trans same)
      subst oldKey
      exact .task actual member finished
  | groupDependency known member _ ih =>
      intro key same
      rw [same] at known
      obtain ⟨before, actual, rfl⟩ := related.node_dependencies_before injective known
      obtain ⟨dependency, oldMember, rfl⟩ := List.mem_map.mp member
      exact .groupDependency actual oldMember (ih dependency rfl)
  | streamDependencies known nonempty _ ih =>
      intro key same
      rw [same] at known
      obtain ⟨before, actual, rfl⟩ := related.node_dependencies_before injective known
      refine .streamDependencies actual ?_ ?_
      · intro empty
        subst before
        exact nonempty rfl
      · intro dependency member
        exact ih (keys dependency) (List.mem_map_of_mem member) dependency rfl
  | producers known noRoot unpublished _ ih =>
      intro key same
      rw [same] at known noRoot unpublished ih
      obtain ⟨producer, known⟩ := known
      refine .producers ⟨producer, (related.node_producer injective ..).mp known⟩ ?_ ?_ ?_
      · intro known
        exact noRoot ((related.node_producer injective ..).mpr known)
      · intro producer known
        exact unpublished producer ((related.node_producer injective ..).mpr known)
      · intro producer known absent
        exact ih producer ((related.node_producer injective ..).mpr known) absent
  | owners known unpublished nonempty _ ih =>
      obtain ⟨before, actual, rfl⟩ := related.task_owners_before known
      refine .owners actual unpublished ?_ ?_
      · intro empty
        subst before
        exact nonempty rfl
      · intro key member
        exact ih (keys key) (List.mem_map_of_mem member) key rfl
  | producerFailed known unpublished member =>
      exact .producerFailed ((related.task_producer ..).mp known) unpublished member
  | producerCancelled known unpublished _ ih =>
      exact .producerCancelled ((related.task_producer ..).mp known) unpublished ih

theorem WorkRefines.task_cancelled_before
    {keys original right failed published occurrence}
    (related : WorkRefines keys original right) (injective : Function.Injective keys)
    (cancelled : Causality.TaskCancelled right failed published occurrence)
    : Causality.TaskCancelled original failed published occurrence := by
  induction cancelled using Causality.TaskCancelled.rec (motive_1 := fun _ _ => True) with
  | task | groupDependency | streamDependencies | producers => trivial
  | owners known unpublished nonempty failures _ =>
      obtain ⟨before, actual, rfl⟩ := related.task_owners_before known
      refine .owners actual unpublished ?_ ?_
      · intro empty
        subst before
        exact nonempty rfl
      · intro key member
        exact related.node_failed_before injective
          (failures (keys key) (List.mem_map_of_mem member)) key rfl
  | producerFailed known unpublished member =>
      exact .producerFailed ((related.task_producer ..).mp known) unpublished member
  | producerCancelled known unpublished _ ih =>
      exact .producerCancelled ((related.task_producer ..).mp known) unpublished ih

theorem WorkRefines.failed_key_image {keys original right failed published renamed}
    (related : WorkRefines keys original right)
    (failure : Causality.NodeFailed right failed published renamed)
    : ∃ key, keys key = renamed := by
  cases failure with
  | task known owner _ =>
      obtain ⟨before, _, rfl⟩ := related.task_owners_before known
      obtain ⟨key, _, same⟩ := List.mem_map.mp owner
      exact ⟨key, same⟩
  | groupDependency known _ _ | streamDependencies known _ _ =>
      obtain ⟨descriptor, producer, known, same⟩ := known
      obtain ⟨before, _, _, rfl, _⟩ := related.node_before known
      exact ⟨before.ref, same⟩
  | producers known _ _ _ =>
      obtain ⟨producer, descriptor, kind, dependencies, known, same⟩ := known
      obtain ⟨before, _, _, rfl, _⟩ := related.node_before known
      exact ⟨before.ref, same⟩

-----------------------------------------------------------------------------------------
-- Checked causal root, including coverage rather than only forward preservation
-----------------------------------------------------------------------------------------

/-- At one structural failure/publication cut, related counts and injectively mapped
keys neither add nor lose reachability, node failure or task cancellation. -/
def RecursiveWorkCausality : Prop :=
  ∀ keys,
    Function.Injective keys
    → ∀ original right,
        WorkRefines keys original right
        → ∀ failed published,
            (∀ occurrence, Reachable right occurrence ↔ Reachable original occurrence)
            ∧ (∀ renamed,
                Causality.NodeFailed right failed published renamed
                ↔ ∃ key,
                    keys key = renamed
                    ∧ Causality.NodeFailed original failed published key)
            ∧ (∀ occurrence,
                Causality.TaskCancelled right failed published occurrence
                ↔ Causality.TaskCancelled original failed published occurrence)

theorem recursiveWorkCausality_holds : RecursiveWorkCausality := by
  intro keys injective original right related failed published
  refine ⟨related.reachable, ?_, ?_⟩
  · intro renamed
    constructor
    · intro failure
      obtain ⟨key, same⟩ := related.failed_key_image failure
      exact ⟨key, same, related.node_failed_before injective failure key same.symm⟩
    · rintro ⟨key, rfl, known⟩
      exact related.node_failed_forward injective known
  · intro occurrence
    exact ⟨related.task_cancelled_before injective, related.task_cancelled_forward injective⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
