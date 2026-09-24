import Proofs.GraphQL.IncrementalDelivery.Correctness.DependencyKeys
import Proofs.GraphQL.IncrementalDelivery.Correctness.OwnerAvailability

/-! Least healthy outstanding keys support finite notice-progress constructions.
These statements derive readiness from execution metadata rather than adding a queue law.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Find a ready task at a least outstanding healthy owner key
-----------------------------------------------------------------------------------------

/-- Outstanding generated work has a ready task at a least healthy unaccounted owner key.
Every smaller healthy key is already accounted for. Witness: a finite key minimum and
the producer/item descent theorem, which preserves that minimum.
-/
theorem least_ready_owner
    {parents bound work groups streams events matching failures occurrence owners producer
      payload}
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer payload)
    (outstanding
      : ¬Accounted work matching events (failedBefore failures events.length) occurrence)
    : ∃ next nextOwners nextProducer result key,
        TaskAt work next nextOwners nextProducer result
        ∧ CanPublish work matching events (failedBefore failures events.length) next
            nextProducer
        ∧ key ∈ nextOwners
        ∧ ¬NodeFailed work (failedBefore failures events.length) key
        ∧ ∀ smaller,
            smaller < key
            → ¬NodeFailed work (failedBefore failures events.length) smaller
            → NodeAccounted work matching events (failedBefore failures events.length)
                smaller := by
  classical
  let qualifies (key : Nat) := ¬NodeFailed work (failedBefore failures events.length) key
    ∧ ∃ task taskOwners birth result,
      TaskAt work task taskOwners birth result ∧ key ∈ taskOwners
      ∧ ¬Accounted work matching events (failedBefore failures events.length) task
  let keys := (List.range bound).filter (fun key => decide (qualifies key))
  have inKeys {key} (qualifiesKey : qualifies key) : key ∈ keys := by
    obtain ⟨healthy, task, taskOwners, birth, result, descriptor, member, unfinished⟩ := qualifiesKey
    obtain ⟨node, kind, dependencies, producer, located, same⟩ := descriptor.owner_known member
    have below := (coherent_node_bounds coherent located).2
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (same ▸ below),
      by simpa only [decide_eq_true_eq] using (show qualifies key from
        ⟨healthy, task, taskOwners, birth, result, descriptor, member, unfinished⟩)⟩
  obtain ⟨owner, member, healthy, _⟩ := explained.outstanding_owner known
    (coherent_task_owners_nonempty coherent known) outstanding
  have original : owner ∈ keys := inKeys ⟨healthy, occurrence, owners, producer, payload,
    known, member, outstanding⟩
  obtain ⟨key, selected, least⟩ := nonempty_keys_minimum keys (by intro empty; simp [empty] at original)
  have qualifiesKey : qualifies key := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp selected).2
  obtain ⟨healthy, task, taskOwners, birth, result, descriptor, member, unfinished⟩ := qualifiesKey
  obtain ⟨next, nextOwners, nextProducer, result, nextKey, readyTask, ready,
    nextMember, nextHealthy, smaller⟩ := readyTask_owner_key_le valid coherent continuous
      ordered descriptor member healthy unfinished
  have nextOutstanding : ¬Accounted work matching events
      (failedBefore failures events.length) next := by
    rintro (cancelled | published)
    · exact ready.2.1 cancelled
    · exact ready.1 published
  have minimum := least nextKey (inKeys ⟨nextHealthy, next, nextOwners, nextProducer,
    result, readyTask, nextMember, nextOutstanding⟩)
  have same : nextKey = key := by omega
  subst nextKey
  refine ⟨next, nextOwners, nextProducer, result, key, readyTask, ready,
    nextMember, nextHealthy, ?_⟩
  intro other before otherHealthy task taskOwners projected contributes
  obtain ⟨birth, payload, taskKnown⟩ := projected
  apply Classical.byContradiction
  intro unaccounted
  have lower := least other (inKeys ⟨otherHealthy, task, taskOwners, birth, payload,
    taskKnown, contributes, unaccounted⟩)
  omega

-----------------------------------------------------------------------------------------
-- Smaller dependencies can be discharged in a maximal history
-----------------------------------------------------------------------------------------

/-- In a maximal explained history, a healthy accounted key satisfies dependencies.
Witness: an announced but uncompleted such key would permit a success completion.
Absent or unannounced accounted keys already satisfy the public dependency rule.
-/
theorem maximal_dependency_satisfied {work groups streams events matching failures key}
    (explained : Explains work groups streams events matching failures)
    (maximal
      : ∀ event next cuts, ¬Explains work groups streams (events ++ [event]) next cuts)
    (healthy : ¬NodeFailed work (failedBefore failures events.length) key)
    (accounted
      : NodeAccounted work matching events (failedBefore failures events.length) key)
    : DependencySatisfied work ((groups ++ streams).map DeliveryNode.key) matching events
        (failedBefore failures events.length) key := by
  classical
  refine ⟨healthy, ?_⟩
  by_cases supported : ∃ birth, NodeHasProducer work key birth
  · by_cases notified : key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events
    · by_cases closed : key ∈ completedKeys events
      · exact Or.inr (Or.inl closed)
      · obtain ⟨birth, node, kind, parents, descriptor, same⟩ := supported
        obtain ⟨event, permitted, _, _, _⟩ := completion_exists descriptor
          (same ▸ And.intro notified closed) (same ▸ accounted)
          (by simpa only [explained.2.1.failedBefore_eq (Nat.le_refl _)]
            using explained.2.1.known)
        exact False.elim (maximal event matching failures (explained.append_event permitted))
    · exact Or.inr (Or.inr ⟨notified, accounted⟩)
  · exact Or.inl supported

-----------------------------------------------------------------------------------------
-- Maximal incomplete histories still have eligible notices
-----------------------------------------------------------------------------------------

/-- A fresh healthy owner of a ready task is announceable once smaller healthy keys
satisfy dependencies. Witness: strict ancestry/stream-dependency ordering and causal failure
rules; the task itself witnesses that a group is not already fully accounted for.
-/
theorem least_owner_announceable
    {parents bound work initial matching events failed occurrence owners producer payload
      node kind dependencies}
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners producer payload)
    (ready : CanPublish work matching events failed occurrence producer)
    (descriptor : NodeAt work node kind dependencies producer)
    (member : node.key ∈ owners) (healthy : ¬NodeFailed work failed node.key)
    (fresh : node.key ∉ announcedKeys initial events)
    (smaller
      : ∀ key,
          key < node.key
          → ¬NodeFailed work failed key
          → DependencySatisfied work initial matching events failed key)
    : CanAnnounce work initial matching events failed node kind dependencies
        producer := by
  classical
  refine ⟨fresh, healthy, ?_, ready.2.2.1, ?_⟩
  · cases kind with
    | stream => exact Or.inl rfl
    | group =>
        apply Or.inr
        intro accounted
        rcases accounted occurrence owners ⟨producer, payload, known⟩ member with
          cancelled | published
        · exact ready.2.1 cancelled
        · exact ready.1 published
  · cases kind with
    | group =>
        intro key member
        exact smaller key (coherent_group_dependencies valid coherent descriptor key member)
          (fun failure => healthy (.groupDependency descriptor member failure))
    | stream =>
        by_cases empty : dependencies = []
        · exact Or.inl empty
        · have healthyParent : ∃ key ∈ dependencies, ¬NodeFailed work failed key := by
            apply Classical.byContradiction
            intro absent
            apply healthy
            apply NodeFailed.streamDependencies descriptor empty
            intro key member
            apply Classical.byContradiction
            intro healthyKey
            exact absent ⟨key, member, healthyKey⟩
          obtain ⟨key, member, healthyKey⟩ := healthyParent
          exact Or.inr ⟨key, member,
            smaller key (coherent_stream_dependencies ordered descriptor key member) healthyKey⟩

/-- A maximal incomplete generated-work history still has a currently eligible notice.
Witness: choose a least healthy outstanding owner, descend to a ready task without
increasing its key, discharge smaller dependencies, and exclude already-announced owners
using the constructed success/failure extension. MixedExistence supplies notice carriers
by maximizing histories with a separate supported-coverage witness.
-/
theorem maximal_outstanding_eligible
    {parents bound paths pathBound work groups streams events matching failures
      occurrence owners producer payload}
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (explained : Explains work groups streams events matching failures)
    (maximal
      : ∀ event next cuts, ¬Explains work groups streams (events ++ [event]) next cuts)
    (known : TaskAt work occurrence owners producer payload)
    (outstanding
      : ¬Accounted work matching events (failedBefore failures events.length) occurrence)
    : ∃ node kind dependencies birth,
        NodeAt work node kind dependencies birth
        ∧ CanAnnounce work ((groups ++ streams).map DeliveryNode.key) matching events
            (failedBefore failures events.length) node kind dependencies birth := by
  obtain ⟨next, nextOwners, nextProducer, result, key, task, ready,
    member, healthy, least⟩ := least_ready_owner valid coherent continuous ordered
      explained known outstanding
  have unannounced : key ∉ announcedKeys ((groups ++ streams).map DeliveryNode.key) events := by
    intro notified
    obtain ⟨event, nextMatching, cuts, extended⟩ := extend_ready_announced pathCoherent
      explained task ready ⟨key, member, notified, healthy⟩
    exact maximal event nextMatching cuts extended
  obtain ⟨node, kind, dependencies, descriptor, same⟩ := task.owner_at_producer member
  refine ⟨node, kind, dependencies, nextProducer, descriptor, ?_⟩
  apply least_owner_announceable valid coherent ordered task ready descriptor
    (same ▸ member) (same ▸ healthy) (same ▸ unannounced)
  intro smaller before smallerHealthy
  apply maximal_dependency_satisfied explained maximal smallerHealthy
  exact least smaller (by simpa only [same] using before) smallerHealthy

/-- A maximal generated-work history with no eligible unannounced notices is terminal.
Witness: the least-key obstruction rules out outstanding tasks, then every open node
would admit a completion. This is a conditional criterion, not a scheduler assumption.
The general mixed-run construction uses the weaker supported-notice coverage witness.
-/
theorem maximal_no_eligible_terminal
    {parents bound paths pathBound work groups streams events matching failures}
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (explained : Explains work groups streams events matching failures)
    (maximal
      : ∀ event next cuts, ¬Explains work groups streams (events ++ [event]) next cuts)
    (noticesCovered
      : ∀ node kind dependencies birth,
          NodeAt work node kind dependencies birth
          → ¬CanAnnounce work ((groups ++ streams).map DeliveryNode.key) matching events
              (failedBefore failures events.length) node kind dependencies birth)
    : Terminal work ((groups ++ streams).map DeliveryNode.key) matching events
        (failedBefore failures events.length) := by
  classical
  have accounted : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload →
      Accounted work matching events (failedBefore failures events.length) occurrence := by
    intro occurrence owners producer payload known
    apply Classical.byContradiction
    intro outstanding
    obtain ⟨node, kind, dependencies, birth, descriptor, eligible⟩ :=
      maximal_outstanding_eligible valid coherent continuous ordered pathCoherent explained
        maximal known outstanding
    exact noticesCovered node kind dependencies birth descriptor eligible
  refine ⟨accounted, ?_⟩
  intro node kind dependencies birth descriptor
  have nodeAccounted : NodeAccounted work matching events
      (failedBefore failures events.length) node.key := by
    rintro occurrence owners ⟨producer, payload, known⟩ _
    exact accounted occurrence owners producer payload known
  by_cases closed : node.key ∈ completedKeys events
  · exact Or.inl closed
  · refine Or.inr ⟨?_, Or.inr nodeAccounted⟩
    intro announced
    obtain ⟨event, allowed, _, _, _⟩ := completion_exists descriptor
      ⟨announced, closed⟩ nodeAccounted
      (by simpa only [explained.2.1.failedBefore_eq (Nat.le_refl _)]
        using explained.2.1.known)
    exact maximal event matching failures (explained.append_event allowed)

end GraphQL.IncrementalDelivery.Correctness
