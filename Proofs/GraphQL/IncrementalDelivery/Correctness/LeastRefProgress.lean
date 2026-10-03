import Proofs.GraphQL.IncrementalDelivery.Correctness.DependencyRefs
import Proofs.GraphQL.IncrementalDelivery.Correctness.OwnerAvailability

/-! Least healthy outstanding refs support finite notice-progress constructions.
These statements derive readiness from execution metadata rather than adding a queue law.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Find a ready task at a least outstanding healthy owner ref
-----------------------------------------------------------------------------------------

/-- Outstanding generated work has a ready task at a least healthy unaccounted owner ref.
Every smaller healthy ref is already accounted for. Witness: a finite ref minimum and
the producer/item descent theorem, which preserves that minimum.
-/
theorem least_ready_owner
    {parents bound work groups streams events matching failures occurrence owners producer
      payload}
    (valid : Valid parents bound) (coherent : MixedRefs.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer payload)
    (outstanding : ¬TaskAccounted work matching events failures occurrence)
    : ∃ next nextOwners nextProducer result ref,
        TaskAt work next nextOwners nextProducer result
        ∧ CanPublish work matching events failures next nextProducer
        ∧ ref ∈ nextOwners
        ∧ ¬NodeFailed work matching events failures ref
        ∧ ∀ smaller,
            smaller < ref
            → ¬NodeFailed work matching events failures smaller
            → NodeAccounted work matching events failures smaller := by
  classical
  let qualifies (ref : NodeRef) := ¬NodeFailed work matching events failures ref
    ∧ ∃ task taskOwners birth result,
      TaskAt work task taskOwners birth result ∧ ref ∈ taskOwners
      ∧ ¬TaskAccounted work matching events failures task
  let refs := (List.range bound).filter (fun ref => decide (qualifies ref))
  have inRefs {ref} (qualifiesRef : qualifies ref) : ref ∈ refs := by
    obtain ⟨healthy, task, taskOwners, birth, result, descriptor, member, unfinished⟩ :=
      qualifiesRef
    obtain ⟨node, kind, dependencies, producer, located, same⟩ := descriptor.owner_known member
    have below := (coherent_node_bounds coherent located).2
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (same ▸ below),
      by simpa only [decide_eq_true_eq] using (show qualifies ref from
        ⟨healthy, task, taskOwners, birth, result, descriptor, member, unfinished⟩)⟩
  obtain ⟨owner, member, healthy, _⟩ := explained.outstanding_owner known
    (coherent_task_owners_nonempty coherent known) outstanding
  have original : owner ∈ refs := inRefs ⟨healthy, occurrence, owners, producer, payload,
    known, member, outstanding⟩
  obtain ⟨ref, selected, least⟩ := nonempty_refs_minimum refs
    (by intro empty; simp [empty] at original)
  have qualifiesRef : qualifies ref := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp selected).2
  obtain ⟨healthy, task, taskOwners, birth, result, descriptor, member, unfinished⟩ := qualifiesRef
  obtain ⟨next, nextOwners, nextProducer, result, nextRef, readyTask, ready,
    nextMember, nextHealthy, smaller⟩ := readyTask_owner_ref_le explained valid coherent continuous
      ordered descriptor member healthy unfinished
  have nextOutstanding : ¬TaskAccounted work matching events
      failures next := by
    rintro (cancelled | published)
    · exact ready.2.1 cancelled
    · exact ready.1 published
  have minimum := least nextRef (inRefs ⟨nextHealthy, next, nextOwners, nextProducer,
    result, readyTask, nextMember, nextOutstanding⟩)
  have same : nextRef = ref := Nat.le_antisymm smaller minimum
  subst nextRef
  refine ⟨next, nextOwners, nextProducer, result, ref, readyTask, ready,
    nextMember, nextHealthy, ?_⟩
  intro other before otherHealthy task taskOwners projected contributes
  obtain ⟨birth, payload, taskKnown⟩ := projected
  apply Classical.byContradiction
  intro unaccounted
  have lower := least other (inRefs ⟨otherHealthy, task, taskOwners, birth, payload,
    taskKnown, contributes, unaccounted⟩)
  exact Nat.not_lt_of_ge lower before

-----------------------------------------------------------------------------------------
-- Smaller dependencies can be discharged in a maximal history
-----------------------------------------------------------------------------------------

/-- In a maximal explained history, a healthy accounted ref satisfies dependencies.
Witness: an announced but uncompleted such ref would permit a success completion.
Absent or unannounced accounted refs already satisfy the public dependency rule.
-/
theorem maximal_dependency_satisfied {work groups streams events matching failures ref}
    (explained : Explains work groups streams events matching failures)
    (maximal
      : ∀ event next cuts, ¬Explains work groups streams (events ++ [event]) next cuts)
    (healthy : ¬NodeFailed work matching events failures ref)
    (accounted : NodeAccounted work matching events failures ref)
    : DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching events
        failures ref := by
  classical
  refine ⟨healthy, ?_⟩
  by_cases supported : ∃ birth, NodeHasProducer work ref birth
  · by_cases notified : ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events
    · by_cases closed : ref ∈ completedRefs events
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

/-- A fresh healthy owner of a ready task is announceable once smaller healthy refs
satisfy dependencies. Witness: strict ancestry/stream-dependency ordering and causal failure
rules; the task itself witnesses that a group is not already fully accounted for.
-/
theorem least_owner_announceable
    {parents bound work groups streams initial matching events failed occurrence owners
      producer payload node kind dependencies}
    (explained : Explains work groups streams events matching failed)
    (valid : Valid parents bound) (coherent : MixedRefs.WorkAt parents 0 bound work)
    (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners producer payload)
    (ready : CanPublish work matching events failed occurrence producer)
    (descriptor : NodeAt work node kind dependencies producer)
    (member : node.ref ∈ owners)
    (healthy : ¬NodeFailed work matching events failed node.ref)
    (fresh : node.ref ∉ announcedRefs initial events)
    (smaller
      : ∀ ref,
          ref < node.ref
          → ¬NodeFailed work matching events failed ref
          → DependencySatisfied work initial matching events failed ref)
    : CanAnnounce work initial matching events failed node kind dependencies
        producer := by
  classical
  refine ⟨fresh, Or.inl ⟨healthy, ?_⟩, ready.2.2.1, ?_⟩
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
        intro ref member
        exact smaller ref (coherent_group_dependencies valid coherent descriptor ref member)
          (fun failure => healthy (.groupDependency descriptor member failure))
    | stream =>
        by_cases empty : dependencies = []
        · exact Or.inl empty
        · have healthyParent
              : ∃ ref ∈ dependencies, ¬NodeFailed work matching events failed ref := by
            apply Classical.byContradiction
            intro absent
            apply healthy
            apply explained.snapshot_nodeFailed
            apply Causality.NodeFailed.streamDependencies ⟨_, _, descriptor, rfl⟩ empty
            intro ref member
            apply explained.nodeFailed_snapshot
            apply Classical.byContradiction
            intro healthyRef
            exact absent ⟨ref, member, healthyRef⟩
          obtain ⟨ref, member, healthyRef⟩ := healthyParent
          exact Or.inr ⟨ref, member,
            smaller ref (coherent_stream_dependencies ordered descriptor ref member) healthyRef⟩

/-- A maximal incomplete generated-work history still has a currently eligible notice.
Witness: choose a least healthy outstanding owner, descend to a ready task without
increasing its ref, discharge smaller dependencies, and exclude already-announced owners
using the constructed success/failure extension. MixedExistence supplies notice carriers
by maximizing histories with a separate supported-coverage witness.
-/
theorem maximal_outstanding_eligible
    {parents bound paths pathBound work groups streams events matching failures
      occurrence owners producer payload}
    (valid : Valid parents bound) (coherent : MixedRefs.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (explained : Explains work groups streams events matching failures)
    (maximal
      : ∀ event next cuts, ¬Explains work groups streams (events ++ [event]) next cuts)
    (known : TaskAt work occurrence owners producer payload)
    (outstanding : ¬TaskAccounted work matching events failures occurrence)
    : ∃ node kind dependencies birth,
        NodeAt work node kind dependencies birth
        ∧ CanAnnounce work ((groups ++ streams).map DeliveryNode.ref) matching events
            failures node kind dependencies birth := by
  obtain ⟨next, nextOwners, nextProducer, result, ref, task, ready,
    member, healthy, least⟩ := least_ready_owner valid coherent continuous ordered
      explained known outstanding
  have unannounced : ref ∉ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events := by
    intro notified
    obtain ⟨event, nextMatching, cuts, extended⟩ := extend_ready_announced pathCoherent
      explained task ready ⟨ref, member, notified, healthy⟩
    exact maximal event nextMatching cuts extended
  obtain ⟨node, kind, dependencies, descriptor, same⟩ := task.owner_at_producer member
  refine ⟨node, kind, dependencies, nextProducer, descriptor, ?_⟩
  apply least_owner_announceable explained valid coherent ordered task ready descriptor
    (same ▸ member) (same ▸ healthy) (same ▸ unannounced)
  intro smaller before smallerHealthy
  apply maximal_dependency_satisfied explained maximal smallerHealthy
  exact least smaller (by simpa only [same] using before) smallerHealthy

/-- A maximal generated-work history with no eligible unannounced notices is terminal.
Witness: the least-ref obstruction rules out outstanding tasks, then every open node
would admit a completion. This is a conditional criterion, not a scheduler assumption.
The general mixed-run construction uses the weaker supported-notice coverage witness.
-/
theorem maximal_no_eligible_terminal
    {parents bound paths pathBound work groups streams events matching failures}
    (valid : Valid parents bound) (coherent : MixedRefs.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (explained : Explains work groups streams events matching failures)
    (maximal
      : ∀ event next cuts, ¬Explains work groups streams (events ++ [event]) next cuts)
    (noticesCovered
      : ∀ node kind dependencies birth,
          NodeAt work node kind dependencies birth
          → ¬CanAnnounce work ((groups ++ streams).map DeliveryNode.ref) matching events
              failures node kind dependencies birth)
    : Terminal work ((groups ++ streams).map DeliveryNode.ref) matching events
        failures := by
  classical
  have accounted : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload →
      TaskAccounted work matching events failures occurrence := by
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
      failures node.ref := by
    rintro occurrence owners ⟨producer, payload, known⟩ _
    exact accounted occurrence owners producer payload known
  by_cases closed : node.ref ∈ completedRefs events
  · exact Or.inl closed
  · refine Or.inr ⟨?_, Or.inr nodeAccounted⟩
    intro announced
    obtain ⟨event, allowed, _, _, _⟩ := completion_exists descriptor
      ⟨announced, closed⟩ nodeAccounted
      (by simpa only [explained.2.1.failedBefore_eq (Nat.le_refl _)]
        using explained.2.1.known)
    exact maximal event matching failures (explained.append_event allowed)

end GraphQL.IncrementalDelivery.Correctness
