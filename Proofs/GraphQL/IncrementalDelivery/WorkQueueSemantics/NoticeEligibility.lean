import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Causality

/-! Retained failure notices broaden only group announcement, not successful delivery. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

/-- A recorded contributing failure already makes its owner failed.
Witness: the existing direct task-failure rule at the recorded cut, for any matching.
-/
theorem HasRecordedFailure.nodeFailed {work failures events ref}
    (recorded : HasRecordedFailure work failures events.length ref)
    (matching : PublicationMatching)
    : NodeFailed work matching events failures ref := by
  obtain ⟨occurrence, owners, finished, ⟨producer, payload, known⟩, owner⟩ := recorded
  exact NodeFailed.task known owner finished

/-- With no recorded contributing failure, the original announcement conditions suffice
and remain necessary. Witness: the added branch is false, leaving the original conjunction.
-/
theorem canAnnounce_iff_of_no_recorded_failure
    {work initial matching events failures node kind dependencies producer}
    (absent : ¬HasRecordedFailure work failures events.length node.ref)
    : CanAnnounce work initial matching events failures node kind dependencies producer
      ↔ node.ref ∉ announcedRefs initial events
        ∧ ¬NodeFailed work matching events failures node.ref
        ∧ (kind = .stream ∨ ¬NodeAccounted work matching events failures node.ref)
        ∧ (∀ source, producer = some source → Published matching events source)
        ∧ match kind with
          | .group =>
              ∀ ref ∈ dependencies,
                DependencySatisfied work initial matching events failures ref
          | .stream =>
              dependencies = []
              ∨ ∃ ref ∈ dependencies,
                  DependencySatisfied work initial matching events failures ref := by
  cases kind <;> simp [CanAnnounce, absent, and_assoc]

/-- Empty failure evidence leaves initialization eligibility exactly as before.
Witness: no occurrence belongs to an empty list of recorded failures.
-/
theorem canAnnounce_emptyFailures_iff
    (work initial matching events node kind dependencies producer)
    : CanAnnounce work initial matching events [] node kind dependencies producer
      ↔ node.ref ∉ announcedRefs initial events
        ∧ ¬NodeFailed work matching events [] node.ref
        ∧ (kind = .stream ∨ ¬NodeAccounted work matching events [] node.ref)
        ∧ (∀ source, producer = some source → Published matching events source)
        ∧ match kind with
          | .group =>
              ∀ ref ∈ dependencies,
                DependencySatisfied work initial matching events [] ref
          | .stream =>
              dependencies = []
              ∨ ∃ ref ∈ dependencies,
                  DependencySatisfied work initial matching events [] ref := by
  cases kind <;> simp [CanAnnounce, HasRecordedFailure, failedBefore, and_assoc]

/-- Streams retain their original fresh, healthy, producer, and dependency conditions.
Witness: the added eligibility branch is restricted to the distinct group constructor.
-/
theorem canAnnounce_stream_iff
    (work initial matching events failures node dependencies producer)
    : CanAnnounce work initial matching events failures node .stream dependencies producer
      ↔ node.ref ∉ announcedRefs initial events
        ∧ ¬NodeFailed work matching events failures node.ref
        ∧ (∀ source, producer = some source → Published matching events source)
        ∧ (dependencies = []
            ∨ ∃ ref ∈ dependencies,
                DependencySatisfied work initial matching events failures ref) := by
  simp [CanAnnounce]

/-- Healthy nodes cannot use the retained-failure exception.
Witness: a recorded contributor would contradict health through the direct failure rule.
-/
theorem canAnnounce_healthy_iff
    {work initial matching events failures node kind dependencies producer}
    (healthy : ¬NodeFailed work matching events failures node.ref)
    : CanAnnounce work initial matching events failures node kind dependencies producer
      ↔ node.ref ∉ announcedRefs initial events
        ∧ (kind = .stream ∨ ¬NodeAccounted work matching events failures node.ref)
        ∧ (∀ source, producer = some source → Published matching events source)
        ∧ match kind with
          | .group =>
              ∀ ref ∈ dependencies,
                DependencySatisfied work initial matching events failures ref
          | .stream =>
              dependencies = []
              ∨ ∃ ref ∈ dependencies,
                  DependencySatisfied work initial matching events failures ref := by
  have absent : ¬HasRecordedFailure work failures events.length node.ref :=
    fun recorded => healthy (recorded.nodeFailed matching)
  cases kind <;> simp [CanAnnounce, healthy, absent]

/-- A retained failure notice does not make its group a healthy publication supporter.
Witness: available owners must be healthy, contradicting the recorded failure.
-/
theorem HasRecordedFailure.not_availableOwner
    {work initial matching events failures node owners}
    (recorded : HasRecordedFailure work failures events.length node.ref)
    : ¬HealthyOpenOwner work initial matching events failures owners node := by
  intro owner
  exact owner.2 (recorded.nodeFailed matching)

/-- A failed dependency still blocks a group's notice, including the new failure branch.
Witness: both announcement alternatives retain the same dependency-health requirement.
-/
theorem canAnnounce_group_dependency_healthy
    {work initial matching events failures node dependencies producer ref}
    (notice
      : CanAnnounce work initial matching events failures node .group
          dependencies producer)
    (member : ref ∈ dependencies)
    : ¬NodeFailed work matching events failures ref :=
  (notice.2.2.2 ref member).1

end GraphQL.IncrementalDelivery.WorkQueueSemantics
