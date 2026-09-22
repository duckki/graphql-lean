import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Causality

/-! Retained failure notices broaden only group announcement, not successful delivery. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

/-- A recorded contributing failure already makes its owner failed.
Witness: the existing direct task-failure rule at the recorded cut, for any matching.
-/
theorem HasRecordedFailure.nodeFailed {work failures events key}
    (recorded : HasRecordedFailure work failures events.length key)
    (matching : PublicationMatching)
    : NodeFailed work matching events failures key := by
  obtain ⟨occurrence, owners, finished, ⟨producer, payload, known⟩, owner⟩ := recorded
  exact NodeFailed.task known owner finished

/-- With no recorded contributing failure, the original announcement conditions suffice
and remain necessary. Witness: the added branch is false, leaving the original conjunction.
-/
theorem canAnnounce_iff_of_no_recorded_failure
    {work initial matching events failures node kind dependencies producer}
    (absent : ¬HasRecordedFailure work failures events.length node.key)
    : CanAnnounce work initial matching events failures node kind dependencies producer
      ↔ node.key ∉ announcedKeys initial events
        ∧ ¬NodeFailed work matching events failures node.key
        ∧ (kind = .stream ∨ ¬NodeAccounted work matching events failures node.key)
        ∧ (∀ source, producer = some source → Published matching events source)
        ∧ match kind with
          | .group =>
              ∀ key ∈ dependencies,
                DependencySatisfied work initial matching events failures key
          | .stream =>
              dependencies = []
              ∨ ∃ key ∈ dependencies,
                  DependencySatisfied work initial matching events failures key := by
  cases kind <;> simp [CanAnnounce, absent, and_assoc]

/-- Empty failure evidence leaves initialization eligibility exactly as before.
Witness: no occurrence belongs to an empty list of recorded failures.
-/
theorem canAnnounce_emptyFailures_iff
    (work initial matching events node kind dependencies producer)
    : CanAnnounce work initial matching events [] node kind dependencies producer
      ↔ node.key ∉ announcedKeys initial events
        ∧ ¬NodeFailed work matching events [] node.key
        ∧ (kind = .stream ∨ ¬NodeAccounted work matching events [] node.key)
        ∧ (∀ source, producer = some source → Published matching events source)
        ∧ match kind with
          | .group =>
              ∀ key ∈ dependencies,
                DependencySatisfied work initial matching events [] key
          | .stream =>
              dependencies = []
              ∨ ∃ key ∈ dependencies,
                  DependencySatisfied work initial matching events [] key := by
  cases kind <;> simp [CanAnnounce, HasRecordedFailure, failedBefore, and_assoc]

/-- Streams retain their original fresh, healthy, producer, and dependency conditions.
Witness: the added eligibility branch is restricted to the distinct group constructor.
-/
theorem canAnnounce_stream_iff
    (work initial matching events failures node dependencies producer)
    : CanAnnounce work initial matching events failures node .stream dependencies producer
      ↔ node.key ∉ announcedKeys initial events
        ∧ ¬NodeFailed work matching events failures node.key
        ∧ (∀ source, producer = some source → Published matching events source)
        ∧ (dependencies = []
            ∨ ∃ key ∈ dependencies,
                DependencySatisfied work initial matching events failures key) := by
  simp [CanAnnounce]

/-- Healthy nodes cannot use the retained-failure exception.
Witness: a recorded contributor would contradict health through the direct failure rule.
-/
theorem canAnnounce_healthy_iff
    {work initial matching events failures node kind dependencies producer}
    (healthy : ¬NodeFailed work matching events failures node.key)
    : CanAnnounce work initial matching events failures node kind dependencies producer
      ↔ node.key ∉ announcedKeys initial events
        ∧ (kind = .stream ∨ ¬NodeAccounted work matching events failures node.key)
        ∧ (∀ source, producer = some source → Published matching events source)
        ∧ match kind with
          | .group =>
              ∀ key ∈ dependencies,
                DependencySatisfied work initial matching events failures key
          | .stream =>
              dependencies = []
              ∨ ∃ key ∈ dependencies,
                  DependencySatisfied work initial matching events failures key := by
  have absent : ¬HasRecordedFailure work failures events.length node.key :=
    fun recorded => healthy (recorded.nodeFailed matching)
  cases kind <;> simp [CanAnnounce, healthy, absent]

/-- A retained failure notice does not make its group a healthy publication supporter.
Witness: available owners must be healthy, contradicting the recorded failure.
-/
theorem HasRecordedFailure.not_availableOwner
    {work initial matching events failures node owners}
    (recorded : HasRecordedFailure work failures events.length node.key)
    : ¬HealthyOpenOwner work initial matching events failures owners node := by
  intro owner
  exact owner.2 (recorded.nodeFailed matching)

/-- A failed dependency still blocks a group's notice, including the new failure branch.
Witness: both announcement alternatives retain the same dependency-health requirement.
-/
theorem canAnnounce_group_dependency_healthy
    {work initial matching events failures node dependencies producer key}
    (notice
      : CanAnnounce work initial matching events failures node .group
          dependencies producer)
    (member : key ∈ dependencies)
    : ¬NodeFailed work matching events failures key :=
  (notice.2.2.2 key member).1

end GraphQL.IncrementalDelivery.WorkQueueSemantics
