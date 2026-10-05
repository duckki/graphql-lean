import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformancePlan
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedAttachmentPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TaskReadiness

/-! Reduce terminal reporting to tasks whose concrete producer has been released. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The reporting frontier: root work and work released by a published producer
-----------------------------------------------------------------------------------------

/-- Every unpublished task with no producer, or with a published producer, has a covering
positive-error completion in `w.events`. This is a proof-construction target on one shared
witness, not a new source-validity or public conformance premise.
-/
def AvailableTaskReporting (work : Execution.Work) (w : Witness) : Prop :=
  ∀ occurrence owners producer payload,
    TaskAt work occurrence owners producer payload
    → (∀ parent, producer = some parent → Published w.matching w.events parent)
    → ¬Published w.matching w.events occurrence
    → FailureReportedFor w.events payload.path

/-- Reports on the released frontier cover all unpublished generated tasks.
Witness: descend the finite producer rank until reaching root or published-producer work,
then propagate the same covering report down generated attachment prefixes. No terminal
law, internal task-accounting premise, or queue-conformance assumption is used.
-/
theorem cancellationReporting_of_availableTaskReporting
    {work w} (generated : ExecutedWork work)
    (available : AvailableTaskReporting work w)
    : CancellationReporting work w := by
  have all : ∀ rank occurrence owners producer payload,
      occurrence.dependencyRank = rank
      → TaskAt work occurrence owners producer payload
      → ¬Published w.matching w.events occurrence
      → FailureReportedFor w.events payload.path := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
        intro occurrence owners producer payload same known unpublished
        cases producer with
        | none =>
            exact available occurrence owners none payload known
              (fun _ impossible => by cases impossible) unpublished
        | some parent =>
            classical
            by_cases published : Published w.matching w.events parent
            · exact available occurrence owners (some parent) payload known
                (fun candidate equal => by cases equal; exact published) unpublished
            · obtain ⟨lower, parents, ancestor, result, parentKnown⟩ :=
                known.producer_dependency
              have reported := ih parent.dependencyRank (by omega) parent parents ancestor
                result rfl parentKnown published
              exact generated.producer_failure_reported known parentKnown reported
  exact fun occurrence owners producer payload known unpublished =>
    all occurrence.dependencyRank occurrence owners producer payload rfl known unpublished

/-- Released-frontier reporting is exactly the full reporting obligation for generated
work. Witness: restriction in one direction and finite producer-rank propagation in the
other. This reduction does not weaken the public terminal cancellation requirement.
-/
theorem cancellationReporting_iff_availableTaskReporting
    {work w} (generated : ExecutedWork work)
    : CancellationReporting work w ↔ AvailableTaskReporting work w := by
  constructor
  · intro reported occurrence owners producer payload known _ unpublished
    exact reported occurrence owners producer payload known unpublished
  · exact cancellationReporting_of_availableTaskReporting generated

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
