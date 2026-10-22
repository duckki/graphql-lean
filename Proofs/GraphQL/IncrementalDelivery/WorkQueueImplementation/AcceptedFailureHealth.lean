import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedTaskErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SelectedFailureCuts

/-! Failure health follows retained rejections and selected proof cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A live unrejected group has no earlier failed contributor.
Witness: retention would supply a listed rejected task, contradicting the actual lookup.
-/
theorem State.RetainedFailures.uncached_noFailedContributor
    {queue : State} {work failed occurrence owners producer payload} {node : GroupNode}
    (counts : queue.RetainedFailures work failed) (_generated : ExecutedWork work)
    (member : node ∈ queue.groupNodes) (unrejected : queue.rejectedTask? node = none)
    (known : TaskAt work occurrence owners producer payload)
    (_failure : payload.failure.isSome = true) (owner : node.group.node.ref ∈ owners)
    : occurrence ∉ failed :=
  counts.unrejected_noFailedContributor member unrejected ⟨producer, payload, known⟩ owner

/-- A selected failure cut retains an owner without an earlier direct cause.
Witness: the selector's exact-prefix criterion excludes every direct invalidation token.
Coarse source eligibility alone does not imply this property.
-/
theorem informativeFailureCuts_directHealthyOwner {work before after cut occurrence}
    (selected : InformativeFailureCuts work [] (before ++ (cut, occurrence) :: after))
    : ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ ∀ prior priorOwners,
            prior ∈ before.map Prod.snd
            → TaskHasOwners work prior priorOwners
            → owner ∉ priorOwners := by
  obtain ⟨owners, ref, known, owner, healthy⟩ := selected.atCut
  refine ⟨owners, ref, known, owner, ?_⟩
  intro prior priorOwners member task contributes
  exact healthy (.task task contributes member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
