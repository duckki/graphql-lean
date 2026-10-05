import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedWork
import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskAttachmentPaths

/-! Execution-generated locality connects concrete cancellation to observable scopes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every executed work tree retains producer-local response attachment bounds.
Witness: the root-completion path certificate, instantiated at the generating execution.
No event-source premise, queue state, or conformance assumption is used.
-/
theorem ExecutedWork.attachments_under {work : Execution.Work}
    (generated : ExecutedWork work)
    : Correctness.ExecutionPaths.WorkUnder [] work := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source, selections,
    equal⟩ := generated
  have under := Correctness.ExecutionPaths.executeRootSelectionSetCore_under
    schema resolvers variables fuel parentType source selections 0
  change Correctness.ExecutionPaths.WorkUnder [] _ at under
  rwa [equal] at under

/-- Generated child tasks lie below their producer's attachment.
Witness: root-completion locality and the located producer's functional task identity.
-/
theorem ExecutedWork.producer_attachment_prefix
    {work occurrence owners producer payload parentOwners ancestor parentPayload}
    (generated : ExecutedWork work)
    (known : TaskAt work occurrence owners (some producer) payload)
    (parent : TaskAt work producer parentOwners ancestor parentPayload)
    : parentPayload.path.IsPrefix payload.path :=
  generated.attachments_under.producer_prefix known parent

/-- A producer failure scope covers cancelled descendant work without another notice.
Witness: generated attachment prefixes retain the same positive-error completion event.
This is a propagation lemma, not an assumption that every cancellation has a report.
-/
theorem ExecutedWork.producer_failure_reported
    {work occurrence owners producer payload parentOwners ancestor parentPayload events}
    (generated : ExecutedWork work)
    (known : TaskAt work occurrence owners (some producer) payload)
    (parent : TaskAt work producer parentOwners ancestor parentPayload)
    (reported : FailureReportedFor events parentPayload.path)
    : FailureReportedFor events payload.path :=
  generated.attachments_under.producer_reported known parent reported

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
