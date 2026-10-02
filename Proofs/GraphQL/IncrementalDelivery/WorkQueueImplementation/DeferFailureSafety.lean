import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureLicensing
import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferDependencies
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedStreamOwnerKeys

/-! Owner health alone licenses failures in generated defer-only work. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling

-----------------------------------------------------------------------------------------
-- Generated defer continuity transports cancellation to every contributing owner
-----------------------------------------------------------------------------------------

/-- Pure execution supplies the static ancestry and producer-support certificates.
Witness: instantiate the existing continuity and stream-owner ordering theorems at
the generating root. These are derived metadata, not extra event-source premises.
-/
theorem ExecutedWork.producerMetadata {work : Execution.Work}
    (generated : ExecutedWork work)
    : ∃ parents bound,
        MixedKeys.WorkAt parents 0 bound work
        ∧ DeferContinuous parents work
        ∧ StreamOwnersOrdered work := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, same⟩ := generated
  obtain ⟨_, parents, _, coherent, continuous⟩ :=
    executeRoot_continuity schema resolvers variables fuel parentType source selections 0
  have ordered := executeRoot_streamOwnersOrdered schema resolvers variables fuel
    parentType source selections 0
  exact ⟨parents, _, same ▸ coherent, same ▸ continuous, same ▸ ordered⟩

/-- Cancellation fails every owner in generated defer-only work, including shared owners.
Witness: execution supplies the ancestry certificate for the existing causal induction.
No output admission, publication support, or failure-licensing premise is used.
-/
theorem ExecutedWork.defer_cancelled_owner_failed
    {work matching events failures occurrence owners producer payload key}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    (known : TaskAt work occurrence owners producer payload) (owner : key ∈ owners)
    (cancelled : TaskCancelled work matching events failures occurrence)
    : NodeFailed work matching events failures key := by
  obtain ⟨parents, bound, coherent, continuous, ordered⟩ := generated.producerMetadata
  exact shape.cancelled_owner_failed coherent continuous ordered known owner cancelled

/-- A cancelled producer fails a defer-only child's contributing owner as well.
Witness: every producer owner fails, and generated defer continuity makes the child's
owner reuse or depend on one of them. The producer need not have published.
-/
theorem ExecutedWork.defer_cancelled_producer_fails_owner
    {work matching events failures occurrence owners producer payload key}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    (known : TaskAt work occurrence owners (some producer) payload) (owner : key ∈ owners)
    (cancelled : TaskCancelled work matching events failures producer)
    : NodeFailed work matching events failures key := by
  obtain ⟨parents, bound, coherent, continuous, ordered⟩ := generated.producerMetadata
  obtain ⟨_, producerOwners, ancestor, result, task⟩ := known.producer_dependency
  exact shape.producer_failure coherent continuous ordered known owner task
    (fun key member => shape.cancelled_owner_failed coherent continuous ordered
      task member cancelled)

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Cut-local owner health suffices for defer-only licensing
-----------------------------------------------------------------------------------------

/-- Defer-only owner health already supplies the producer-safety node at every cut.
Witness: a cancelled producer would fail the healthy contributing owner at that same
ordered prefix. No inventory completeness or publication matching law is required.
-/
theorem failureCutProducerSafety_of_deferOwnerHealth {work w}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    (owners : FailureCutOwnerHealth work w)
    : FailureCutProducerSafety work w := by
  intro before cut occurrence after split producer ⟨ownerKeys, payload, known⟩ cancelled
  obtain ⟨otherOwners, key, ⟨birth, result, other⟩, owner, healthy⟩ :=
    owners before cut occurrence after split
  exact healthy (generated.defer_cancelled_producer_fails_owner shape known
    ((known.unique other).1.symm ▸ owner) cancelled)

/-- For generated defer-only work, healthy contributing owners exclude prior cancellation.
Witness: the existing cancellation-to-owner theorem at each exact ordered prefix.
This discharges the reduction directly, without assuming producer publication or safety.
-/
theorem uncancelledFailures_of_deferOwnerHealth {work w}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    (owners : FailureCutOwnerHealth work w)
    : UncancelledFailures work w := by
  intro before cut occurrence after split cancelled
  obtain ⟨ownerKeys, key, ⟨producer, payload, known⟩, owner, healthy⟩ :=
    owners before cut occurrence after split
  exact healthy (generated.defer_cancelled_owner_failed shape known owner cancelled)

/-- Announced failures are licensed once defer-only owner health is constructed.
Witness: combine the direct cancellation reduction with the existing announced-inventory
equivalence. `GuardHealthCuts` supplies owner health for actual defer-only replay;
mixed-stream conformance remains a separate obligation.
-/
theorem failureWitness_of_deferOwnerHealth {work w}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    (announced : AnnouncedFailures work w) (owners : FailureCutOwnerHealth work w)
    : FailureWitness work (initialKeys work) w.matching w.events w.failures :=
  failureWitness announced
    (uncancelledFailures_of_deferOwnerHealth generated shape owners)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
