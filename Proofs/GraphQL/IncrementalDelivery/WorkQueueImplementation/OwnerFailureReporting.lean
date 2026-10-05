import Proofs.GraphQL.IncrementalDelivery.Correctness.OwnerScopeInheritance
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedMixedOwners
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedDescriptors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedWork

/-! Ref-based group-report evidence yields a covering generated attachment scope. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Execution supplies path and full-ancestor metadata independently of queue admission
-----------------------------------------------------------------------------------------

/-- Executed work has one coherent assignment of owner refs to attachment paths.
Witness: the mixed defer/stream root-execution metadata theorem, without success premises.
-/
theorem ExecutedWork.ownerPathAssignment {work : Execution.Work}
    (generated : ExecutedWork work)
    : ∃ paths bound, Semantics.MixedOwnerPaths.WorkAt paths bound work := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source, selections,
    equal⟩ := generated
  obtain ⟨paths, coherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners
    schema resolvers variables fuel parentType source selections 0
  exact ⟨paths, _, equal ▸ coherent⟩

/-- An actual owner or one of its full defer ancestors has a positive error completion.
`events` is the unchanged output history; `owner` and `dependencies` are structural group
metadata. This proof-only target is about ref-based closure provenance, not data coverage.
-/
def GroupFailureReported (events : List Execution.WorkQueueEvent)
    (owner : Execution.DeliveryNode) (dependencies : NodeRefs)
    : Prop :=
  ∃ reporter errors,
    0 < errors
    ∧ .groupFailure reporter errors ∈ events
    ∧ (reporter.ref = owner.ref ∨ reporter.ref ∈ dependencies)

/-- A group-report origin remains valid after more outputs are observed.
Witness: retain the exact positive-error closure and its ancestor-ref relationship.
-/
theorem GroupFailureReported.append {events owner dependencies}
    (reported : GroupFailureReported events owner dependencies)
    (tail : List Execution.WorkQueueEvent)
    : GroupFailureReported (events ++ tail) owner dependencies := by
  obtain ⟨reporter, errors, positive, member, ancestor⟩ := reported
  exact ⟨reporter, errors, positive, List.mem_append_left _ member, ancestor⟩

-----------------------------------------------------------------------------------------
-- Ref accounting does not need to assume the resulting response path coverage
-----------------------------------------------------------------------------------------

/-- A reported contributor or defer ancestor covers the execution group's attachment.
Witness: locate the actual admitted failure event, then use execution-derived owner-path
and full-ancestor metadata. The contributing group may itself remain unannounced.
No terminal reporting or response-reconstruction law is assumed.
-/
theorem ExecutedWork.groupReport_covers_task
    {work groups streams events matching failures address owners producer payload
      owner dependencies birth}
    (generated : ExecutedWork work)
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (ownerKnown : NodeAt work owner .group dependencies birth)
    (contributes : owner.ref ∈ owners)
    (reported : GroupFailureReported events owner dependencies)
    : FailureReportedFor events payload.path := by
  obtain ⟨reporter, errors, positive, member, ancestor⟩ := reported
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨parents, parent, reporterKnown⟩ := (explained.2.2 index _ selected).1
  have scope : FailureReportedFor events reporter.path :=
    ⟨reporter, errors, positive, ⟨[], by simp⟩, Or.inl member⟩
  obtain ⟨paths, bound, coherent⟩ := generated.ownerPathAssignment
  rcases ancestor with same | above
  · have equal := generated.nodeRefCoherent _ _ _ _ _ _ _ _ reporterKnown ownerKnown same
    rw [equal] at scope
    exact Correctness.reported_owner_covers_task coherent known ownerKnown contributes scope
  · obtain ⟨ancestors, canonical⟩ := generated.groupDependenciesCanonical
    exact Correctness.reported_owner_ancestor_covers_task coherent canonical known
      ownerKnown contributes reporterKnown above scope

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
