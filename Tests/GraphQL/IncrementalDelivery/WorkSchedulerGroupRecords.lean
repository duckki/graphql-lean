import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Tests.GraphQL.IncrementalDelivery.Fixtures.WorkDeclarations

open GraphQL.IncrementalDelivery.Tests (declaredTask)

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerGroupRecords
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : DeliveryNode := ⟨0, [], none⟩
private def wrapper : DeliveryNode := ⟨1, [], none⟩
private def child : DeliveryNode := ⟨2, [], none⟩

private def work : Execution.Work :=
  declaredTask [⟨child, [wrapper, parent]⟩] [] ({ result := .ok ([], 0) }) .empty

/-- The intermediate wrapper has a registration descriptor with its own parent.
Witness: its nearest-first ancestor chain is a suffix of the child contributor's chain.
-/
theorem wrapper_record : GroupRecordAt work wrapper [parent.ref] := by
  refine ⟨⟨child, [wrapper, parent]⟩, ?_, [parent], ?_, rfl⟩
  · simp [GroupMetadata.fragments, work, declaredTask, declaredTask.chain]
  · exact List.suffix_cons _ _

/-- An ancestor record does not assert a task-contributing spec node at that ref.
Witness: the finite node-token inventory contains only the actual child contributor.
-/
theorem wrapper_not_nodeAt
    : ¬∃ dependencies producer, NodeAt work wrapper .group dependencies producer := by
  rintro ⟨dependencies, producer, known⟩
  have token := known.observationToken
  simp [observationTokens, work, declaredTask, wrapper, child] at token

/-- Parent descriptors remain available even when neither ancestor owns any task.
Witness: the full-chain parent theorem applied to the wrapper's record.
-/
theorem wrapper_parent_record
    : ∃ node, node.ref = parent.ref ∧ GroupRecordAt work node [] :=
  wrapper_record.parent

/-- The integration invariant permits taskless records before pruning.
Witness: exact lowering provenance, followed by the general integration preservation law.
-/
theorem integrated_records
    : (({} : State).maybeIntegrateWork (Work.fromExecution work)).1.GroupNodesMatchWork
        work := by
  have empty : ({} : State).GroupNodesMatchWork work := by
    intro node member
    cases member
  apply empty.maybeIntegrateWork
  intro group member
  obtain ⟨dependencies, known, _⟩ :=
    workFromSpec_groups_recordAt_root member
  exact ⟨dependencies, known⟩

/-- The wrapper is genuinely live in this intermediate state, not a vacuous invariant.
Witness: reduce integration before the separate empty-group pruning phase.
-/
example
    : ((({} : State).maybeIntegrateWork (Work.fromExecution work)).1.groupNode?
        wrapper.ref).isSome
      = true := by cbv

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerGroupRecords
