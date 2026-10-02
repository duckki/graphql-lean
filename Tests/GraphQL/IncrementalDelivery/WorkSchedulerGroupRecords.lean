import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerGroupRecords
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : DeliveryNode := ⟨0, [], none⟩
private def wrapper : DeliveryNode := ⟨1, [], none⟩
private def child : DeliveryNode := ⟨2, [], none⟩

private def work : Execution.Work :=
  .executionGroup [⟨child, [wrapper, parent]⟩] [] (.ok ([], 0)) .empty

/-- The intermediate wrapper has a registration descriptor with its own parent.
Witness: its nearest-first ancestor chain is a suffix of the child contributor's chain.
-/
theorem wrapper_record : GroupRecordAt work wrapper [parent.key] := by
  refine ⟨[], [⟨child, [wrapper, parent]⟩], [], .ok ([], 0), .empty, none, [],
    ⟨child, [wrapper, parent]⟩, [parent], rfl, List.mem_cons_self, ?_, rfl⟩
  exact List.suffix_cons _ _

/-- An ancestor record does not assert a task-contributing spec node at that key.
Witness: the finite node-token inventory contains only the actual child contributor.
-/
theorem wrapper_not_nodeAt
    : ¬∃ dependencies producer, NodeAt work wrapper .group dependencies producer := by
  rintro ⟨dependencies, producer, known⟩
  have token := known.observationToken
  simp [observationTokens, work, wrapper, child] at token

/-- Parent descriptors remain available even when neither ancestor owns any task.
Witness: the full-chain parent theorem applied to the wrapper's record.
-/
theorem wrapper_parent_record
    : ∃ node, node.key = parent.key ∧ GroupRecordAt work node [] :=
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
    workFromSpec_groups_recordAt (Located.root (root := work)) member
  exact ⟨dependencies, known⟩

/-- The wrapper is genuinely live in this intermediate state, not a vacuous invariant.
Witness: reduce integration before the separate empty-group pruning phase.
-/
example
    : ((({} : State).maybeIntegrateWork (Work.fromExecution work)).1.groupNode?
        wrapper.key).isSome
      = true := by cbv

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerGroupRecords
