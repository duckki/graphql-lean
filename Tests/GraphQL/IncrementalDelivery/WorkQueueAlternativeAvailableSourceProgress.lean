import Tests.GraphQL.IncrementalDelivery.Fixtures.AvailableSourceDisposal
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableSourceDrain

/-! Cached startup accounts for a held source and both newly available failure counts. -/

namespace GraphQL.IncrementalDelivery.Tests.AvailableSourceDisposal
open AlternativeWorkQueue AlternativeWorkQueue.NativeRefinement

private theorem keys : initial.queue.TaskNodeKeysUnique := by
  simp [ReferenceWorkQueue.State.TaskNodeKeysUnique, initial, buffered,
    producer, firstFailure, secondFailure]

private theorem represented
    : RecordTargetRepresented initial.queue (.stream source.ref) :=
  .bufferedStream (occurrence := producer) (node := buffered) (by cbv) rfl
    List.mem_cons_self

example
    : RecordTargetRepresented closed.1.queue (.stream source.ref)
      ∨ .stream source.ref ∈ closed.2.1 :=
  sourceRecord_startNewWork_available initial keys ⟨[owner], []⟩ {} [] available
    represented

example : closed.1.queue.groupNodes = [] := by cbv
example : closed.2.1 = [.task producer, .stream source.ref] := by cbv
example : closed.2.2 = [⟨owner, 5⟩] := by cbv

#print axioms sourceRecord_startGroup_available
#print axioms sourceRecord_startNewWork_available
#print axioms sourceRecord_drainReadyGroups_available

end GraphQL.IncrementalDelivery.Tests.AvailableSourceDisposal
