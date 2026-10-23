import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedUnsettledTaskDrain
import Tests.GraphQL.IncrementalDelivery.Fixtures.AvailableTaskDisposal

/-! Cache exposure before notification causes inline cleanup only for unfinished tasks. -/

namespace AlternativeAvailableTaskProgressChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue.NativeRefinement
open Tests.AvailableTaskDisposal

example : (state.queue.taskNode? failed.occurrence).bind (·.rejection) = none := by cbv

example : (state.startGroup group.ref [] available).1.queue.groupNodes = [] := by cbv

-- A cached rejected computation has finished; only the unfinished companion task is aborted.
example : (state.startGroup group.ref [] available).2.1 = [.task waiting.occurrence] := by
  cbv

example
    : (state.startGroup group.ref [] available).2.2.map
        (fun notice =>
          (notice.group.ref, notice.errors))
      = [(group.ref, 2)] := by cbv

example : (state.startGroup group.ref).2.1 = [] := by cbv
example : (state.startGroup group.ref).2.2 = [] := by cbv

#print axioms startGroup_linkedTask_progress_available
#print axioms startNewWork_linkedTask_progress_available
#print axioms fusedUnsettledDrainProgress_available
#print axioms FusedUnsettledDrainProgress_holds

end AlternativeAvailableTaskProgressChecks
