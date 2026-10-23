import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableTaskSourceProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableStreamSourceProgress

/-! Prepared-source progress at an actual exposed source cut, with supplied availability. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

/-- Registration-bearing inputs, named independently of their source-validity evidence. -/
def RegistrationInput : GraphEvent → Prop
  | .taskSuccess _ _ | .streamItems _ _ => True
  | _ => False

/-- Both registration-bearing handlers retain a prepared source record or cancel it in
their actual effect trace. The source queue has already exposed the complete host snapshot.
-/
theorem sourceFrame_preparedSource_progress_available {queue : ReferenceWorkQueue.State}
    {work parents before event key} (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (source : ReferenceWorkQueue.UncancelledReplayFrame queue work parents before)
    (keys : queue.TaskNodeKeysUnique) (inventory : queue.ChildStreamInventory)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ [event]))
    (release : RegistrationInput event) (available : List (Occurrence × Nat))
    (cached : queue.cacheTaskFailures available = queue)
    (represented
      : RecordTargetRepresented (registrationSnapshot queue event available)
          (.stream key))
    : let reduced := ({ queue } : State).handleGraphEvent event available
      RecordTargetRepresented reduced.1.queue (.stream key)
      ∨ .cancelSource key ∈ reduced.2.2.1 := by
  dsimp only
  cases event with
  | taskSuccess incoming result =>
      simp only [State.handleGraphEvent, cached]
      exact sourceFrame_taskSuccess_sourceRecord_available generated canonical source keys inventory
        incoming result valid available represented
  | streamItems stream items =>
      simp only [State.handleGraphEvent, cached]
      exact sourceFrame_streamItems_sourceRecord_available generated canonical source keys inventory
        stream items (ReferenceWorkQueue.validGraphEvents_last valid).2.1 available represented
  | taskFailure | groupFailure | streamSuccess | streamFailure => cases release

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
