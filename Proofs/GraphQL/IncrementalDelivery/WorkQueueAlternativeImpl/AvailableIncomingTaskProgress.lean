import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IncomingTaskProgress

/-! Accepted incoming task records at actual exposed FIFO cuts with batch-wide exclusions. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

/-- A fresh accepted task outside the batch's outcome set retains a record or receives
the same dispatch's abort. Consumed outcomes and future cache availability stay distinct.
-/
theorem sourceFrame_acceptedTask_progress_available {queue : ReferenceWorkQueue.State}
    {work parents before event excluded task}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (source : ReferenceWorkQueue.UncancelledReplayFrame queue work parents before)
    (accounted
      : queue.PendingAccounting work
          (ReferenceWorkQueue.GraphEvent.taskSettlements before))
    (keys : queue.TaskNodeKeysUnique)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ [event]))
    (included
      : (event.recordTaskOutcome
          (ReferenceWorkQueue.GraphEvent.taskSettlements before)).Subset
          excluded)
    (rejections : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ∈ excluded))
    (available : List (Occurrence × Nat))
    (cached : queue.cacheTaskFailures available = queue)
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ excluded)
    (returned : task ∈ acceptedChildTasks queue event)
    (pending : task.occurrence ∉ excluded)
    : let reduced := ({ queue } : State).handleGraphEvent event available
      RecordTargetRepresented reduced.1.queue (.task task.occurrence)
      ∨ .abortTask task.occurrence ∈ reduced.2.2.1 := by
  dsimp only
  have beforeIncluded
      : (ReferenceWorkQueue.GraphEvent.taskSettlements before).Subset excluded := by
    intro occurrence member
    apply included
    cases event with
    | taskSuccess | taskFailure => exact List.mem_cons_of_mem _ member
    | streamItems | groupFailure | streamSuccess | streamFailure => exact member
  have registered := registrationSnapshot_acceptedTask_registered_available returned available
  by_cases owned :
    ∃ owner ∈ task.groups,
      ∃ group,
        (registrationSnapshot queue event available).groupNode? owner.ref = some group
  · exact sourceFrame_preparedTask_progress_available generated canonical source accounted keys
      valid available cached
      (rejections.mono (fun occurrence _ member same => pending (same ▸ member)))
      (fun occurrence errors member same => pending (same ▸ licensed occurrence errors member))
      registered (fun member => pending (included member)) owned
  · have ownerless : ∀ owner ∈ task.groups,
        (registrationSnapshot queue event available).groupNode? owner.ref = none := by
      intro owner member
      cases found : (registrationSnapshot queue event available).groupNode? owner.ref with
      | none => rfl
      | some group => exact False.elim (owned ⟨owner, member, group, found⟩)
    exact .inr
      (registration_rejectedTask_aborted_available
        (SourceRegistrationFrame.of_pendingAccounting
          (pendingAccounting_weakenSettled accounted beforeIncluded))
        generated.declarations (ReferenceWorkQueue.validGraphEvents_last valid).2.1
        pending returned rejections available cached licensed ownerless)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
