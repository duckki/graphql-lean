import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSnapshot
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRejections

/-! Both registration proof views preserve the same occurrence-indexed rejection origins. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- The eager proof view introduces no task rejection. -/
theorem eagerRegistrationSnapshot_taskRejections {queue : ReferenceWorkQueue.State}
    {property} (prior : queue.TaskRejectionsSatisfy property) (event : GraphEvent)
    : (eagerRegistrationSnapshot queue event).TaskRejectionsSatisfy property := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [eagerRegistrationSnapshot, found] using prior
      | some node =>
          simp only [eagerRegistrationSnapshot, found]
          exact (prior.putTaskNode { node with value := some result.value }
            (prior node (List.mem_of_find?_eq_some found))).maybeIntegrateWork
            result.work (some occurrence)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [eagerRegistrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] using prior
      | true =>
          rw [eagerRegistrationSnapshot_streamItems queue stream items active]
          exact ReferenceWorkQueue.State.preparedStreamItems_preserves
            (fun current => current.TaskRejectionsSatisfy property) prior items []
            (fun _ item _ supported =>
              ((supported.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
  | taskFailure | groupFailure | streamSuccess | streamFailure => exact prior

/-- The actual delayed view retains only rejections supported by the same earlier inputs. -/
theorem registrationSnapshot_taskRejections {queue : ReferenceWorkQueue.State} {property}
    (prior : queue.TaskRejectionsSatisfy property) (event : GraphEvent)
    (projection : SnapshotProjection queue event)
    : (registrationSnapshot queue event).TaskRejectionsSatisfy property := by
  intro node member
  exact eagerRegistrationSnapshot_taskRejections prior event node (projection.nodes member)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
