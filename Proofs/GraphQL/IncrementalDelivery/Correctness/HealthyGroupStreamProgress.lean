import Proofs.GraphQL.IncrementalDelivery.Correctness.ReleasedStreamAccounting
import Proofs.GraphQL.IncrementalDelivery.Correctness.HealthyGroupStreamReporting

/-! Complete released-stream continuations whose deferred groups cannot fail. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

/-- A released-stream prefix has a complete continuation when pure work keeps its deferred
groups healthy. Witness: extend to task accounting, close all announced refs, then derive
actual cancellation reports from singleton stream failures and producer-local paths.
Original batches are retained, and neither terminal reporting nor fairness is assumed.
-/
theorem released_streams_run_extension_of_healthy_groups
    {base paths bound work groups streams events matching failures batches}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (healthyGroups
      : ∀ outputs next cuts,
          Explains work groups streams outputs next cuts
          → ∀ node dependencies birth,
              NodeAt work node .group dependencies birth
              → ¬NodeFailed work next outputs cuts node.ref)
    (explained : Explains work groups streams events matching failures)
    (deferred : DeferredTasksAccounted work matching events failures)
    (closed : StreamDependenciesCompleted work events)
    (notified
      : StreamsNotified work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (batched : WorkBatching events batches)
    : ∃ tail : List WorkQueueEvent,
        AdmissibleRun work
          ⟨
            groups,
            streams,
            batches ++ tail.map (fun event => [event]) ++ [[.workQueueTermination]]
          ⟩ := by
  obtain ⟨tail, next, cuts, admitted, accounted⟩ :=
    account_released_streams coherent explained deferred closed notified
  obtain ⟨closures, _, _, finished, allClosed⟩ := admitted.close_open_refs accounted
    (announcedRefs ((groups ++ streams).map DeliveryNode.ref) (events ++ tail))
    (fun _ opened => opened.1)
  have reports occurrence owners producer payload
      (known : TaskAt work occurrence owners producer payload)
      (unpublished : ¬Published next ((events ++ tail) ++ closures) occurrence)
      : FailureReportedFor ((events ++ tail) ++ closures) payload.path := by
    exact Explains.cancelled_reported_of_healthy_groups coherent under positive finished
      (healthyGroups _ _ _ finished) allClosed
      (((accounted _ _ _ _ known).append closures).resolve_right unpublished) known
  have finalBatching := (batched.append (WorkBatching.singletons tail)).append
    (WorkBatching.singletons closures)
  obtain ⟨last, run, _, _⟩ := finalBatching.finish_accounted finished
    (fun occurrence owners producer payload known =>
      (accounted occurrence owners producer payload known).append closures) reports
  refine ⟨tail ++ closures ++ last, ?_⟩
  simpa only [List.map_append, List.append_assoc] using run

end GraphQL.IncrementalDelivery.Correctness
