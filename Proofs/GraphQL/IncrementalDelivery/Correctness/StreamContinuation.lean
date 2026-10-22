import Proofs.GraphQL.IncrementalDelivery.Correctness.ReleasedStreamAccounting
import Proofs.GraphQL.IncrementalDelivery.Correctness.AnnouncedGroupCancellationReporting
import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamNoticeSupport

/-! Complete released-stream continuations additionally require observable reporting. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics
open Semantics.Ancestry Semantics.GeneralScheduling

/-- A released-stream prefix with every defer group initially announced admits a complete continuation.
Witness: maximize accounting-preserving stream extensions, close announced refs, then derive
actual reports from the announced group scopes and accepted settlements. Generated path
locality carries these reports to unannounced descendants. Positive failed payloads are
required; raw zero-count failures cannot report missing attachments.
-/
theorem finish_released_streams
    {ancestry refBound roles base paths bound work groups streams events matching
      failures}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (valid : Valid ancestry refBound) (refs : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (allocated : (streamAllocationRefs work).Nodup)
    (groupsAnnounced
      : ∀ node dependencies birth,
          NodeAt work node .group dependencies birth
          → node.ref ∈ groups.map DeliveryNode.ref)
    (explained : Explains work groups streams events matching failures)
    (deferred : DeferredTasksAccounted work matching events failures)
    (closed : StreamDependenciesCompleted work events)
    (notified
      : StreamsNotified work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    : ∃ tail next cuts,
        Explains work groups streams (events ++ tail) next cuts
        ∧ Terminal work ((groups ++ streams).map DeliveryNode.ref) next (events ++ tail)
            cuts := by
  obtain ⟨tail, next, cuts, admitted, accounted⟩ :=
    account_released_streams coherent positive explained deferred closed notified
  have support := Explains.streamNoticesSupported_of_initial_groups refs roleCoherent
    admitted groupsAnnounced
  have causes := Explains.openFailureCauses_of_supported_streams valid refs roleCoherent
    allocated positive admitted support
  obtain ⟨closures, _, _, finished, allClosed⟩ := admitted.close_open_refs causes accounted
    (announcedRefs ((groups ++ streams).map DeliveryNode.ref) (events ++ tail))
    (fun _ opened => opened.1)
  have visible : ∀ node dependencies birth,
      NodeAt work node .group dependencies birth
      → node.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref)
          (events ++ tail ++ closures) := by
    intro node dependencies birth descriptor
    apply List.mem_append_left
    simpa only [List.map_append]
      using List.mem_append_left (streams.map DeliveryNode.ref)
        (groupsAnnounced _ _ _ descriptor)
  have finalAccounted occurrence owners producer payload
      (known : TaskAt work occurrence owners producer payload)
      : TaskAccounted work next (events ++ tail ++ closures) cuts occurrence :=
    (accounted occurrence owners producer payload known).append closures
  have reports occurrence owners producer payload
      (known : TaskAt work occurrence owners producer payload)
      (unpublished : ¬Published next (events ++ tail ++ closures) occurrence)
      : FailureReportedFor (events ++ tail ++ closures) payload.path :=
    Explains.cancelled_reported_of_announced_groups valid refs roleCoherent coherent under
      positive finished visible allClosed
      ((finalAccounted _ _ _ _ known).resolve_right unpublished) known
  obtain ⟨last, _, _, finalized, terminal⟩ := finished.finish_accounted
    (fun ref opened _ => False.elim (opened.2 (allClosed ref opened.1))) finalAccounted reports
  exact ⟨
    tail ++ closures ++ last,
    next,
    cuts,
    by simpa only [List.append_assoc] using finalized,
    by simpa only [List.append_assoc] using terminal
  ⟩

/-- The continuation retains every previously supplied work batch and its grouping.
Witness: append singleton batches for the constructed suffix, then one termination batch.
-/
theorem released_streams_run_extension
    {ancestry refBound roles base paths bound work groups streams events matching failures
      batches}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (valid : Valid ancestry refBound) (refs : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (under : ExecutionPaths.WorkUnder base work)
    (positive : ExecutionErrors.WorkPositive work)
    (allocated : (streamAllocationRefs work).Nodup)
    (groupsAnnounced
      : ∀ node dependencies birth,
          NodeAt work node .group dependencies birth
          → node.ref ∈ groups.map DeliveryNode.ref)
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
  obtain ⟨tail, next, cuts, admitted, terminal⟩ :=
    finish_released_streams coherent valid refs roleCoherent under positive allocated groupsAnnounced
      explained deferred closed notified
  exact ⟨tail, events ++ tail, next, cuts, admitted, terminal,
    (batched.append (WorkBatching.singletons tail)).append
      (WorkBatching.singletons [.workQueueTermination])⟩

end GraphQL.IncrementalDelivery.Correctness
