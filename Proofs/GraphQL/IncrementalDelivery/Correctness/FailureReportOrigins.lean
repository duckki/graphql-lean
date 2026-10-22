import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata
import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SingletonOwners
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SettlementAvailability

/-! Concrete completion timing supplies reporting without assuming Terminal. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics

/-- Coherent owner metadata and a post-settlement closure report the failed attachment.
Witness: the closing owner counts the recorded positive failure; its generated path is
a prefix of the task attachment. The owner may have been announced after settlement.
This theorem assumes neither terminal reporting nor openness at the settlement cut.
-/
theorem Explains.completion_reports_task
    {paths bound work groups streams events matching failures cut occurrence owners
      producer payload ref index event}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (recorded : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence owners producer payload)
    (positive : 0 < payload.failure.getD 0)
    (contributes : ref ∈ owners) (selected : events[index]? = some event)
    (afterSettlement : cut ≤ index) (closed : ref ∈ eventCompleted event)
    : FailureReportedFor events payload.path := by
  have allowed := explained.2.2 index event selected
  have recordedBefore : occurrence ∈ failedBefore failures (events.take index).length := by
    have bound := (List.getElem?_eq_some_iff.mp selected).1
    simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
      using mem_failedBefore recorded afterSettlement
  obtain ⟨node, errors, same, failure, count⟩ :=
    allowed.failure_completion recordedBefore known contributes closed
  have reports : event ∈ events := List.mem_of_getElem? selected
  have nonzero : 0 < errors := by omega
  rcases failure with rfl | rfl
  all_goals
    obtain ⟨dependencies, birth, descriptor⟩ := allowed.1
    have below := workAt_owner_prefix coherent known descriptor (same.symm ▸ contributes)
    have attachment : payloadPath payload = payload.path := by cases payload <;> rfl
    rw [attachment] at below
    obtain ⟨suffix, equal⟩ := below
    exact ⟨node, errors, nonzero, ⟨suffix, equal.symm⟩,
      by first | exact Or.inl reports | exact Or.inr reports⟩

/-- A contributor may be announced after settlement and still report the failed attachment.
Witness: its actual closure occurs after the cut and counts the positive failure; coherent
owner metadata transfers the completion scope to the attachment. No owner need be open at
settlement, and no terminal reporting or previously supplied report is assumed.
-/
theorem Explains.recorded_task_reported_of_eventual_notice
    {paths bound work groups streams events matching failures cut occurrence owners
      producer payload}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (recorded : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence owners producer payload)
    (positive : 0 < payload.failure.getD 0)
    (eventualOwner
      : ∃ ref ∈ owners,
          ref ∉ completedRefs (events.take cut)
          ∧ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    : FailureReportedFor events payload.path := by
  obtain ⟨index, node, errors, afterSettlement, contributes, selected, _⟩ :=
    explained.failure_reported_of_eventual_notice closedRefs recorded known eventualOwner
  rcases selected with group | stream
  · exact Explains.completion_reports_task coherent explained recorded known positive
      contributes group afterSettlement (by simp [eventCompleted])
  · exact Explains.completion_reports_task coherent explained recorded known positive
      contributes stream afterSettlement (by simp [eventCompleted])

/-- An eventually announced contributor reports its full node scope, not merely the failed
shared task's attachment. Witness: its post-settlement completion counts the positive
failure, and same-ref path coherence identifies the actual notice scope. This is needed
when a broader co-owner also loses private work outside the shared task's attachment.
-/
theorem Explains.recorded_owner_reported_of_eventual_notice
    {paths bound work groups streams events matching failures cut occurrence owners
      producer payload node kind dependencies birth}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (recorded : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence owners producer payload)
    (_positive : 0 < payload.failure.getD 0)
    (descriptor : NodeAt work node kind dependencies birth)
    (contributes : node.ref ∈ owners)
    (unfinished : node.ref ∉ completedRefs (events.take cut))
    (announced
      : node.ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    : FailureReportedFor events node.path := by
  obtain ⟨index, reporter, errors, _, same, selected, counted⟩ :=
    explained.contributor_failure_reported_of_eventual_notice closedRefs recorded known
      contributes unfinished announced
  have nonzero : 0 < errors := by omega
  rcases selected with group | stream
  all_goals
    have allowed := explained.2.2 index _ (by assumption)
    obtain ⟨parents, source, reportedNode⟩ := allowed.1
    have scope := workAt_same_path coherent reportedNode descriptor same
    refine ⟨reporter, errors, nonzero, ?_, ?_⟩
    · exact ⟨[], by simp [scope]⟩
    · first
      | exact Or.inl (List.mem_of_getElem? group)
      | exact Or.inr (List.mem_of_getElem? stream)

/-- Covering notices for the contributors that survive a shared settlement supplies a
report once announced refs close. Witness: settlement licensing leaves a healthy unfinished
owner before this failure, even if all previously announced co-owners already closed.
The notice premise concerns visibility only, not response coverage or terminal reporting.
-/
theorem Explains.recorded_task_reported_of_surviving_notices
    {paths bound work groups streams events matching before cut occurrence after owners
      producer payload}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (explained
      : Explains work groups streams events matching
          (before ++ (cut, occurrence) :: after))
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (known : TaskAt work occurrence owners producer payload)
    (positive : 0 < payload.failure.getD 0)
    (notified
      : ∀ ref ∈ owners,
          ¬NodeFailed work matching (events.take cut) before ref
          → ref ∉ completedRefs (events.take cut)
          → ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events)
    : FailureReportedFor events payload.path := by
  obtain ⟨ref, member, healthy, unfinished⟩ := explained.failure_outstanding_owner known
  exact Explains.recorded_task_reported_of_eventual_notice coherent explained closedRefs
    (by simp) known positive
    ⟨ref, member, unfinished, notified ref member healthy unfinished⟩

/-- A recorded positive failure with a still-open contributor is reported once announced
refs close. Witness: the independent closure bound locates an actual error completion;
generated owner metadata makes its scope cover the failed task's attachment.
This is a sufficient timing case, not a restriction on admitted failure settlements.
-/
theorem Explains.recorded_task_reported
    {paths bound work groups streams events matching failures cut occurrence owners
      producer payload}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (recorded : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence owners producer payload)
    (positive : 0 < payload.failure.getD 0)
    (openOwner
      : ∃ ref ∈ owners,
          Open ((groups ++ streams).map DeliveryNode.ref) (events.take cut) ref)
    : FailureReportedFor events payload.path := by
  obtain ⟨index, node, errors, afterSettlement, contributes, selected, _⟩ :=
    explained.failure_reported_of_closures closedRefs recorded known openOwner
  rcases selected with group | stream
  · exact Explains.completion_reports_task coherent explained recorded known positive contributes group
      afterSettlement (by simp [eventCompleted])
  · exact Explains.completion_reports_task coherent explained recorded known positive contributes stream
      afterSettlement (by simp [eventCompleted])

/-- A positive singleton-owned failure is reported once announced IDs close.
Witness: settlement licensing itself keeps the sole owner open; its actual later
completion counts the failure and coherent owner paths cover the task attachment.
No terminal law, reporting assumption, or supplied open-owner premise is used.
-/
theorem Explains.singleton_recorded_task_reported
    {paths bound work groups streams events matching failures cut occurrence ref producer
      payload}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (closedRefs
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (recorded : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence [ref] producer payload)
    (positive : 0 < payload.failure.getD 0)
    : FailureReportedFor events payload.path :=
  Explains.recorded_task_reported coherent explained closedRefs recorded known positive
    ⟨ref, by simp, explained.singleton_failure_open recorded known⟩

end GraphQL.IncrementalDelivery.Correctness
