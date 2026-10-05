import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedProgressEvents
import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingNoticeCoverage

/-! Executable event choices preserve the reporting-aware constructive notice frontier.
These witnesses choose covering carriers without restricting public admission.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Failure settlement preserves retained group notices
-----------------------------------------------------------------------------------------

/-- A ready failure extends reporting-aware coverage with an actual failure completion.
Witness: the ordinary licensed failure step; newly recorded contributors were already
eligible before settlement, while all other retained notices transport backwards.
-/
theorem reporting_failure
    {ancestry bound roles work groups streams events matching failures occurrence owners
      producer payload}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (known : TaskAt work occurrence owners producer payload)
    (ready : CanPublish work matching events failures occurrence producer)
    (fails : payload.failure.isSome = true)
    (opened : ∃ ref ∈ owners, Open ((groups ++ streams).map DeliveryNode.ref) events ref)
    : ∃ event cuts,
        Explains work groups streams (events ++ [event]) matching cuts
        ∧ ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            matching (events ++ [event]) cuts := by
  obtain ⟨node, count, event, contributes, control, _, extended⟩ :=
    explained.failure_step known fails (ready.reachable explained known) opened ready.2.1
  have included : failures ⊆ failures ++ [(events.length, occurrence)] :=
    List.subset_append_left _ _
  have failed : NodeFailed work matching (events ++ [event])
      (failures ++ [(events.length, occurrence)]) node.ref :=
    .task known contributes (by simp [failedBefore, List.filter_append])
  have noNotices : eventPending event = [] := by
    rcases control with rfl | rfl <;> rfl
  have completion : eventCompleted event = [node.ref] := by
    rcases control with rfl | rfl <;> rfl
  have failureTransport : ∀ ref,
      NodeFailed work matching events failures ref →
      NodeFailed work matching (events ++ [event])
        (failures ++ [(events.length, occurrence)]) ref :=
    fun _ failure => (failure.mono included).append _
  have notices : (announcedRefs ((groups ++ streams).map DeliveryNode.ref) events).Subset
      (announcedRefs ((groups ++ streams).map DeliveryNode.ref) (events ++ [event])) := by
    intro ref member
    simpa [announcedRefs, pendingRefs, noNotices] using member
  have completions : ∀ ref,
      roles ref = false →
      ¬NodeFailed work matching (events ++ [event])
        (failures ++ [(events.length, occurrence)]) ref →
      ref ∈ completedRefs (events ++ [event]) → ref ∈ completedRefs events := by
    intro ref _ healthy completed
    simp only [completedRefs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, completion, List.mem_append, List.mem_singleton] at completed
    rcases completed with earlier | rfl
    · exact earlier
    · exact False.elim (healthy failed)
  have publications : ∀ task,
      Published matching (events ++ [event]) task → Published matching events task := by
    intro task published
    rcases published_append_singleton_iff.mp published with earlier | ⟨value, _⟩
    · exact earlier
    · rcases control with rfl | rfl <;> cases value
  have healthyCovered := supported_coverage_control valid coherent roleCoherent explained
    covered.1 extended failureTransport notices completions publications (by
      intro ref accounted other otherOwners projected member
      exact ((accounted other otherOwners projected member).more_failures included).append
        [event])
  refine ⟨event, _, extended, ?_⟩
  apply group_notices_covered_settlement valid coherent roleCoherent covered
    healthyCovered extended explained known ready failureTransport notices completions
    publications
  intro ref recorded
  obtain ⟨task, otherOwners, settled, ⟨birth, result, taskKnown⟩, member⟩ := recorded
  have oldFailures := explained.2.1.failedBefore_eq (by simp : events.length ≤
    (events ++ [event]).length)
  have oldAtBoundary := explained.2.1.failedBefore_eq (Nat.le_refl events.length)
  simp only [failedBefore, List.filter_append, List.map_append, List.mem_append] at settled
  rcases settled with earlier | current
  · exact Or.inl ⟨task, otherOwners, by
      rw [oldAtBoundary]
      change task ∈ failedBefore failures (events ++ [event]).length at earlier
      rwa [oldFailures] at earlier, ⟨birth, result, taskKnown⟩, member⟩
  · have same : task = occurrence := by simpa [failedBefore] using current
    subst task
    exact Or.inr ((TaskAt.unique taskKnown known).1 ▸ member)

-----------------------------------------------------------------------------------------
-- A stream-only closure leaves the reporting frontier unchanged
-----------------------------------------------------------------------------------------

/-- A healthy stream completion preserves reporting-aware notice coverage.
Witness: supported stream closure plus backward transport of unchanged publications and
failure evidence. The stream role cannot newly satisfy a defer dependency by closure.
-/
theorem reporting_complete_stream
    {ancestry bound roles work groups streams events matching failures node dependencies
      producer}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (known : NodeAt work node .stream dependencies producer)
    (opened : Open ((groups ++ streams).map DeliveryNode.ref) events node.ref)
    (healthy : ¬NodeFailed work matching events failures node.ref)
    (accounted : NodeAccounted work matching events failures node.ref)
    : Explains work groups streams (events ++ [.streamSuccess node]) matching failures
      ∧ ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching (events ++ [.streamSuccess node]) failures := by
  obtain ⟨extended, retained⟩ := supported_complete_stream valid coherent roleCoherent
    explained covered.1 known opened healthy accounted
  refine ⟨extended, ?_⟩
  apply group_notices_covered_noncarrier valid coherent roleCoherent covered retained
    extended
    (fun _ failure => failure.append _)
    (by
      intro ref member
      simpa [announcedRefs, pendingRefs, eventPending] using member)
    (by
      intro ref role _ completed
      simp only [completedRefs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, eventCompleted, List.mem_append, List.mem_singleton] at completed
      rcases completed with earlier | rfl
      · exact earlier
      · have streamRole : roles node.ref = true := node_ref_role roleCoherent known
        rw [role] at streamRole
        cases streamRole)
    ?_ ?_ ?_
  · intro occurrence owners birth payload task published
    have earlier : Published matching events occurrence := by
      rcases published_append_singleton_iff.mp published with earlier | ⟨value, _⟩
      · exact earlier
      · cases value
    exact explained.published_producer task earlier
  · intro group deps birth _ notice source generated
    rcases published_append_singleton_iff.mp (notice.2.2.1 source generated)
      with earlier | ⟨value, _⟩
    · exact earlier
    · cases value
  · intro ref recorded
    obtain ⟨task, owners, settled, descriptor, member⟩ := recorded
    refine ⟨task, owners, ?_, descriptor, member⟩
    rw [explained.2.1.failedBefore_eq (Nat.le_refl events.length)]
    rwa [explained.2.1.failedBefore_eq (by simp)] at settled

-----------------------------------------------------------------------------------------
-- Every ready announced task preserves the reporting frontier
-----------------------------------------------------------------------------------------

/-- A ready task with an announced healthy owner has a reporting-aware extension.
Witness: object publication preserves retained co-owners, stream publication carries a
covering frontier, and failure settlement preserves both healthy and failed group notices.
This is a constructive choice of next event, not a law on every admitted extension.
-/
theorem extend_ready_reporting
    {ancestry refBound roles paths pathBound work groups streams events matching failures
      occurrence owners producer payload}
    (valid : Valid ancestry refBound) (refs : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (coherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (known : TaskAt work occurrence owners producer payload)
    (ready : CanPublish work matching events failures occurrence producer)
    (announced
      : ∃ ref ∈ owners,
          ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events
          ∧ ¬NodeFailed work matching events failures ref)
    : ∃ event next cuts,
        Explains work groups streams (events ++ [event]) next cuts
        ∧ ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            next (events ++ [event]) cuts := by
  obtain ⟨ref, member, notified, healthy⟩ := announced
  have opened : Open ((groups ++ streams).map DeliveryNode.ref) events ref := by
    refine ⟨notified, ?_⟩
    intro completed
    rcases explained.completed_accounted completed with failed | accounted
    · exact healthy failed
    · rcases accounted occurrence owners ⟨producer, payload, known⟩ member
        with cancelled | published
      · exact ready.2.1 cancelled
      · exact ready.1 published
  have failing (fails : payload.failure.isSome = true) :
      ∃ event next cuts, Explains work groups streams (events ++ [event]) next cuts
        ∧ ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            next (events ++ [event]) cuts := by
    obtain ⟨event, cuts, extended, retained⟩ := reporting_failure valid refs roleCoherent
      explained covered known ready fails ⟨ref, member, opened⟩
    exact ⟨event, matching, cuts, extended, retained⟩
  cases payload with
  | object path result =>
      cases result with
      | error errors => exact failing rfl
      | ok value =>
          obtain ⟨data, errors⟩ := value
          have deferred : ∃ address, occurrence = .executionGroup address := by
            cases StructuralEquivalence.taskAt_of_current known with
            | executionGroup => exact ⟨_, rfl⟩
          obtain ⟨address, rfl⟩ := deferred
          obtain ⟨node, kind, dependencies, nodeProducer, descriptor, same⟩ :=
            known.owner_known member
          obtain ⟨owner, selected⟩ := owner_exists_of_available coherent known
            ⟨node, ⟨⟨kind, dependencies, nodeProducer, descriptor⟩, same ▸ member,
              same ▸ opened⟩, same ▸ healthy⟩
          have extended := explained.publish_object known ready selected
          let event := WorkQueueEvent.groupValues owner [{ path, data, errors }]
          have failureTransport : ∀ ref,
              NodeFailed work matching events failures ref →
              NodeFailed work (matchNext matching events.length (.executionGroup address))
                (events ++ [event]) failures ref := by
            intro ref failure
            have same := nodeFailed_matching_eq (work := work) (events := events)
              (failures := failures)
              (fun _ before => matchNext_before matching (.executionGroup address) before)
            exact (same ▸ failure).append [event]
          have unavailable : ∀ ref ∈ owners,
              ¬DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref)
                matching events failures ref :=
            fun _ contributes => ready_owner_dependency_unsatisfied explained known
              contributes ready
          have notices : (announcedRefs ((groups ++ streams).map DeliveryNode.ref) events).Subset
              (announcedRefs ((groups ++ streams).map DeliveryNode.ref) (events ++ [event])) := by
            intro ref member
            simpa [announcedRefs, pendingRefs, event, eventPending] using member
          have completions : (completedRefs (events ++ [event])).Subset
              (completedRefs events) := by
            intro ref member
            simpa [completedRefs, event, eventCompleted] using member
          have publications : ∀ task,
              Published (matchNext matching events.length (.executionGroup address))
                (events ++ [event]) task →
              Published matching events task ∨ task = .executionGroup address := by
            intro task published
            rcases published_append_singleton_iff.mp published with earlier | ⟨_, same⟩
            · have same := published_matching_eq (events := events)
                (fun _ before => matchNext_before matching (.executionGroup address) before)
              exact Or.inl (same ▸ earlier)
            · exact Or.inr (by simpa only [matchNext, ↓reduceIte] using same.symm)
          have producers : ∀ occurrence owners producer payload,
              TaskAt work occurrence owners producer payload → Published matching events occurrence
              → ∀ source, producer = some source → Published matching events source :=
            fun _ _ _ _ task published =>
            explained.published_producer task published
          have retained := supported_coverage_publication valid refs roleCoherent continuous
            ordered covered.1 extended failureTransport known ready unavailable producers
            notices completions publications (by
              intro ref accounted occurrence owners projected member
              exact (accounted occurrence owners projected member).matchNext_append
                (.executionGroup address) event)
          refine ⟨event, _, failures, extended, ?_⟩
          apply group_notices_covered_publication valid refs roleCoherent continuous
            ordered covered retained extended failureTransport known ready unavailable
            producers notices completions publications
          intro ref recorded
          obtain ⟨task, owners, settled, descriptor, member⟩ := recorded
          refine ⟨task, owners, ?_, descriptor, member⟩
          rw [explained.2.1.failedBefore_eq (Nat.le_refl events.length)]
          rwa [explained.2.1.failedBefore_eq (by simp)] at settled
  | item node result =>
      cases result with
      | error errors => exact failing rfl
      | ok value =>
          obtain ⟨item, errors⟩ := value
          have ownerRef : ref = node.ref := by
            cases StructuralEquivalence.taskAt_of_current known with
            | item located selected => exact List.mem_singleton.mp member
          have selected := stream_owner_of_open coherent known (ownerRef ▸ opened)
            (ownerRef ▸ healthy)
          obtain ⟨newGroups, newStreams, extended, notices⟩ :=
            explained.publish_item_noticesCovered known ready selected
          exact ⟨_, _, _, extended, reportingNoticesCovered_of_noticesCovered notices⟩

end GraphQL.IncrementalDelivery.Correctness
