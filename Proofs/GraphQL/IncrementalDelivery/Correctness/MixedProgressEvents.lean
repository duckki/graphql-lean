import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedNoticeExtension

/-! Actual event extensions preserving the proof-only mixed notice witness.
Covering carriers are existential choices, not extra scheduler requirements.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Control observations preserve supported notice coverage
-----------------------------------------------------------------------------------------

/-- A healthy stream can complete without uncovering supported notices.
Witness: completion changes no publication and its stream role excludes every defer
dependency ref. Existing accounted tasks remain accounted for in the extended history.
-/
theorem supported_complete_stream
    {ancestry bound roles work groups streams events matching failures node dependencies
      producer}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (known : NodeAt work node .stream dependencies producer)
    (opened : Open ((groups ++ streams).map DeliveryNode.ref) events node.ref)
    (healthy : ¬NodeFailed work matching events failures node.ref)
    (accounted : NodeAccounted work matching events failures node.ref)
    : Explains work groups streams (events ++ [.streamSuccess node]) matching failures
      ∧ SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching (events ++ [.streamSuccess node]) failures := by
  have extended : Explains work groups streams
      (events ++ [.streamSuccess node]) matching failures := by
    apply explained.append_event
    simp only [EventAllowed, explained.2.1.filter_eq_self (Nat.le_refl _)]
    exact ⟨⟨dependencies, producer, known⟩, opened, healthy, accounted⟩
  refine ⟨extended, ?_⟩
  apply supported_coverage_control valid coherent roleCoherent explained covered extended
    (fun _ failure => failure.append _)
  · intro ref member
    simpa [announcedRefs, pendingRefs, eventPending] using member
  · intro ref role _ completed
    simp only [completedRefs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, eventCompleted, List.mem_append, List.mem_singleton] at completed
    rcases completed with earlier | rfl
    · exact earlier
    · have streamRole : roles node.ref = true := node_ref_role roleCoherent known
      rw [role] at streamRole
      cases streamRole
  · intro task published
    rcases published_append_singleton_iff.mp published with earlier | ⟨value, _⟩
    · exact earlier
    · cases value
  · intro ref accounted occurrence owners projected member
    exact (accounted occurrence owners projected member).append _

/-- A ready failure extends a supported history with an actual counted completion.
Witness: the bounded failure-cut construction; only its now-failed owner completes, so
the generic nonpublishing preservation theorem applies even to mixed cancellation.
-/
theorem supported_failure
    {ancestry bound roles work groups streams events matching failures occurrence owners
      producer payload}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (known : TaskAt work occurrence owners producer payload)
    (ready : CanPublish work matching events failures occurrence producer)
    (fails : payload.failure.isSome = true)
    (opened : ∃ ref ∈ owners, Open ((groups ++ streams).map DeliveryNode.ref) events ref)
    : ∃ event cuts,
        Explains work groups streams (events ++ [event]) matching cuts
        ∧ SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            matching (events ++ [event]) cuts := by
  obtain ⟨node, count, event, contributes, control, _, extended⟩ :=
    explained.failure_step known fails (ready.reachable explained known) opened
      ready.2.1
  have included : failures ⊆ failures ++ [(events.length, occurrence)] :=
    List.subset_append_left _ _
  have failed : NodeFailed work matching (events ++ [event])
      (failures ++ [(events.length, occurrence)]) node.ref :=
    .task known contributes (by simp [failedBefore, List.filter_append])
  have noNotices : eventPending event = [] := by
    rcases control with rfl | rfl <;> rfl
  have completion : eventCompleted event = [node.ref] := by
    rcases control with rfl | rfl <;> rfl
  refine ⟨event, _, extended, ?_⟩
  apply supported_coverage_control valid coherent roleCoherent explained covered extended
    (fun _ failure => (failure.mono included).append _)
  · intro ref member
    simpa [announcedRefs, pendingRefs, noNotices] using member
  · intro ref _ healthy completed
    simp only [completedRefs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, completion, List.mem_append, List.mem_singleton] at completed
    rcases completed with earlier | rfl
    · exact earlier
    · exact False.elim (healthy failed)
  · intro task published
    rcases published_append_singleton_iff.mp published with earlier | ⟨value, _⟩
    · exact earlier
    · rcases control with rfl | rfl <;> cases value
  · intro ref accounted occurrence owners projected member
    exact ((accounted occurrence owners projected member).more_failures included).append [event]

-----------------------------------------------------------------------------------------
-- Every ready announced task has a coverage-preserving extension
-----------------------------------------------------------------------------------------

/-- A ready task with an announced healthy owner extends a supported mixed history.
Witness: a ready object publication, a stream publication carrying a covering frontier,
or the actual failure-cut extension. Neither payload success nor singleton ownership is
assumed; generated paths supply a permitted owner when several groups overlap.
-/
theorem extend_ready_supported
    {ancestry refBound roles paths pathBound work groups streams events matching failures
      occurrence owners producer payload}
    (valid : Valid ancestry refBound) (refs : MixedRefs.WorkAt ancestry 0 refBound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (coherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (known : TaskAt work occurrence owners producer payload)
    (ready : CanPublish work matching events failures occurrence producer)
    (announced
      : ∃ ref ∈ owners,
          ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events
          ∧ ¬NodeFailed work matching events failures ref)
    : ∃ event next cuts,
        Explains work groups streams (events ++ [event]) next cuts
        ∧ SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
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
        ∧ SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            next (events ++ [event]) cuts := by
    obtain ⟨event, cuts, extended, retained⟩ := supported_failure valid refs roleCoherent
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
              same ▸ opened⟩,
              same ▸ healthy⟩
          have extended := explained.publish_object known ready selected
          let event := WorkQueueEvent.groupValues owner [{ path, data, errors }]
          refine ⟨event, _, failures, extended, ?_⟩
          have failureTransport : ∀ ref,
              NodeFailed work matching events failures ref →
                NodeFailed work (matchNext matching events.length (.executionGroup address))
                  (events ++ [event]) failures ref := by
            intro ref failure
            have same := nodeFailed_matching_eq (work := work) (events := events)
              (failures := failures)
              (fun _ before => matchNext_before matching (.executionGroup address) before)
            exact (same ▸ failure).append [event]
          apply supported_coverage_publication valid refs roleCoherent continuous ordered
            covered extended failureTransport known ready
          · intro ref contributes dependency
            exact ready_owner_dependency_unsatisfied explained known contributes ready
              dependency
          · exact fun _ _ _ _ task published => explained.published_producer task published
          · intro ref member
            simpa [announcedRefs, pendingRefs, event, eventPending] using member
          · intro ref member
            simpa [completedRefs, event, eventCompleted] using member
          · intro task published
            rcases published_append_singleton_iff.mp published with earlier | ⟨_, same⟩
            · have same := published_matching_eq (events := events)
                (fun _ before => matchNext_before matching (.executionGroup address) before)
              exact Or.inl (same ▸ earlier)
            · exact Or.inr (by simpa only [matchNext, ↓reduceIte] using same.symm)
          · intro ref accounted occurrence owners projected member
            exact (accounted occurrence owners projected member).matchNext_append
              (.executionGroup address) event
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
          exact ⟨_, _, _, extended, supportedNoticesCovered_of_noticesCovered notices⟩

end GraphQL.IncrementalDelivery.Correctness
