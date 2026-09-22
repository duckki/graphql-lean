import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedNoticeExtension

/-! Actual event extensions preserving the proof-only mixed notice witness.
Covering carriers are existential choices, not extra scheduler requirements.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Control observations preserve supported notice coverage
-----------------------------------------------------------------------------------------

/-- A healthy stream can complete without uncovering supported notices.
Witness: completion changes no publication and its stream role excludes every defer
dependency key. Existing accounted tasks remain accounted for in the extended history.
-/
theorem supported_complete_stream
    {ancestry bound roles work groups streams events matching failures node dependencies
      producer}
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
          matching events (failures.map Prod.snd))
    (known : NodeAt work node .stream dependencies producer)
    (opened : Open ((groups ++ streams).map DeliveryNode.key) events node.key)
    (healthy : ¬NodeFailed work (failedBefore failures events.length) node.key)
    (accounted
      : NodeAccounted work matching events (failedBefore failures events.length) node.key)
    : Explains work groups streams (events ++ [.streamSuccess node]) matching failures
      ∧ SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
          matching (events ++ [.streamSuccess node]) (failures.map Prod.snd) := by
  refine ⟨explained.append_event
    ⟨⟨dependencies, producer, known⟩, opened, healthy, accounted⟩, ?_⟩
  apply supported_coverage_control valid coherent roleCoherent explained covered
    (List.Subset.refl _)
  · intro key member
    simpa [announcedKeys, pendingKeys, eventPending] using member
  · intro key role _ completed
    simp only [completedKeys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, eventCompleted, List.mem_append, List.mem_singleton] at completed
    rcases completed with earlier | rfl
    · exact earlier
    · have streamRole : roles node.key = true := node_key_role roleCoherent known
      rw [role] at streamRole
      cases streamRole
  · intro task published
    rcases published_append_singleton_iff.mp published with earlier | ⟨value, _⟩
    · exact earlier
    · cases value
  · intro key accounted occurrence owners projected member
    exact (accounted occurrence owners projected member).append _

/-- A ready failure extends a supported history with an actual counted completion.
Witness: the bounded failure-cut construction; only its now-failed owner completes, so
the generic nonpublishing preservation theorem applies even to mixed cancellation.
-/
theorem supported_failure
    {ancestry bound roles work groups streams events matching failures occurrence owners
      producer payload}
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
          matching events (failures.map Prod.snd))
    (known : TaskAt work occurrence owners producer payload)
    (ready
      : CanPublish work matching events (failedBefore failures events.length)
          occurrence producer)
    (fails : payload.failure.isSome = true)
    (opened : ∃ key ∈ owners, Open ((groups ++ streams).map DeliveryNode.key) events key)
    : ∃ event cuts,
        Explains work groups streams (events ++ [event]) matching cuts
        ∧ SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
            matching (events ++ [event]) (cuts.map Prod.snd) := by
  have stable := explained.2.1.failedBefore_eq (Nat.le_refl _)
  obtain ⟨node, count, event, contributes, control, _, extended⟩ :=
    explained.failure_step known fails (ready.reachable explained known) opened
      (by simpa only [stable] using ready.2.1)
  have included : failures.map Prod.snd ⊆
      (failures ++ [(events.length, occurrence)]).map Prod.snd := by
    simp only [List.map_append]
    exact List.subset_append_left _ _
  have failed : NodeFailed work
      ((failures ++ [(events.length, occurrence)]).map Prod.snd) node.key :=
    .task known contributes (by simp)
  have noNotices : eventPending event = [] := by
    rcases control with rfl | rfl <;> rfl
  have completion : eventCompleted event = [node.key] := by
    rcases control with rfl | rfl <;> rfl
  refine ⟨event, _, extended, ?_⟩
  apply supported_coverage_control valid coherent roleCoherent explained covered included
  · intro key member
    simpa [announcedKeys, pendingKeys, noNotices] using member
  · intro key _ healthy completed
    simp only [completedKeys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, completion, List.mem_append, List.mem_singleton] at completed
    rcases completed with earlier | rfl
    · exact earlier
    · exact False.elim (healthy failed)
  · intro task published
    rcases published_append_singleton_iff.mp published with earlier | ⟨value, _⟩
    · exact earlier
    · rcases control with rfl | rfl <;> cases value
  · intro key accounted occurrence owners projected member
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
    {ancestry keyBound roles paths pathBound work groups streams events matching failures
      occurrence owners producer payload}
    (valid : Valid ancestry keyBound) (keys : MixedKeys.WorkAt ancestry 0 keyBound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (coherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
          matching events (failures.map Prod.snd))
    (known : TaskAt work occurrence owners producer payload)
    (ready
      : CanPublish work matching events (failedBefore failures events.length)
          occurrence producer)
    (announced
      : ∃ key ∈ owners,
          key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events
          ∧ ¬NodeFailed work (failedBefore failures events.length) key)
    : ∃ event next cuts,
        Explains work groups streams (events ++ [event]) next cuts
        ∧ SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
            next (events ++ [event]) (cuts.map Prod.snd) := by
  obtain ⟨key, member, notified, healthy⟩ := announced
  have opened : Open ((groups ++ streams).map DeliveryNode.key) events key := by
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
        ∧ SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
            next (events ++ [event]) (cuts.map Prod.snd) := by
    obtain ⟨event, cuts, extended, retained⟩ := supported_failure valid keys roleCoherent
      explained covered known ready fails ⟨key, member, opened⟩
    exact ⟨event, matching, cuts, extended, retained⟩
  have stable := explained.2.1.failedBefore_eq (Nat.le_refl _)
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
            ⟨node, ⟨kind, dependencies, nodeProducer, descriptor⟩, same ▸ member,
              same ▸ opened,
              same ▸ healthy⟩
          have extended := explained.publish_object known ready selected
          let event := WorkEvent.groupValues owner [{ path, data, errors }]
          refine ⟨event, _, failures, extended, ?_⟩
          apply supported_coverage_publication valid keys roleCoherent continuous ordered
            covered known (by simpa only [stable] using ready)
          · intro key contributes dependency
            exact ready_owner_dependency_unsatisfied explained known contributes ready
              (by simpa only [stable] using dependency)
          · exact fun _ _ _ _ task published => explained.published_producer task published
          · intro key member
            simpa [announcedKeys, pendingKeys, event, eventPending] using member
          · intro key member
            simpa [completedKeys, event, eventCompleted] using member
          · intro task published
            rcases published_append_singleton_iff.mp published with earlier | ⟨_, same⟩
            · exact Or.inl ((published_matching_eq
                (fun _ before => matchNext_before matching (.executionGroup address) before)) ▸ earlier)
            · exact Or.inr (by simpa only [matchNext, ↓reduceIte] using same.symm)
          · intro key accounted occurrence owners projected member
            exact (accounted occurrence owners projected member).matchNext_append
              (.executionGroup address) event
  | item node result =>
      cases result with
      | error errors => exact failing rfl
      | ok value =>
          obtain ⟨item, errors⟩ := value
          have ownerKey : key = node.key := by
            cases StructuralEquivalence.taskAt_of_current known with
            | item located selected => exact List.mem_singleton.mp member
          have selected := stream_owner_of_open coherent known (ownerKey ▸ opened)
            (ownerKey ▸ healthy)
          obtain ⟨newGroups, newStreams, extended, notices⟩ :=
            explained.publish_item_noticesCovered known ready selected
          exact ⟨_, _, _, extended, supportedNoticesCovered_of_noticesCovered notices⟩

end GraphQL.IncrementalDelivery.Correctness
