import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationMatching
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublisherRegistry

/-! Actual remapped object owners satisfy the scheduler rule on the shared task matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Notice state survives atomic expansion and the selected value's local block prefix
-----------------------------------------------------------------------------------------

/-- Expanding one well-shaped event preserves its pending and completed key lists exactly.
Witness: object atoms have no notices; stream notices stay on the final nonempty item;
all controls remain unchanged. This is output projection, not an admission assumption.
-/
theorem publicationAtoms_noticeState (event : Execution.WorkQueueEvent)
    (nonempty : NonemptyValues event)
    : pendingKeys (publicationAtoms event) = eventPending event
      ∧ completedKeys (publicationAtoms event) = eventCompleted event := by
  cases event with
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => exact False.elim (nonempty rfl)
      | case2 =>
          simp [publicationAtoms, streamPublicationAtoms, pendingKeys, completedKeys]
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, pendingKeys, completedKeys,
            eventPending, eventCompleted]
            using ih (by simp [NonemptyValues])
  | groupValues =>
      simp [publicationAtoms, pendingKeys, completedKeys, List.flatMap_map,
        eventPending, eventCompleted]
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [publicationAtoms, pendingKeys, completedKeys]

/-- Atomic expansion preserves the full notice state of a well-shaped normalized prefix.
Witness: concatenate the exact per-event key projections in their original order.
-/
theorem publicationAtoms_list_noticeState (events : List Execution.WorkQueueEvent)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    : pendingKeys (events.flatMap publicationAtoms) = pendingKeys events
      ∧ completedKeys (events.flatMap publicationAtoms) = completedKeys events := by
  induction events with
  | nil => exact ⟨rfl, rfl⟩
  | cons event rest ih =>
      obtain ⟨notices, closures⟩ := publicationAtoms_noticeState event
        (nonempty event List.mem_cons_self)
      obtain ⟨laterNotices, laterClosures⟩ :=
        ih (fun next member => nonempty next (List.mem_cons_of_mem _ member))
      change (publicationAtoms event).flatMap eventPending = eventPending event at notices
      change (publicationAtoms event).flatMap eventCompleted = eventCompleted event at closures
      constructor
      · simpa only [List.flatMap_cons, pendingKeys, List.flatMap_append, notices]
          using congrArg (eventPending event ++ ·) laterNotices
      · simpa only [List.flatMap_cons, completedKeys, List.flatMap_append, closures]
          using congrArg (eventCompleted event ++ ·) laterClosures

namespace ConformancePlan

/-- Every contributing group has exact active/open agreement at an actual object atom.
Witness: group-key freshness establishes the real publisher registry at the recovered raw
prefix; atomic expansion and earlier values of the same block leave notice state unchanged.
-/
theorem Witness.groupPublication_contributorRegistry {work inputs index owner payload}
    {w : Witness} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (origin
      : GroupPublicationOrigin
          {
            active :=
              (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
          }
          ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload)
    : ∀ candidate ∈ origin.value.deliveryGroups,
        candidate.key
          ∈ (({
                active :=
                  (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
              }
              : IncrementalPublisher).normalizeBatch
              origin.before).1.active.map
              Execution.DeliveryNode.key
        ↔ Open (initialKeys work) (w.events.take index) candidate.key := by
  let publisher : IncrementalPublisher :=
    { active := (initialQueue work).initialGroups ++ (initialQueue work).initialStreams }
  have isPrefix : origin.before.IsPrefix
      ((initialQueue work).rawEventReplay inputs.flatten).2 :=
    ⟨_, origin.rawEq.symm⟩
  have shape := (initialQueue work).rawEventReplay_nonemptyValues inputs.flatten
    valid.nonemptyItems
  have normalizedShape := (publisher.normalizeBatch_nonemptyValues origin.before
    (fun event member => shape event (isPrefix.subset member))).2
  obtain ⟨pending, completed⟩ := publicationAtoms_list_noticeState _ normalizedShape
  obtain ⟨silentPending, silentCompleted⟩ := GroupPublicationOrigin.object_prefix_keys
    (publisher.normalizeBatch origin.before).1 origin.group origin.values origin.offset
  simp only [pendingKeys, completedKeys] at pending completed silentPending silentCompleted
  have same := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  have valuePrefix := origin.valuePrefix
  rw [← same] at valuePrefix
  intro candidate member
  obtain ⟨dependencies, producer, known⟩ :=
    Witness.groupPublication_contributorsLocated valid origin candidate member
  have registry := createWorkQueue_rawPrefix_groupRegistry generated valid known isPrefix
  dsimp only at registry
  rw [registry, valuePrefix]
  simp only [Open, announcedKeys, pendingKeys, completedKeys, List.flatMap_append]
  rw [pending, completed, silentPending, silentCompleted, List.append_nil, List.append_nil]
  rfl

/-- Every actual object atom selects an open longest-path contributor with healthy support.
Witness: derive the publisher registry on the same recovered raw prefix and apply its
max-selection theorem, keeping the exact task occurrence from the shared closure ledger.
-/
theorem GroupPublicationReleases.matched_owner {work inputs w}
    (releases : GroupPublicationReleases work inputs w)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w) {index owner values}
    (selected : w.events[index]? = some (.groupValues owner values))
    : ∃ owners producer value,
        TaskAt work (w.matching index) owners producer
          (.object value.path (.ok (value.data, value.errors)))
        ∧ values = [value]
        ∧ PublicationOwner work (initialKeys work) w.matching (w.events.take index)
            w.failures owners owner := by
  obtain ⟨origin, ⟨producer, known⟩, available⟩ :=
    releases.matched_available valid started history ledger selected
  exact ⟨_, producer, origin.value, known, origin.payloadEq,
    Witness.groupPublication_owner_of_registry generated valid origin available
      (Witness.groupPublication_contributorRegistry generated valid started history origin)⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
