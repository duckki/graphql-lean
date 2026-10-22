import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublisherRegistry
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupPublicationMatching
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationOwnership

/-! Actual startup object wire owners satisfy longest-open selection with healthy support. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Exact contributor metadata and active/open registry agreement establish the actual
publisher's longest-path owner rule. The healthy supporter remains the release group;
the selected wire owner may be a different failed co-owner that is still open.
-/
theorem Witness.startup_groupPublication_owner_of_registry {work}
    {inputs : List (List GraphEvent)} {w : Witness} {index owner payload}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (origin
      : GroupPublicationOrigin
          {
            active :=
              ((State.initialize (Work.fromExecution work) startup)).initialGroups
              ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
          }
          (((State.initialize (Work.fromExecution work) startup)).rawBatches inputs).2
          index owner payload)
    (available
      : HealthyOpenOwner work (initialRefs work) w.matching (w.events.take index)
          w.failures (origin.value.deliveryGroups.map Execution.DeliveryNode.ref)
          origin.group)
    (registry
      : ∀ candidate ∈ origin.value.deliveryGroups,
          candidate.ref
            ∈ (({
                  active :=
                    ((State.initialize (Work.fromExecution work) startup)).initialGroups
                    ++ ((State.initialize (Work.fromExecution work)
                          startup)).initialStreams
                }
                : IncrementalPublisher).normalizeBatch
                origin.before).1.active.map
                Execution.DeliveryNode.ref
          ↔ Open (initialRefs work) (w.events.take index) candidate.ref)
    : PublicationOwner work (initialRefs work) w.matching (w.events.take index) w.failures
        (origin.value.deliveryGroups.map Execution.DeliveryNode.ref) owner := by
  let publisher : IncrementalPublisher :=
    { active :=
        ((State.initialize (Work.fromExecution work) startup)).initialGroups
          ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams }
  let current := (publisher.normalizeBatch origin.before).1
  have located (candidate : Execution.DeliveryNode)
      (member : candidate ∈ origin.value.deliveryGroups)
      : ∃ kind dependencies producer, NodeAt work candidate kind dependencies producer := by
    obtain ⟨dependencies, producer, known⟩ :=
      Witness.startup_groupPublication_contributorsLocated startup valid origin candidate member
    exact ⟨.group, dependencies, producer, known⟩
  have contributes := openOwner_contributor_of_coherent work generated.nodeRefCoherent
    origin.value located (initialRefs work) (w.events.take index) origin.group available.1
  have active (candidate : Execution.DeliveryNode)
      (member : candidate ∈ origin.value.deliveryGroups)
      : (current.active.any (fun node => node.ref == candidate.ref) = true)
        ↔ Open (initialRefs work) (w.events.take index) candidate.ref := by
    rw [← registry candidate member]
    simp only [List.any_eq_true, beq_iff_eq, List.mem_map, current, publisher]
  have ownerRule := current.getBestIdAndSubPath_owner work (initialRefs work) w.matching
    (w.events.take index) w.failures origin.group origin.value
    ((active origin.group contributes).mpr available.1.2.2) contributes
    (by
      intro candidate member
      rw [active candidate member]
      exact ⟨fun opened => ⟨located candidate member,
        List.mem_map.mpr ⟨candidate, member, rfl⟩, opened⟩, fun known => known.2.2⟩)
    ⟨origin.group, available⟩ generated.nodeRefCoherent located
  simpa only [origin.ownerEq] using ownerRule

/-- Each actual startup object contributor has exact active/open agreement at its
original raw prefix. Atomic splitting and earlier values of that block change no notices.
-/
theorem Witness.startup_groupPublication_contributorRegistry
    {work inputs index owner payload} {w : Witness} (generated : ExecutedWork work)
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (_started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (origin
      : GroupPublicationOrigin
          {
            active :=
              ((State.initialize (Work.fromExecution work) startup)).initialGroups
              ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
          }
          (((State.initialize (Work.fromExecution work) startup)).rawBatches inputs).2
          index owner payload)
    : ∀ candidate ∈ origin.value.deliveryGroups,
        candidate.ref
          ∈ (({
                active :=
                  ((State.initialize (Work.fromExecution work) startup)).initialGroups
                  ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
              }
              : IncrementalPublisher).normalizeBatch
              origin.before).1.active.map
              Execution.DeliveryNode.ref
        ↔ Open (initialRefs work) (w.events.take index) candidate.ref := by
  let publisher : IncrementalPublisher :=
    { active :=
        ((State.initialize (Work.fromExecution work) startup)).initialGroups
          ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams }
  have isPrefix : origin.before.IsPrefix
      (((State.initialize (Work.fromExecution work)
          startup)).rawBatches inputs).2 :=
    ⟨_, origin.rawEq.symm⟩
  have shape := ((State.initialize (Work.fromExecution work)
    startup)).rawBatches_nonemptyValues inputs valid.nonemptyItems
  have normalizedShape := (publisher.normalizeBatch_nonemptyValues origin.before
    (fun event member => shape event (isPrefix.subset member))).2
  obtain ⟨pending, completed⟩ := publicationAtoms_list_noticeState _ normalizedShape
  obtain ⟨silentPending, silentCompleted⟩ := GroupPublicationOrigin.object_prefix_refs
    (publisher.normalizeBatch origin.before).1 origin.group origin.values origin.offset
  simp only [pendingRefs, completedRefs] at pending completed silentPending silentCompleted
  have carrier := (Witness.startup_rawBatches_nonterminal startup history origin.carrier
    (by intro impossible; cases impossible)).1
  have within := (List.getElem?_eq_some_iff.mp carrier).1
  have earlier := origin.before_carrier
  have valuePrefix := origin.valuePrefix
  rw [Witness.startup_rawBatches_prefix startup history index (by omega)] at valuePrefix
  intro candidate member
  obtain ⟨dependencies, producer, known⟩ :=
    Witness.startup_groupPublication_contributorsLocated startup valid origin candidate member
  have registry := generated.startup_rawBatchPrefix_groupRegistry startup valid known isPrefix
  dsimp only at registry
  rw [registry, valuePrefix]
  simp only [Open, announcedRefs, pendingRefs, completedRefs, List.flatMap_append]
  rw [pending, completed, silentPending, silentCompleted, List.append_nil, List.append_nil]
  simp only [publisher, initialRefs, initialQueue, State.initializeWithStartup_initialGroups,
    State.initializeWithStartup_initialStreams]

/-- Every actual object atom selects an open longest-path contributor with healthy support.
Witness: derive the publisher registry on the same recovered raw prefix and apply its
max-selection theorem, keeping the exact task occurrence from the shared closure ledger.
-/
theorem StartupGroupPublicationReleases.matched_owner {work inputs w}
    {startup : InitialStartup}
    (releases : StartupGroupPublicationReleases work startup inputs w)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    {index owner values} (selected : w.events[index]? = some (.groupValues owner values))
    : ∃ owners producer value,
        TaskAt work (w.matching index) owners producer
          (.object value.path (.ok (value.data, value.errors)))
        ∧ values = [value]
        ∧ PublicationOwner work (initialRefs work) w.matching (w.events.take index)
            w.failures owners owner := by
  obtain ⟨origin, ⟨producer, known⟩, available⟩ :=
    releases.matched_available valid started history ledger selected
  exact ⟨_, producer, origin.value, known, origin.payloadEq,
    Witness.startup_groupPublication_owner_of_registry generated startup valid origin available
      (Witness.startup_groupPublication_contributorRegistry generated startup valid started
        history origin)⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
