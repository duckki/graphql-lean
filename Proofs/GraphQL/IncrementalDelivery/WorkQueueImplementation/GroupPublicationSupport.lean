import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationCarrierOrigins
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationContributors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublisherOwnership
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublisherRegistry

/-! Successful raw release carriers support remapped publications on the shared witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Started replay has exactly the normalized raw nonterminal history
-----------------------------------------------------------------------------------------

/-- Removing the optional final marker leaves exactly normalized sequential raw replay.
Witness: the started-batch equation and the handler-level exclusion of termination.
All host batches, owner choices, and publication positions are retained.
-/
theorem createWorkQueue_nonterminalAtoms_flattened {work : Execution.Work}
    (inputs : List (List GraphEvent)) (started : inputsStarted work inputs = true)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      queue.nonterminalAtoms inputs
      = (publisher.normalizeBatch (queue.rawEventReplay inputs.flatten).2).2.flatMap
          publicationAtoms := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let atoms := (publisher.normalizeBatch (queue.rawEventReplay inputs.flatten).2).2.flatMap
    publicationAtoms
  have absent : Execution.WorkQueueEvent.workQueueTermination ∉ atoms := by
    rw [publicationAtoms_list_termination_mem,
      IncrementalPublisher.normalizeBatch_termination_mem]
    exact queue.rawEventReplay_noTermination inputs.flatten
  obtain ⟨terminal, outputs⟩ := createWorkQueue_runNormalized_flattened inputs started
  change (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms
    = atoms ++ (if terminal then [.workQueueTermination] else []) at outputs
  change ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms).filter _ = atoms
  rw [outputs, List.filter_append]
  cases terminal <;> simp only [Bool.false_eq_true, ↓reduceIte, List.filter_nil,
    List.filter_cons, List.append_nil] <;>
    apply List.filter_eq_self.mpr <;>
    intro event member <;>
    cases event <;> try rfl
  all_goals exact False.elim (absent member)

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- A remapped ID does not hide the healthy group that actually flushed its value
-----------------------------------------------------------------------------------------

/-- Every actual object atom has an exact raw release origin on the canonical history.
Witness: started replay preserves the raw output and the queue pairs each publication
with its triggering group's successful closure. No publication admission is assumed.
-/
theorem Witness.groupPublication_origin {work inputs} {w : Witness} {index owner payload}
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupValues owner payload))
    : let queue := initialQueue work
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      Nonempty
        (GroupPublicationOrigin publisher (queue.rawEventReplay inputs.flatten).2
          index owner payload) := by
  rw [history, createWorkQueue_nonterminalAtoms_flattened inputs started] at selected
  exact ((initialQueue work).rawEventReplay_publicationPairs inputs.flatten).normalized_origin
    _ selected

/-- The actual raw release group is known, open, and historically healthy at its value.
The selected wire owner may be different, and may already be failed. Contributor
membership and longest-open owner selection remain separate obligations.
Witness: its unchanged successful carrier supplies provenance and durable health; the
intervening object-only segment has exactly the same notice state.
-/
theorem Witness.groupPublication_releaseReady {work inputs w index owner payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (healthy : GroupSuccessesHealthy work w)
    (origin
      : GroupPublicationOrigin
          {
            active :=
              (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
          }
          ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload)
    : (∃ dependencies producer, NodeAt work origin.group .group dependencies producer)
      ∧ Open (initialKeys work) (w.events.take index) origin.group.key
      ∧ ¬NodeFailed work w.matching (w.events.take index) w.failures
          origin.group.key := by
  have historyEq := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  have carrier : w.events[origin.carrierIndex]?
      = some (.groupSuccess origin.group origin.groups origin.streams) := by
    rw [historyEq]
    exact origin.carrier
  obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history carrier
  have known := createWorkQueue_runNormalized_atomicGroupClosuresLocated generated valid _
    (List.mem_of_getElem? atFull)
  have opened := createWorkQueue_runNormalized_groupClosureOpenAt generated valid atFull
    List.mem_cons_self
  dsimp only at opened
  rw [beforeEq] at opened
  have noticeState := origin.noticeState
  dsimp only at noticeState
  rw [← historyEq] at noticeState
  refine ⟨known, ?_, healthy.atPrefix carrier index⟩
  simpa only [Open, announcedKeys, initialKeys, initialQueue, noticeState.1,
    noticeState.2]
    using opened

/-- Every object atom retains its actual release origin and that group's known, open,
healthy status. This is weaker than `PublicationAdmission`: it does not yet connect the
raw group's task memberships to the shared matching or validate the remapped owner.
-/
def GroupPublicationReleases (work : Execution.Work) (inputs : List (List GraphEvent))
    (w : Witness)
    : Prop :=
  ∀ index owner payload,
    w.events[index]? = some (.groupValues owner payload)
    → ∃ origin
          : GroupPublicationOrigin
              {
                active :=
                  (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
              }
              ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload,
        (∃ dependencies producer, NodeAt work origin.group .group dependencies producer)
        ∧ Open (initialKeys work) (w.events.take index) origin.group.key
        ∧ ¬NodeFailed work w.matching (w.events.take index) w.failures origin.group.key

/-- All actual object publications have healthy raw release groups on the shared witness.
Witness: recover each raw pair, then reuse successful-carrier health and unchanged notice
state. The input laws are unchanged and no publication-admission premise is used.
-/
theorem groupPublicationReleases_of_groupHealth {work inputs w}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (healthy : GroupSuccessesHealthy work w)
    : GroupPublicationReleases work inputs w := by
  intro index owner payload selected
  obtain ⟨origin⟩ := Witness.groupPublication_origin started history selected
  exact ⟨origin, Witness.groupPublication_releaseReady generated valid started history
    healthy origin⟩

/-- Every retained raw release group is an available contributing owner for its full value.
Witness: actual raw membership supplies the owner key; the release certificate supplies
provenance, openness, and health on the same history, matching, and failure cuts.
Connecting that value to the selected matching occurrence remains a separate ledger step.
-/
theorem GroupPublicationReleases.available {work inputs w}
    (releases : GroupPublicationReleases work inputs w)
    (valid : ValidGraphEvents work inputs.flatten) {index owner payload}
    (selected : w.events[index]? = some (.groupValues owner payload))
    : ∃ origin
          : GroupPublicationOrigin
              {
                active :=
                  (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
              }
              ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload,
        HealthyOpenOwner work (initialKeys work) w.matching (w.events.take index)
          w.failures (origin.value.deliveryGroups.map Execution.DeliveryNode.key)
          origin.group := by
  obtain ⟨origin, ⟨dependencies, producer, known⟩, opened, healthy⟩ :=
    releases index owner payload selected
  have member := createWorkQueue_rawEventReplay_publicationContributors valid
    origin.group origin.values origin.members.1 origin.value origin.members.2
  exact ⟨origin, ⟨⟨.group, dependencies, producer, known⟩, member, opened⟩, healthy⟩

/-- The raw release origin retains every contributor's structural descriptor.
Witness: recover its actual successful source input with the full contributor-bearing
value, then apply source matching. Equal response data does not identify a task here.
-/
theorem Witness.groupPublication_contributorsLocated {work}
    {inputs : List (List GraphEvent)} {index owner payload}
    (valid : ValidGraphEvents work inputs.flatten)
    (origin
      : GroupPublicationOrigin
          {
            active :=
              (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
          }
          ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload)
    : ∀ contributor ∈ origin.value.deliveryGroups,
        ∃ dependencies producer,
          NodeAt work contributor .group dependencies producer := by
  obtain ⟨occurrence, result, _, same, source⟩ :=
    createWorkQueue_rawEventReplay_valueSource valid origin.members.1 origin.members.2
  intro contributor member
  exact source.success_contributorsLocated contributor (same.symm ▸ member)

/-- Actual raw-value ownership reduces to registry agreement on its contributing groups.
Witness: the release group is an available contributor; structural key coherence recovers
its full descriptor. The real max-selection fold then chooses a longest open contributor,
retaining the healthy release group as separate support. This theorem does not assume
that the selected wire owner itself is healthy.
-/
theorem Witness.groupPublication_owner_of_registry {work}
    {inputs : List (List GraphEvent)} {w : Witness} {index owner payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (origin
      : GroupPublicationOrigin
          {
            active :=
              (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
          }
          ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload)
    (available
      : HealthyOpenOwner work (initialKeys work) w.matching (w.events.take index)
          w.failures (origin.value.deliveryGroups.map Execution.DeliveryNode.key)
          origin.group)
    (registry
      : ∀ candidate ∈ origin.value.deliveryGroups,
          candidate.key
            ∈ (({
                  active :=
                    (initialQueue work).initialGroups
                    ++ (initialQueue work).initialStreams
                }
                : IncrementalPublisher).normalizeBatch
                origin.before).1.active.map
                Execution.DeliveryNode.key
          ↔ Open (initialKeys work) (w.events.take index) candidate.key)
    : PublicationOwner work (initialKeys work) w.matching (w.events.take index) w.failures
        (origin.value.deliveryGroups.map Execution.DeliveryNode.key) owner := by
  let publisher : IncrementalPublisher :=
    { active := (initialQueue work).initialGroups ++ (initialQueue work).initialStreams }
  let current := (publisher.normalizeBatch origin.before).1
  have located (candidate : Execution.DeliveryNode)
      (member : candidate ∈ origin.value.deliveryGroups)
      : ∃ kind dependencies producer, NodeAt work candidate kind dependencies producer := by
    obtain ⟨dependencies, producer, known⟩ :=
      Witness.groupPublication_contributorsLocated valid origin candidate member
    exact ⟨.group, dependencies, producer, known⟩
  have contributes := openOwner_contributor_of_coherent work generated.nodeKeyCoherent
    origin.value located (initialKeys work) (w.events.take index) origin.group available.1
  have active (candidate : Execution.DeliveryNode)
      (member : candidate ∈ origin.value.deliveryGroups)
      : (current.active.any (fun node => node.key == candidate.key) = true)
        ↔ Open (initialKeys work) (w.events.take index) candidate.key := by
    rw [← registry candidate member]
    simp only [List.any_eq_true, beq_iff_eq, List.mem_map, current, publisher]
  have ownerRule := current.getBestIdAndSubPath_owner work (initialKeys work) w.matching
    (w.events.take index) w.failures origin.group origin.value
    ((active origin.group contributes).mpr available.1.2.2) contributes
    (by
      intro candidate member
      rw [active candidate member]
      exact ⟨fun opened => ⟨located candidate member,
        List.mem_map.mpr ⟨candidate, member, rfl⟩, opened⟩, fun known => known.2.2⟩)
    ⟨origin.group, available⟩ generated.nodeKeyCoherent located
  simpa only [origin.ownerEq] using ownerRule

/-- The same mixed witness now carries each object value's healthy raw release origin.
Witness: extend the existing batching, failure, stream, and group-accounting certificates
without changing their history, publication matching, or ordered failure inventory.
-/
theorem mixed_groupReleaseCertificates {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ FailureAdmission work w
        ∧ StreamSuccessAdmission work w
        ∧ StreamPublicationReady work w
        ∧ GroupSuccessesHealthy work w
        ∧ GroupSuccessesAccounted work w
        ∧ BufferedClosureLedger work inputs w
        ∧ GroupPublicationReleases work inputs w := by
  obtain ⟨w, history, shape, announced, uncancelled, failures, streams, ready, healthy,
    accounted, ledger⟩ := mixed_groupAccountingCertificates generated valid started
  exact ⟨w, history, shape, announced, uncancelled, failures, streams, ready, healthy,
    accounted, ledger,
    groupPublicationReleases_of_groupHealth generated valid started history healthy⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
