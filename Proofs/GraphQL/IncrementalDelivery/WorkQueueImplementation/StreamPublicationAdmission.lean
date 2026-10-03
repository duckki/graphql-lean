import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamEventAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedDescriptors

/-! Actual stream publications have full causal readiness and their unique healthy owner. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A stream value uses its sole contributing owner, independently of child notice rules
-----------------------------------------------------------------------------------------

/-- Every stream value has exact provenance, complete readiness, and a valid wire owner.
All clauses use the same witness and strict output prefix. This certificate intentionally
leaves admission of the value's carried child notices to the separate announcement proof.
-/
def StreamPublicationReady (work : Execution.Work) (w : Witness) : Prop :=
  ∀ index stream values groups children,
    w.events[index]? = some (.streamValues stream values groups children)
    → ∃ value producer,
        values = [value]
        ∧ TaskAt work (w.matching index) [stream.ref] producer
            (.item stream (.ok (value.item, value.errors)))
        ∧ CanPublish work w.matching (w.events.take index) w.failures (w.matching index)
            producer
        ∧ PublicationOwner work (initialRefs work) w.matching (w.events.take index)
            w.failures [stream.ref] stream

/-- The canonical stream-readiness certificate has a healthy longest-path owner.
Witness: the actual stream action is open and healthy; exact item provenance gives its
sole owner. Existing ref coherence identifies every competing descriptor with that same
stream, so longest-path selection introduces no new choice or source assumption.
-/
theorem streamPublicationReady_of_certificates {work inputs w streams}
    (generated : ExecutedWork work) (coherent : NodeRefCoherent work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (ready : StreamValuesReady work w)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (cuts
      : StreamFailureCuts work
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streams)
    (exactCuts
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures
        = mergeFailureCuts
            (sourceObjectFailureCuts 0
              (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2))
            streams)
    : StreamPublicationReady work w := by
  intro index stream values groups children selected
  obtain ⟨value, producer, singleton, task, canPublish⟩ :=
    ready index stream values groups children selected
  obtain ⟨_, dependencies, known⟩ := itemTask_owner_nodeAt task
  obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
  have opened := createWorkQueue_runNormalized_streamOpenAt generated valid atFull
    List.mem_cons_self
  dsimp only at opened
  rw [beforeEq] at opened
  have healthy := streamAction_healthy_of_successfulItems generated valid started history
    announced safe cuts exactCuts known selected rfl
      (by intros; intro impossible; cases impossible)
  have active : OpenOwner work (initialRefs work) (w.events.take index) [stream.ref]
      stream := ⟨⟨.stream, dependencies, producer, known⟩, List.mem_cons_self, opened⟩
  refine ⟨value, producer, singleton, task, canPublish,
    active, ⟨stream, active, healthy⟩, ?_⟩
  intro other available
  obtain ⟨⟨kind, parents, source, otherKnown⟩, member, _⟩ := available
  have same := coherent other kind parents source stream .stream dependencies producer
    otherKnown known (List.mem_singleton.mp member)
  rw [same]
  exact Nat.le_refl _

-----------------------------------------------------------------------------------------
-- Only the actual carried notices remain before full stream-value admission
-----------------------------------------------------------------------------------------

/-- Stream-value admission is exactly its remaining child-announcement obligation.
Witness: the existing readiness/owner certificate supplies every other event clause;
the forward implication projects announcements from actual admission. Failure cuts stay
frozen at the event start even though notices see the carrier publication.
-/
theorem streamValueAllowed_iff_announcements {work w index stream values groups children}
    (ready : StreamPublicationReady work w)
    (selected : w.events[index]? = some (.streamValues stream values groups children))
    : EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
        (.streamValues stream values groups children)
      ↔ Announcements work (initialRefs work) w.matching
          (w.events.take index ++ [.streamValues stream values [] []])
          (w.failures.filter (fun entry => entry.1 ≤ index)) groups children := by
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  simp only [EventAllowed, length]
  constructor
  · rintro ⟨_, _, _, _, _, _, _, announcements⟩
    exact announcements
  · intro announcements
    obtain ⟨value, producer, singleton, task, canPublish, owner⟩ :=
      ready index stream values groups children selected
    refine ⟨[stream.ref], producer, value, singleton, task,
      ?_, ?_, announcements⟩
    · exact (canPublish_filter (Nat.le_of_eq length)).mpr canPublish
    · exact (owner_filter (Nat.le_of_eq length)).mpr owner

/-- An actual stream value carrying no notices now satisfies the full event rule.
Witness: the exact announcement reduction leaves only empty, trivially valid lists.
The original event and history are unchanged; notices are not dropped from other events.
-/
theorem streamValueAllowed_without_notices {work w index stream values}
    (ready : StreamPublicationReady work w)
    (selected : w.events[index]? = some (.streamValues stream values [] []))
    : EventAllowed work (initialRefs work) w.matching (w.events.take index) w.failures
        (.streamValues stream values [] []) := by
  apply (streamValueAllowed_iff_announcements ready selected).mpr
  simp [Announcements]

/-- Mixed replay shares stream publication readiness and the proved control cases.
Witness: retain the common canonical construction, attach unique healthy stream owners,
and reuse failed/successful stream admission. Generated descriptor coherence supplies
unique owner metadata; no extra host law or admission premise is introduced.
-/
theorem mixed_eventCertificates {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ UncancelledFailures work w
        ∧ FailureAdmission work w
        ∧ StreamSuccessAdmission work w
        ∧ StreamPublicationReady work w := by
  obtain ⟨w, history, shape, announced, uncancelled, _, accounted, ready, safe,
    streams, cuts, exactCuts⟩ := mixed_failureCertificates_with_cuts generated valid started
  exact ⟨w, history, shape, announced, uncancelled,
    failureAdmission_of_announced generated valid history announced,
    streamSuccessAdmission_of_successfulItems generated valid started history announced
      accounted safe cuts exactCuts,
    streamPublicationReady_of_certificates generated generated.nodeRefCoherent valid started
      history announced
      ready safe cuts exactCuts⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
