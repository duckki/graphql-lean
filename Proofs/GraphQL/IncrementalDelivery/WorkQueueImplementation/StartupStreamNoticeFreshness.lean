import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamNoticeAdmission

/-! Group-released stream notices are fresh on the common conformance witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Replay uniqueness survives normalization and atomic expansion
-----------------------------------------------------------------------------------------

/-- Any canonical stream notice excludes all strictly earlier stream notices.
Witness: the selected prefix is a sublist of the globally unique inventory; splitting it
at the carrier separates old refs from every ref announced by that carrier.
-/
theorem startup_streamNotice_ref_fresh {work inputs index event ref} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event) (noticed : ref ∈ streamNoticeRefs event)
    : ref
      ∉ (initialQueue work).initialStreams.map Execution.DeliveryNode.ref
        ++ (w.events.take index).flatMap streamNoticeRefs := by
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp selected
  have split : w.events = w.events.take index ++ event :: w.events.drop (index + 1) := by
    rw [← value, ← List.drop_eq_getElem_cons bound]
    exact (List.take_append_drop index w.events).symm
  have unique := startup_streamNoticeRefs_nodup generated startup valid started history
  conv at unique => arg 1; arg 2; arg 2; rw [split]
  simp only [List.flatMap_append, List.flatMap_cons, ← List.append_assoc] at unique
  intro repeated
  exact (List.nodup_append.mp (List.nodup_append.mp unique).1).2.2
    ref repeated ref noticed rfl

-----------------------------------------------------------------------------------------
-- Successful group controls have fresh, eligible, and distinct child streams
-----------------------------------------------------------------------------------------

/-- A group-released stream is fresh against all earlier group and stream announcements.
Witness: generated role separation converts a repeated notice to a stream-only notice,
which contradicts the derived global stream inventory.
-/
theorem startup_groupStreamNotice_fresh {work inputs index group groups streams child}
    {w : Witness} (generated : ExecutedWork work)
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ streams)
    : child.ref ∉ announcedRefs (initialRefs work) (w.events.take index) := by
  obtain ⟨dependencies, producer, known⟩ :=
    State.startup_runNormalized_atomicStreamNoticesLocated startup valid _
      (List.mem_of_getElem? (Witness.startup_event startup history selected).1) child noticed
  intro repeated
  exact startup_streamNotice_ref_fresh generated startup valid started history selected
    (List.mem_map_of_mem noticed)
    (startup_streamNode_announced_stream generated startup valid history known repeated)

/-- Actual group-produced stream notices satisfy complete eligibility without extra laws.
Witness: derive freshness from consumed links and reuse the existing shared producer,
healthy dependency, and historical failure-support certificates.
-/
theorem startup_groupStreamNotice_canAnnounce_of_replay
    {work inputs w index group groups streams child} (generated : ExecutedWork work)
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (healthy : GroupSuccessesHealthy work w) (producers : StreamNoticeProducers work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ streams)
    : ∃ dependencies producer,
        NodeAt work child .stream dependencies producer
        ∧ CanAnnounce work (initialRefs work) w.matching
            (w.events.take index ++ [.groupSuccess group [] []])
            (w.failures.filter (fun entry => decide (entry.1 ≤ index)))
            child .stream dependencies producer :=
  startup_groupStreamNotice_canAnnounce generated startup valid history announced support
    healthy producers selected noticed
    (startup_groupStreamNotice_fresh generated startup valid started history selected
      noticed)

/-- A successful group's combined child-notice list has no repeated ref.
Witness: both global notice inventories supply internal uniqueness; generated roles
exclude collisions between group and stream lists on the same carrier.
-/
theorem startup_groupCarrierNoticeRefs_nodup {work inputs group groups streams}
    {index : Nat} {w : Witness} (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : ((groups ++ streams).map Execution.DeliveryNode.ref).Nodup := by
  have groupUnique := (List.nodup_append.mp
    (startup_groupNoticeRefs_nodup generated startup matched valid started history)).2.1
  have streamUnique := (List.nodup_append.mp
    (startup_streamNoticeRefs_nodup generated startup valid started history)).2.1
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp (List.mem_of_getElem? selected)
  rw [split, List.flatMap_append, List.flatMap_cons] at groupUnique streamUnique
  have atFull := List.mem_of_getElem? (Witness.startup_event startup history selected).1
  have groupKnown :=
    State.startup_runNormalized_atomicGroupNoticesLocated generated startup valid _ atFull
  have streamKnown := State.startup_runNormalized_atomicStreamNoticesLocated startup valid _ atFull
  rw [List.map_append]
  refine List.nodup_append.mpr
    ⟨(List.nodup_append.mp (List.nodup_append.mp groupUnique).2.1).1,
      (List.nodup_append.mp (List.nodup_append.mp streamUnique).2.1).1, ?_⟩
  intro first groupMember second streamMember same
  obtain ⟨group, included, groupRef⟩ := List.mem_map.mp groupMember
  obtain ⟨stream, noticed, streamRef⟩ := List.mem_map.mp streamMember
  obtain ⟨parents, birth, descriptor⟩ := groupKnown group included
  obtain ⟨enclosing, producer, known⟩ := streamKnown stream noticed
  exact generated.groupStreamRefsDisjoint descriptor known
    (groupRef.trans (same.trans streamRef.symm))

/-- Item-produced stream notices satisfy full eligibility without an extra freshness law.
Witness: derive freshness from actual registration and combine it with the existing joint
producer, dependency, and failure-support certificates on the unchanged witness.
-/
theorem startup_itemStreamNotice_canAnnounce_of_replay
    {work inputs w index stream values groups streams child}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (producers : StreamNoticeProducers work w)
    (selected : w.events[index]? = some (.streamValues stream values groups streams))
    (noticed : child ∈ streams)
    : ∃ producer,
        NodeAt work child .stream [] producer
        ∧ CanAnnounce work (initialRefs work) w.matching
            (w.events.take index ++ [.streamValues stream values [] []])
            (w.failures.filter (fun entry => decide (entry.1 ≤ index)))
            child .stream [] producer :=
  startup_itemStreamNotice_canAnnounce generated startup valid started history announced
    support producers selected noticed
    (startup_itemStreamNotice_fresh generated startup valid started history selected
      noticed)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
