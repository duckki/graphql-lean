import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.PublicationExtension

/-! Stream notice eligibility from the shared publication and failure witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A fresh stream cannot already have an accepted item failure
-----------------------------------------------------------------------------------------

/-- A contributor to a generated stream has that stream as its sole owner.
Witness: role separation excludes object tasks; an item's singleton owner must be the
supplied stream ref. No source execution or output-admission premise is needed.
-/
theorem ExecutedWork.streamContributor_owners {work stream dependencies producer}
    (generated : ExecutedWork work)
    (located : NodeAt work stream .stream dependencies producer)
    {occurrence owners} (known : TaskHasOwners work occurrence owners)
    (owner : stream.ref ∈ owners)
    : owners = [stream.ref] := by
  obtain ⟨parent, payload, task⟩ := known
  cases occurrence with
  | executionGroup address =>
      obtain ⟨groups, path, result, children, enclosing, atTask, sameOwners, _⟩ := task
      rw [sameOwners] at owner
      obtain ⟨group, member, sameRef⟩ := List.mem_map.mp owner
      exact False.elim
        (generated.groupStreamRefsDisjoint (.group atTask member) located sameRef)
  | item address ordinal =>
      obtain ⟨node, items, enclosing, result, children, _, _, sameOwners, _⟩ := task
      rw [sameOwners] at owner
      exact sameOwners.trans (congrArg List.singleton (List.mem_singleton.mp owner).symm)

namespace ConformancePlan

/-- An unannounced stream has no contributing failure through the supplied prefix.
Witness: each retained failure requires a previously announced owner, and a stream item
has only this one owner. Later cuts are excluded rather than used to justify the notice.
-/
theorem AnnouncedFailures.stream_unrecorded {work w stream dependencies producer count}
    (announced : AnnouncedFailures work w) (generated : ExecutedWork work)
    (located : NodeAt work stream .stream dependencies producer)
    (fresh : stream.ref ∉ announcedRefs (initialRefs work) (w.events.take count))
    {occurrence owners} (known : TaskHasOwners work occurrence owners)
    (owner : stream.ref ∈ owners)
    : occurrence ∉ failedBefore w.failures count := by
  intro recorded
  obtain ⟨entry, kept, same⟩ := List.mem_map.mp recorded
  obtain ⟨member, reached⟩ := List.mem_filter.mp kept
  have reached : entry.1 ≤ count := by simpa using reached
  obtain ⟨otherOwners, otherKnown, ref, contributes, notified⟩ := announced.2 entry member
  obtain ⟨parent, payload, task⟩ := known
  obtain ⟨otherParent, otherPayload, otherTask⟩ := otherKnown
  rw [same] at otherTask
  have single := generated.streamContributor_owners located
    (show TaskHasOwners work occurrence owners from ⟨parent, payload, task⟩) owner
  rw [← (task.unique otherTask).1, single] at contributes
  have equal := List.mem_singleton.mp contributes
  apply fresh
  rw [equal] at notified
  rcases List.mem_append.mp notified with initial | later
  · exact List.mem_append_left _ initial
  · obtain ⟨event, earlier, pending⟩ := List.mem_flatMap.mp later
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨event, List.take_subset_take_left w.events reached earlier, pending⟩)

-----------------------------------------------------------------------------------------
-- Retained producer evidence applies at the carrier with its own notices erased
-----------------------------------------------------------------------------------------

/-- A group-carried stream's producer was published strictly before the control carrier.
Witness: the retained inclusive publication cannot be the nonvalue group completion.
-/
theorem StreamNoticeProducers.group {work w index group groups streams child}
    (producers : StreamNoticeProducers work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ streams)
    : ∃ dependencies producer,
        NodeAt work child .stream dependencies (some producer)
        ∧ Published w.matching (w.events.take index) producer := by
  obtain ⟨dependencies, producer, located, published⟩ :=
    producers index _ selected child noticed
  rw [List.take_add_one, selected] at published
  refine ⟨dependencies, producer, located, ?_⟩
  rcases published_append_singleton_iff.mp published with earlier | current
  · exact earlier
  · exact False.elim current.1

/-- An item-carried stream keeps its producer publication after erasing the child notices.
Witness: publication before or at the carrier is unchanged by its notice lists. A producer
from the last item of a batch may therefore publish in this same atomic carrier.
-/
theorem StreamNoticeProducers.item {work w index stream items groups streams child}
    (producers : StreamNoticeProducers work w)
    (selected : w.events[index]? = some (.streamValues stream items groups streams))
    (noticed : child ∈ streams)
    : ∃ dependencies producer,
        NodeAt work child .stream dependencies (some producer)
        ∧ Published w.matching
            (w.events.take index ++ [.streamValues stream items [] []]) producer := by
  obtain ⟨dependencies, producer, located, published⟩ :=
    producers index _ selected child noticed
  rw [List.take_add_one, selected] at published
  refine ⟨dependencies, producer, located, ?_⟩
  simpa only [Option.toList_some, published_append_singleton_iff, IsValue] using published

/-- Fresh streams with a published producer need only the usual dependency readiness.
Witness: prior announcement licensing excludes direct item failures; publication support
excludes producer failure/cancellation. Failure cuts are frozen at the carrier's start,
so its own publication is visible without introducing a later failure into eligibility.
This is a derived local rule, not an additional scheduler or host-source assumption.
-/
theorem streamNotice_canAnnounce {work w index event plain stream dependencies producer}
    (generated : ExecutedWork work) (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (selected : w.events[index]? = some event)
    (sameValue : IsValue event ↔ IsValue plain) (noNotices : eventPending plain = [])
    (located : NodeAt work stream .stream dependencies (some producer))
    (published : Published w.matching (w.events.take index ++ [plain]) producer)
    (fresh : stream.ref ∉ announcedRefs (initialRefs work) (w.events.take index))
    (dependenciesReady
      : dependencies = []
        ∨ ∃ ref ∈ dependencies,
            DependencySatisfied work (initialRefs work) w.matching
              (w.events.take index ++ [plain])
              (w.failures.filter (fun entry => decide (entry.1 ≤ index))) ref)
    : CanAnnounce work (initialRefs work) w.matching (w.events.take index ++ [plain])
        (w.failures.filter (fun entry => decide (entry.1 ≤ index)))
        stream .stream dependencies (some producer) := by
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  have publishedActual : Published w.matching w.events producer := by
    have atCarrier : Published w.matching (w.events.take index ++ [event]) producer := by
      rcases published_append_singleton_iff.mp published with earlier | current
      · exact earlier.append [event]
      · exact published_append_singleton_iff.mpr
          (.inr ⟨sameValue.mpr current.1, current.2⟩)
    have prefixEq : w.events.take index ++ [event] = w.events.take (index + 1) := by
      simp only [List.take_add_one, selected, Option.toList_some]
    rw [prefixEq] at atCarrier
    simpa only [List.take_append_drop] using atCarrier.append (w.events.drop (index + 1))
  have failedPayloads : ∀ cut occurrence, (cut, occurrence) ∈ w.failures
      → ∃ owners producer payload,
          TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true :=
    fun cut occurrence member => (announced.1.2.2.1 (cut, occurrence) member).2.2
  have succeeded : TaskSucceeds work producer := by
    obtain ⟨position, output, atOutput, value, matched⟩ := publishedActual
    obtain ⟨owners, parent, payload, _, known, success, _⟩ :=
      support position output atOutput value
    exact ⟨owners, parent, payload, matched ▸ known, success⟩
  have safe : ¬TaskCancelled work w.matching (w.events.take index) w.failures producer := by
    intro cancelled
    have full := cancelled.append (w.events.drop index)
    rw [List.take_append_drop] at full
    exact support.cancelled_unpublished failedPayloads full publishedActual
  have frozen :=
    causality_append_eq (work := work) (matching := w.matching)
      (events := w.events.take index)
      (failures := w.failures.filter (fun entry => decide (entry.1 ≤ index)))
      (by
        intro entry member; simpa only [length]
          using (of_decide_eq_true (List.mem_filter.mp member).2)) [plain]
  have healthy : ¬NodeFailed work w.matching (w.events.take index) w.failures stream.ref := by
    apply generated.streamHealthy_of_producerSafety failedPayloads located
      (fun source same => (Option.some.inj same) ▸ succeeded)
      (fun source same => (Option.some.inj same) ▸ safe)
    · intro occurrence owners known owner
      simpa only [length] using announced.stream_unrecorded generated located fresh known owner
    · rcases dependenciesReady with empty | ⟨ref, member, ready⟩
      · exact .inl empty
      · refine .inr ⟨ref, member, ?_⟩
        simpa only [frozen.1, nodeFailed_filter (Nat.le_of_eq length)] using ready.1
  refine ⟨?_, .inl ⟨?_, .inl rfl⟩, ?_, dependenciesReady⟩
  · simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, noNotices, List.nil_append, List.append_nil] using fresh
  · simpa only [frozen.1, nodeFailed_filter (Nat.le_of_eq length)] using healthy
  · intro source same
    exact (Option.some.inj same) ▸ published

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
