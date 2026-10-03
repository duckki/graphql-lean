import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetainedNoticeProducers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyClosureAccounting

/-! Retained notice evidence moves to the carrier without admitting later failure cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The contract checks notices after their carrier, before adding those same notices
-----------------------------------------------------------------------------------------

/-- The proof-side carrier used by `EventAllowed`, with its new child notices removed. -/
def withoutChildNotices : Execution.WorkQueueEvent → Execution.WorkQueueEvent
  | .groupSuccess group _ _ => .groupSuccess group [] []
  | .streamValues stream values _ _ => .streamValues stream values [] []
  | event => event

/-- Clearing child notices changes neither value status nor completion refs.
Witness: only group-success and stream-value constructors carry child notices.
-/
theorem withoutChildNotices_projections (event : Execution.WorkQueueEvent)
    : (IsValue event ↔ IsValue (withoutChildNotices event))
      ∧ eventPending (withoutChildNotices event) = []
      ∧ eventCompleted (withoutChildNotices event) = eventCompleted event := by
  cases event <;> simp [withoutChildNotices, IsValue, eventPending, eventCompleted]

-----------------------------------------------------------------------------------------
-- Extending a carrier does not extend its frozen failure inventory
-----------------------------------------------------------------------------------------

/-- Once cuts are frozen at `bound`, later prefix lengths reveal no additional failures.
Witness: the two cutoff filters collapse to their smaller bound, retaining original order.
-/
theorem failedBefore_frozen_extend (failures : FailureCuts) {bound count : Nat}
    (reached : bound ≤ count)
    : failedBefore (failures.filter (fun entry => entry.1 ≤ bound)) count
      = failedBefore failures bound := by
  unfold failedBefore
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro entry _
  rw [← Bool.decide_and]
  have same : (entry.1 ≤ count ∧ entry.1 ≤ bound) ↔ entry.1 ≤ bound := by omega
  simp only [same]

/-- Replacing a carrier without changing whether it publishes a value preserves publications.
Witness: earlier publications are unchanged; the final occurrence uses the same matching
entry and value flag. Notice lists are not part of the publication relation.
-/
theorem published_carrier_eq {matching : PublicationMatching}
    {events : List Execution.WorkQueueEvent} {left right : Execution.WorkQueueEvent}
    (same : IsValue left ↔ IsValue right)
    : Published matching (events ++ [left]) = Published matching (events ++ [right]) := by
  funext occurrence
  apply propext
  simp only [published_append_singleton_iff, same]

/-- Removing only a carrier's notices preserves the publication-support certificate.
Witness: reuse earlier support and the last event's task, healthy owner, and producer.
No announcement-admission premise is involved.
-/
theorem PublicationSupport.replace_last {work matching events failures left right}
    (support : PublicationSupport work matching (events ++ [left]) failures)
    (same : IsValue left ↔ IsValue right)
    : PublicationSupport work matching (events ++ [right]) failures := by
  have prior : PublicationSupport work matching events failures := by
    simpa using support.take events.length
  apply prior.append_event
  intro value
  have last := support events.length left (by simp) (same.mpr value)
  simpa using last

-----------------------------------------------------------------------------------------
-- A notice carrier cannot consume the retained group's object-task memberships
-----------------------------------------------------------------------------------------

/-- Retained group contents remain unpublished after a control or item-only carrier.
Witness: a retained membership is an object occurrence by permanent registration. A
carrier either publishes nothing or names an item occurrence, so it cannot publish that
membership. Task/error contents and source prerequisites retain the same emitting queue.
-/
theorem RetainedNoticeContents.append_nonObject
    {work matching events failed received child event}
    (contents : RetainedNoticeContents work matching events failed received child)
    (itemOnly
      : IsValue event → ∃ address ordinal, matching events.length = .item address ordinal)
    : RetainedNoticeContents work matching (events ++ [event]) failed received child := by
  obtain ⟨located, queue, node, found, same, retained, sound, registered, cached,
    ready, unpublished⟩ := contents
  refine ⟨located, queue, node, found, same, retained, sound, registered, cached, ready, ?_⟩
  intro occurrence member published
  rcases published_append_singleton_iff.mp published with earlier | current
  · exact unpublished occurrence member earlier
  · obtain ⟨address, ordinal, isItem⟩ := itemOnly current.1
    obtain ⟨task, taskMember, sameTask, _⟩ := sound node (List.mem_of_find?_eq_some found)
      occurrence member
    obtain ⟨source, _, _, isObject, _⟩ := (registered task taskMember).1
    have impossible : Occurrence.executionGroup source = .item address ordinal :=
      isObject.symm.trans (sameTask.trans (current.2.symm.trans isItem))
    cases impossible

namespace ConformancePlan

/-- A successful carrier satisfies its own dependency at the frozen notice boundary.
Witness: durable group health restricts to the carrier's initial cut, while the carrier
itself supplies completion. No admission of its carried notices is assumed.
-/
theorem groupSuccess_dependencySatisfied_noticeCarrier
    {work} {w : Witness} {index group groups streams}
    (healthy : GroupSuccessesHealthy work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : DependencySatisfied work (initialRefs work) w.matching
        (w.events.take index ++ [.groupSuccess group [] []])
        (w.failures.filter (fun entry => entry.1 ≤ index)) group.ref := by
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  have frozen :=
    causality_append_eq (work := work) (matching := w.matching)
      (events := w.events.take index)
      (failures := w.failures.filter (fun entry => entry.1 ≤ index))
      (by
        intro entry member; simpa only [length]
          using (of_decide_eq_true (List.mem_filter.mp member).2))
      [.groupSuccess group [] []]
  refine ⟨?_, .inr (.inl ?_)⟩
  · simpa only [frozen.1, nodeFailed_filter (Nat.le_of_eq length)]
      using healthy.atPrefix selected index
  · simp [completedRefs, eventCompleted]

/-- Removing child notices keeps healthy completed-dependency accounting at the frozen cut.
Witness: clearing notices preserves completion refs, publications, and every causal
snapshot. The frozen closure theorem therefore applies without seeing a later failure.
-/
theorem healthy_completed_accounted_noticeCarrier {work} {w : Witness} {index event ref}
    (groups : GroupSuccessesAccounted work w) (streams : StreamSuccessAdmission work w)
    (failures : FailureAdmission work w) (selected : w.events[index]? = some event)
    (closed : ref ∈ completedRefs (w.events.take index ++ [withoutChildNotices event]))
    (healthy
      : ¬NodeFailed work w.matching
          (w.events.take index ++ [withoutChildNotices event])
          (w.failures.filter (fun entry => entry.1 ≤ index)) ref)
    : NodeAccounted work w.matching (w.events.take index ++ [withoutChildNotices event])
        (w.failures.filter (fun entry => entry.1 ≤ index)) ref := by
  have projection := withoutChildNotices_projections event
  have causal := causality_carrier_eq (work := work) (matching := w.matching)
    (events := w.events.take index)
    (failures := w.failures.filter (fun entry => entry.1 ≤ index)) projection.1
  have closedAt : ref ∈ completedRefs (w.events.take (index + 1)) := by
    simpa only [List.take_add_one, selected, Option.toList_some, completedRefs,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      projection.2.2]
      using closed
  have healthyAt : ¬NodeFailed work w.matching (w.events.take (index + 1))
      (w.failures.filter (fun entry => entry.1 ≤ index)) ref := by
    simpa only [List.take_add_one, selected, Option.toList_some, causal.1] using healthy
  have accounted := healthy_completed_accounted_frozen groups streams failures
    (Nat.le_refl _) closedAt healthyAt
  simpa only [List.take_add_one, selected, Option.toList_some, NodeAccounted,
    TaskAccounted, causal.2, published_carrier_eq projection.1]
    using accounted

/-- Actual carried group contents survive the notice-free carrier at its original cut.
Witness: group carriers publish nothing, and exact stream provenance gives an item
occurrence. Neither can consume a retained object membership; cutoff composition keeps
the accepted failure inventory fixed while the visible output prefix grows by one.
-/
theorem groupNotice_contents_atCarrier {work inputs} {w : Witness} {index event child}
    (ready : StreamPublicationReady work w)
    (contents
      : RetainedNoticeContents work w.matching (w.events.take index)
          (failedBefore w.failures index) inputs child)
    (selected : w.events[index]? = some event)
    (noticed : child.ref ∈ groupNoticeRefs event)
    : RetainedNoticeContents work w.matching
        (w.events.take index ++ [withoutChildNotices event])
        (failedBefore (w.failures.filter (fun entry => entry.1 ≤ index))
          (w.events.take index ++ [withoutChildNotices event]).length) inputs child := by
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  have reached : index ≤ (w.events.take index ++ [withoutChildNotices event]).length := by
    simp only [List.length_append, List.length_singleton, length]
    omega
  rw [failedBefore_frozen_extend _ reached]
  apply contents.append_nonObject
  intro value
  cases event with
  | groupSuccess => cases value
  | streamValues stream values groups streams =>
      obtain ⟨item, producer, _, known, _⟩ := ready index stream values groups streams selected
      rw [length]
      cases identity : w.matching index with
      | item address ordinal => exact ⟨address, ordinal, rfl⟩
      | executionGroup address =>
          rw [identity] at known
          obtain ⟨_, _, _, _, _, _, _, impossible⟩ := known
          cases impossible
  | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases noticed

/-- The frozen notice boundary retains full support and successful-source-item safety.
Witness: restrict the original cuts, replace only the actual carrier's notice lists,
and use frozen-cut causality to retain strict-prefix item safety through that carrier.
This does not assume any new notice is eligible.
-/
theorem noticeCarrier_support_and_itemSafety
    {work} {inputs : List (List GraphEvent)} {w : Witness} {index event plain}
    (support : PublicationSupport work w.matching w.events w.failures)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (selected : w.events[index]? = some event)
    (same : IsValue event ↔ IsValue plain)
    : PublicationSupport work w.matching (w.events.take index ++ [plain])
        (w.failures.filter (fun entry => entry.1 ≤ index))
      ∧ ∀ source ordinal,
          Occurrence.item source ordinal ∈ inputs.flatten.flatMap GraphEvent.successes
          → ¬TaskCancelled work w.matching (w.events.take index ++ [plain])
              (w.failures.filter (fun entry => entry.1 ≤ index))
              (.item source ordinal) := by
  have length : (w.events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  have subset : (w.failures.filter (fun entry => entry.1 ≤ index)).Subset w.failures :=
    fun _ member => (List.mem_filter.mp member).1
  have prior := (support.take (index + 1)).restrict_failures subset
  rw [List.take_add_one, selected, Option.toList_some] at prior
  refine ⟨prior.replace_last same, ?_⟩
  have frozen :=
    causality_append_eq (work := work) (matching := w.matching)
      (events := w.events.take index)
      (failures := w.failures.filter (fun entry => entry.1 ≤ index))
      (by
        intro entry member; simpa only [length]
          using (of_decide_eq_true (List.mem_filter.mp member).2)) [plain]
  intro source ordinal succeeded cancelled
  rw [frozen.2] at cancelled
  exact safe.prefix (List.prefix_refl _) index subset source ordinal
    succeeded cancelled

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
