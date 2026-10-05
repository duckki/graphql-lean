import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SettlementAvailability

/-! Classify contributors that closed before a later accepted shared settlement.
Earlier failed closure need not count the later failure, and may have a zero count.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- A later settlement cannot consume work accounted for at an earlier boundary
-----------------------------------------------------------------------------------------

/-- A task with an accepted failure cannot already be accounted for strictly before its cut.
Witness: its failed payload excludes earlier publication. Ordered cuts identify historical
cancellation with cancellation by licensing predecessors, which the accepted settlement
excludes. Equal cuts deliberately require a different ordered-predecessor argument.
-/
theorem Explains.recorded_task_unaccounted_before_cut
    {work groups streams events matching failures cut occurrence index}
    (explained : Explains work groups streams events matching failures)
    (recorded : (cut, occurrence) ∈ failures)
    (earlier : index < cut)
    : ¬TaskAccounted work matching (events.take index) failures occurrence := by
  intro accounted
  obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp recorded
  rw [equal] at explained accounted
  have licensed := explained.2.1 before cut occurrence after rfl
  rcases accounted with cancelled | published
  · have visible := explained.2.1.filter_before_settlement
      (index := (events.take index).length) (by simp only [List.length_take]; omega)
    have retained : TaskCancelled work matching (events.take index)
        (before.filter (fun entry => entry.1 ≤ (events.take index).length)) occurrence := by
      rw [← visible]
      simpa only [taskCancelled_filter (Nat.le_refl _)] using cancelled
    have past : TaskCancelled work matching (events.take index) before occurrence := by
      simpa only [taskCancelled_filter (Nat.le_refl _)] using retained
    apply licensed.2.2.2
    have reached : index ≤ cut := Nat.le_of_lt earlier
    have extension := past.append ((events.take cut).drop index)
    have first : (events.take cut).take index = events.take index := by
      rw [List.take_take, Nat.min_eq_left reached]
    rwa [← first, List.take_append_drop] at extension
  · apply explained.failed_unpublished (occurrence := occurrence)
      (mem_failedBefore (occurrence := occurrence) (by simp) (Nat.le_refl cut))
    simpa only [List.take_append_drop] using published.append (events.drop index)

/-- A healthy accounted ref cannot acquire a directly recorded contributor failure later.
Witness: an already-reached cut contradicts health; a later cut contradicts prior accounting
of that same contributor. Dependency failure is intentionally not excluded by this lemma.
-/
theorem Explains.healthy_accounted_no_recorded_failure
    {work groups streams events matching failures index ref}
    (explained : Explains work groups streams events matching failures)
    (healthy : ¬NodeFailed work matching (events.take index) failures ref)
    (accounted : NodeAccounted work matching (events.take index) failures ref)
    : ¬HasRecordedFailure work failures events.length ref := by
  intro recorded
  obtain ⟨occurrence, owners, settled, ⟨producer, payload, known⟩, member⟩ := recorded
  obtain ⟨entry, included, same⟩ := List.mem_map.mp settled
  have inCuts := (List.mem_filter.mp included).1
  have actual : (entry.1, occurrence) ∈ failures := by simpa only [← same] using inCuts
  by_cases reached : entry.1 ≤ (events.take index).length
  · exact healthy (NodeFailed.task known member (mem_failedBefore actual reached))
  · have later : index < entry.1 := by
      have bounded := explained.2.1.cut_le actual
      simp only [List.length_take] at reached
      omega
    exact explained.recorded_task_unaccounted_before_cut actual later
      (accounted occurrence owners ⟨producer, payload, known⟩ member)

-----------------------------------------------------------------------------------------
-- Successful closure cannot precede a contributor's accepted failure
-----------------------------------------------------------------------------------------

/-- A contributor closed before an accepted failure has an actual earlier failure closure.
Witness: settlement licensing excludes earlier cancellation, while the fixed failed payload
excludes publication. A success closure would account for that task and contradict one of
those facts. The earlier failure count is not asserted positive or charged for later work.
-/
theorem Explains.contributor_closed_before_settlement_failed
    {work groups streams events matching failures cut occurrence owners producer payload
      ref}
    (explained : Explains work groups streams events matching failures)
    (recorded : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence owners producer payload)
    (contributes : ref ∈ owners)
    (closed : ref ∈ completedRefs (events.take cut))
    : ∃ index node errors,
        index < cut
        ∧ node.ref = ref
        ∧ (events[index]? = some (.groupFailure node errors)
            ∨ events[index]? = some (.streamFailure node errors)) := by
  obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp recorded
  rw [equal] at explained
  have licensed := explained.2.1 before cut occurrence after rfl
  have earlier := explained.before_settlement
  have unpublished : ¬Published matching (events.take cut) occurrence := by
    intro published
    apply explained.failed_unpublished (occurrence := occurrence)
      (mem_failedBefore (occurrence := occurrence) (by simp) (Nat.le_refl cut))
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  have unaccounted
      (accounted : NodeAccounted work matching (events.take cut) before ref) : False := by
    exact licensed.2.2.2
      ((accounted occurrence owners ⟨producer, payload, known⟩ contributes).resolve_right
        unpublished)
  obtain ⟨event, member, closes⟩ := List.mem_flatMap.mp closed
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have beforeCut : index < cut := by simp only [List.length_take] at bound; omega
  have original : events[index]? = some event := by
    simpa only [List.getElem?_take_of_lt beforeCut] using selected
  have allowed := earlier.2.2 index event selected
  cases event <;>
    simp only [eventCompleted, List.mem_singleton, List.not_mem_nil] at closes
  all_goals try contradiction
  all_goals subst ref
  all_goals simp only [EventAllowed, NodeAccounted, TaskAccounted,
    nodeFailed_filter (Nat.le_refl _), taskCancelled_filter (Nat.le_refl _)] at allowed
  case groupSuccess node newGroups newStreams =>
    exact False.elim (unaccounted (fun task taskOwners descriptor member =>
      TaskAccounted.take_prefix (allowed.2.2.2.1 task taskOwners descriptor member)
        (Nat.le_of_lt bound)))
  case streamSuccess node =>
    exact False.elim (unaccounted (fun task taskOwners descriptor member =>
      TaskAccounted.take_prefix (allowed.2.2.2 task taskOwners descriptor member)
        (Nat.le_of_lt bound)))
  case groupFailure node errors =>
    exact ⟨index, node, errors, beforeCut, rfl, Or.inl original⟩
  case streamFailure node errors =>
    exact ⟨index, node, errors, beforeCut, rfl, Or.inr original⟩

end GraphQL.IncrementalDelivery.WorkQueueSemantics
