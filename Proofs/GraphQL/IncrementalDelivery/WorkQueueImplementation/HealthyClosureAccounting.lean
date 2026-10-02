import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventAccounting

/-! Healthy completed dependencies inherit accounting without assuming carried notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A healthy completed key is task-accounted at every prefix of the common witness.
Witness: locate its completion. Successful group and stream certificates supply earlier
accounting, which survives the intervening outputs; an admitted failure completion would
contradict present health. Carried-notice admission and terminal accounting are not used.
-/
theorem healthy_completed_accounted {work w count key}
    (groups : GroupSuccessesAccounted work w)
    (streams : StreamSuccessAdmission work w) (failures : FailureAdmission work w)
    (closed : key ∈ completedKeys (w.events.take count))
    (healthy : ¬NodeFailed work w.matching (w.events.take count) w.failures key)
    : NodeAccounted work w.matching (w.events.take count) w.failures key := by
  obtain ⟨event, member, closes⟩ := List.mem_flatMap.mp closed
  obtain ⟨index, atPrefix⟩ := List.mem_iff_getElem?.mp member
  have within : index < count := by
    have bound := (List.getElem?_eq_some_iff.mp atPrefix).1
    simp only [List.length_take] at bound
    omega
  have selected : w.events[index]? = some event := by
    rwa [List.getElem?_take_of_lt within] at atPrefix
  have earlier : (w.events.take count).take index = w.events.take index := by
    simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt within)]
  have extendAccounted
      (prior : NodeAccounted work w.matching (w.events.take index) w.failures key)
      : NodeAccounted work w.matching (w.events.take count) w.failures key := by
    have extended := prior.append ((w.events.take count).drop index)
    rwa [← earlier, List.take_append_drop] at extended
  have extendFailure
      (prior : NodeFailed work w.matching (w.events.take index) w.failures key)
      : NodeFailed work w.matching (w.events.take count) w.failures key := by
    have extended := prior.append ((w.events.take count).drop index)
    rwa [← earlier, List.take_append_drop] at extended
  cases event with
  | groupValues | streamValues | workQueueTermination => cases closes
  | groupSuccess group children streamChildren =>
      have same := List.mem_singleton.mp closes
      exact extendAccounted (same ▸ groups index group children streamChildren selected)
  | streamSuccess stream =>
      have same := List.mem_singleton.mp closes
      have admitted := streams index stream selected
      have accounted := (nodeAccounted_filter (Nat.le_refl _)).mp admitted.2.2.2
      exact extendAccounted (same ▸ accounted)
  | groupFailure group errors =>
      have same := List.mem_singleton.mp closes
      have admitted := failures.1 index group errors selected
      have failed := admitted.2.2.1
      rw [nodeFailed_filter (Nat.le_refl _)] at failed
      exact False.elim (healthy (extendFailure (same ▸ failed)))
  | streamFailure stream errors =>
      have same := List.mem_singleton.mp closes
      have admitted := failures.2 index stream errors selected
      have failed := admitted.2.2.1
      rw [nodeFailed_filter (Nat.le_refl _)] at failed
      exact False.elim (healthy (extendFailure (same ▸ failed)))

/-- Healthy completed keys remain accounted when failures are frozen at the carrier's start.
Witness: each earlier completion uses only cuts through its own strict prefix, all within
the supplied bound. Its accounting extends with those same cuts; an earlier failure
completion contradicts health. Failures recorded after the carrier are never imported.
-/
theorem healthy_completed_accounted_frozen {work w count bound key}
    (groups : GroupSuccessesAccounted work w)
    (streams : StreamSuccessAdmission work w) (failures : FailureAdmission work w)
    (within : count ≤ bound + 1)
    (closed : key ∈ completedKeys (w.events.take count))
    (healthy
      : ¬NodeFailed work w.matching (w.events.take count)
          (w.failures.filter (fun entry => entry.1 ≤ bound)) key)
    : NodeAccounted work w.matching (w.events.take count)
        (w.failures.filter (fun entry => entry.1 ≤ bound)) key := by
  obtain ⟨event, member, closes⟩ := List.mem_flatMap.mp closed
  obtain ⟨index, atPrefix⟩ := List.mem_iff_getElem?.mp member
  have earlierIndex : index < count := by
    have size := (List.getElem?_eq_some_iff.mp atPrefix).1
    simp only [List.length_take] at size
    omega
  have reached : (w.events.take index).length ≤ bound := by
    simp only [List.length_take]
    omega
  have selected : w.events[index]? = some event := by
    rwa [List.getElem?_take_of_lt earlierIndex] at atPrefix
  have earlier : (w.events.take count).take index = w.events.take index := by
    simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt earlierIndex)]
  have extendAccounted
      (prior : NodeAccounted work w.matching (w.events.take index) w.failures key)
      : NodeAccounted work w.matching (w.events.take count)
          (w.failures.filter (fun entry => entry.1 ≤ bound)) key := by
    have frozen := (nodeAccounted_filter reached).mpr prior
    have extended := frozen.append ((w.events.take count).drop index)
    rwa [← earlier, List.take_append_drop] at extended
  have excludeFailure
      (prior : NodeFailed work w.matching (w.events.take index) w.failures key) : False := by
    have frozen : NodeFailed work w.matching (w.events.take index)
        (w.failures.filter (fun entry => entry.1 ≤ bound)) key := by
      rwa [nodeFailed_filter reached]
    have extended := frozen.append ((w.events.take count).drop index)
    rw [← earlier, List.take_append_drop] at extended
    exact healthy extended
  cases event with
  | groupValues | streamValues | workQueueTermination => cases closes
  | groupSuccess group children streamChildren =>
      have same := List.mem_singleton.mp closes
      exact extendAccounted (same ▸ groups index group children streamChildren selected)
  | streamSuccess stream =>
      have same := List.mem_singleton.mp closes
      have admitted := streams index stream selected
      exact extendAccounted (same ▸ (nodeAccounted_filter (Nat.le_refl _)).mp admitted.2.2.2)
  | groupFailure group errors =>
      have same := List.mem_singleton.mp closes
      have failed := (failures.1 index group errors selected).2.2.1
      rw [nodeFailed_filter (Nat.le_refl _)] at failed
      exact False.elim (excludeFailure (same ▸ failed))
  | streamFailure stream errors =>
      have same := List.mem_singleton.mp closes
      have failed := (failures.2 index stream errors selected).2.2.1
      rw [nodeFailed_filter (Nat.le_refl _)] at failed
      exact False.elim (excludeFailure (same ▸ failed))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
