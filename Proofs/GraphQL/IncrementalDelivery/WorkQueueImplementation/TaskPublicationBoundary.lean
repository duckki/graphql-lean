import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainClosureBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyPending

/-! Separate already-active owner-fold publications from later ready-drain publications. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The single-pass owner fold does not activate its released children
-----------------------------------------------------------------------------------------

/-- Every value block in the owner fold belongs to a group active before that fold.
Witness: each flush is guarded by root membership; roots only shrink until the caller
activates the accumulated child work. No generated-work or source premise is needed.
-/
theorem State.successGroupFold_values_active (queue : State)
    (groups : List Execution.DeliveryNode) {group values}
    (emitted
      : Execution.WorkQueueEvent.groupValues group values
        ∈ (groups.foldl successGroupStep (queue, [], {})).2.1)
    : group.key ∈ queue.rootGroups := by
  have loop (remaining : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (roots : acc.1.rootGroups.Subset queue.rootGroups)
      (prior : ∀ owner payload,
        Execution.WorkQueueEvent.groupValues owner payload ∈ acc.2.1 → owner.key ∈ queue.rootGroups)
      : ∀ owner payload,
        Execution.WorkQueueEvent.groupValues owner payload
            ∈ (remaining.foldl successGroupStep acc).2.1
          → owner.key ∈ queue.rootGroups := by
    induction remaining generalizing acc with
    | nil => exact prior
    | cons next rest ih =>
        rw [List.foldl_cons]
        dsimp only [successGroupStep]
        split
        · exact ih _ roots prior
        · rename_i node found
          split
          · rename_i ready
            have active : node.group.node.key ∈ acc.1.rootGroups := by
              simp only [Bool.and_eq_true, List.contains_iff_mem] at ready
              exact acc.1.groupNode?_key found ▸ ready.1.1
            let updated := { node with pending := node.pending - 1 }
            have remainingRoots
                : ((acc.1.putGroupNode updated).finishGroupSuccess updated).1.rootGroups.Subset
                    queue.rootGroups :=
              (State.finishGroupSuccess_rootsSubset _ _).trans roots
            let flushed := (acc.1.putGroupNode updated).finishGroupSuccess updated
            refine ih (flushed.1, acc.2.1 ++ flushed.2.1,
              ⟨acc.2.2.newGroups ++ flushed.2.2.newGroups,
                acc.2.2.newStreams ++ flushed.2.2.newStreams⟩) remainingRoots ?_
            intro owner payload member
            rcases List.mem_append.mp member with earlier | current
            · exact prior owner payload earlier
            · obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp current
              have same := (State.finishGroupSuccess_value_index _ _ selected).2
              exact same ▸ roots active
          · exact ih _ roots prior
  exact loop groups (queue, [], {}) (List.Subset.refl _)
    (fun _ _ member => False.elim (List.not_mem_nil member)) group values emitted

-----------------------------------------------------------------------------------------
-- An initially inactive group's value must be in the handler's recursive drain
-----------------------------------------------------------------------------------------

/-- An inactive group's task-success publication has an exact later-drain boundary.
Witness: a missing or rejected task produces no value; the guarded owner fold can only
publish initially active groups. Indexed append decomposition identifies the drain block
and preserves its complete strict output prefix, including earlier owner-fold output.
-/
theorem State.taskSuccess_inactiveValue_drain (queue : State)
    (occurrence : Occurrence) (result : TaskResult) {position group values}
    (selected
      : (queue.taskSuccess occurrence result).2[position]?
        = some (.groupValues group values))
    (inactive : group.key ∉ queue.rootGroups)
    : ∃ incoming,
        queue.taskNode? occurrence = some incoming
        ∧ queue.taskHasHealthyOwner incoming.task = true
        ∧ let prepared :=
            ((queue.putTaskNode
                { incoming with value := some result.value }).maybeIntegrateWork
              result.work (some occurrence)).1
          let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
          let activated := released.1.startNewWork released.2.2
          ∃ index,
            activated.drainReadyGroups.2[index]? = some (.groupValues group values)
            ∧ (queue.taskSuccess occurrence result).2.take position
              = released.2.1 ++ activated.drainReadyGroups.2.take index := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found] at selected
  | some incoming =>
      rw [queue.taskSuccess_eq occurrence result incoming found] at selected
      cases healthy : queue.taskHasHealthyOwner incoming.task with
      | false => simp [healthy] at selected
      | true =>
          simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at selected
          let prepared :=
            ((queue.putTaskNode { incoming with value := some result.value }).maybeIntegrateWork
              result.work (some occurrence)).1
          let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
          let activated := released.1.startNewWork released.2.2
          change (released.2.1 ++ activated.drainReadyGroups.2)[position]? = _ at selected
          have bound : released.2.1.length ≤ position := by
            by_cases bound : released.2.1.length ≤ position
            · exact bound
            exfalso
            have first : released.2.1[position]? = some (.groupValues group values) := by
              simpa only
                [List.getElem?_append_left (by omega : position < released.2.1.length)]
                using selected
            have active := prepared.successGroupFold_values_active incoming.task.groups
              (List.mem_of_getElem? first)
            apply inactive
            simpa only [prepared, State.maybeIntegrateWork_rootGroups, State.putTaskNode]
              using active
          refine ⟨incoming, rfl, healthy, position - released.2.1.length, ?_, ?_⟩
          · simpa only [List.getElem?_append_right bound] using selected
          · rw [queue.taskSuccess_eq occurrence result incoming found]
            simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            change (released.2.1 ++ activated.drainReadyGroups.2).take position = _
            rw [List.take_append, List.take_of_length_le bound]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
