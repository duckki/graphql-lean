import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingCounts

/-! First-match task lookups under computation-record replacement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Replacing another occurrence preserves the existing first-match task lookup.
Witness: map/find induction; the replacement still has the distinct updated occurrence.
No task-map uniqueness premise is required.
-/
theorem State.putTaskNode_lookup_other {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (updated : TaskNode)
    (different : updated.task.occurrence ≠ occurrence)
    : (queue.putTaskNode updated).taskNode? occurrence = some node := by
  have loop (nodes : List TaskNode)
      (lookup : nodes.find? (fun node => node.task.occurrence == occurrence) = some node)
      : (nodes.map (fun old =>
          if old.task.occurrence == updated.task.occurrence then updated else old)).find?
            (fun node => node.task.occurrence == occurrence) = some node := by
    induction nodes with
    | nil => cases lookup
    | cons head rest ih =>
        by_cases replace : head.task.occurrence = updated.task.occurrence
        · have skip : head.task.occurrence ≠ occurrence := replace ▸ different
          have tail : rest.find? (fun node => node.task.occurrence == occurrence)
              = some node := by
            simpa [List.find?_cons, occurrence_beq_iff_eq, skip] using lookup
          simpa [List.find?_cons, occurrence_beq_iff_eq, replace, different] using ih tail
        · by_cases selected : head.task.occurrence = occurrence
          · simpa [List.find?_cons, occurrence_beq_iff_eq, selected, Ne.symm different]
              using lookup
          · have tail : rest.find? (fun node => node.task.occurrence == occurrence)
                = some node := by
              simpa [List.find?_cons, occurrence_beq_iff_eq, selected] using lookup
            simpa [List.find?_cons, occurrence_beq_iff_eq, replace, selected]
              using ih tail
  exact loop queue.taskNodes found

/-- Replacing a present occurrence makes that exact replacement the first matching node.
Witness: map/find induction; earlier nonmatching nodes remain nonmatching and the first
matching node receives the supplied replacement, regardless of duplicate later entries.
-/
theorem State.putTaskNode_lookup_same {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (updated : TaskNode)
    (same : updated.task.occurrence = occurrence)
    : (queue.putTaskNode updated).taskNode? occurrence = some updated := by
  change (queue.taskNodes.map (fun old =>
    if old.task.occurrence == updated.task.occurrence then updated else old)).find?
      (fun candidate => candidate.task.occurrence == occurrence) = _
  rw [same]
  have loop (nodes : List TaskNode)
      (lookup : nodes.find? (fun candidate => candidate.task.occurrence == occurrence)
        = some node)
      : (nodes.map (fun old =>
          if old.task.occurrence == occurrence then updated else old)).find?
            (fun candidate => candidate.task.occurrence == occurrence) = some updated := by
    induction nodes with
    | nil => cases lookup
    | cons head rest ih =>
        by_cases selected : (head.task.occurrence == occurrence) = true
        · simp [selected, same, (occurrence_beq_iff_eq occurrence occurrence).mpr rfl]
        · have tail : rest.find? (fun candidate => candidate.task.occurrence == occurrence)
              = some node := by simpa [List.find?_cons, selected] using lookup
          simpa [List.find?_cons, selected] using ih tail
  exact loop queue.taskNodes found

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
