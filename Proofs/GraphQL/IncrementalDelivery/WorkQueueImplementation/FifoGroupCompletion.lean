import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemGroupCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingFailureFrames

/-! Announced groups remain active, await an internal failure control, or have completed. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- FIFO completion tracking retains a queued failure until its actual notification output.
Pending controls carry no new announcements and are not counted as emitted completions. -/
def FifoGroupNoticeCompletion (initial : NodeRefs) (result : State × List WorkQueueEvent)
    : Prop :=
  ∀ ref ∈ initial ++ result.2.flatMap rawGroupNoticeRefs,
    ref ∈ result.1.groupNoticeSupport ∨ ref ∈ result.2.flatMap rawGroupClosureRefs

/-- A silent transition retains every tracked ref in its live or pending support. -/
theorem FifoGroupNoticeCompletion.silent {initial queue}
    (included : initial.Subset queue.groupNoticeSupport)
    : FifoGroupNoticeCompletion initial (queue, []) := by
  intro ref member
  exact .inl (included (by simpa using member))

/-- FIFO completion tracking composes using the actual live and pending support. -/
theorem FifoGroupNoticeCompletion.append {initial first second}
    (left : FifoGroupNoticeCompletion initial first)
    (right : FifoGroupNoticeCompletion first.1.groupNoticeSupport second)
    : FifoGroupNoticeCompletion initial (second.1, first.2 ++ second.2) := by
  intro ref member
  have later (member : ref ∈ first.1.groupNoticeSupport ++ second.2.flatMap rawGroupNoticeRefs) :=
    (right ref member).imp_right (List.mem_append_right (first.2.flatMap rawGroupClosureRefs))
  simp only [List.flatMap_append] at member ⊢
  rcases List.mem_append.mp member with old | noticed
  · rcases left ref (List.mem_append_left _ old) with active | closed
    · exact later (List.mem_append_left _ active)
    · exact .inr (List.mem_append_left _ closed)
  · rcases List.mem_append.mp noticed with earlier | next
    · rcases left ref (List.mem_append_right _ earlier) with active | closed
      · exact later (List.mem_append_left _ active)
      · exact .inr (List.mem_append_left _ closed)
    · exact later (List.mem_append_right _ next)

/-- Empty pending state converts FIFO tracking into ordinary emitted completion tracking. -/
theorem FifoGroupNoticeCompletion.completed {initial result}
    (tracked : FifoGroupNoticeCompletion initial result)
    (empty : result.1.groupFailureEvents = [])
    : GroupNoticeCompletion initial result := by
  intro ref member
  rcases tracked ref member with active | closed
  · exact .inl (by simpa [State.groupNoticeSupport, State.pendingGroupFailureRefs, empty]
      using active)
  · exact .inr closed

/-- Failure controls contribute closures but no new group notices. -/
theorem groupFailureEvents_noticeRefs (failures : List GroupFailureEvent)
    : (failures.map
        (fun failure => WorkQueueEvent.groupFailure failure.group failure.errors)).flatMap
        rawGroupNoticeRefs
      = [] := by
  induction failures with
  | nil => rfl
  | cons failure rest ih => exact ih

/-- Enqueue effects retain local removal tracking without emitting a completion early. -/
theorem GroupNoticeCompletion.enqueueGroupFailures {initial queue events}
    (failures : List GroupFailureEvent)
    (tracked
      : GroupNoticeCompletion initial
          (
            queue,
            events
            ++ failures.map (fun failure => .groupFailure failure.group failure.errors)
          ))
    : FifoGroupNoticeCompletion (initial ++ queue.pendingGroupFailureRefs)
        (queue.enqueueGroupFailures failures, events) := by
  intro ref member
  have finish (mentioned : ref ∈ initial ++ events.flatMap rawGroupNoticeRefs)
      : ref ∈ (queue.enqueueGroupFailures failures).groupNoticeSupport
        ∨ ref ∈ events.flatMap rawGroupClosureRefs := by
    have result := tracked ref (by simpa only [List.flatMap_append,
      groupFailureEvents_noticeRefs, List.append_nil] using mentioned)
    rcases result with active | closed
    · exact .inl (List.mem_append_left _ active)
    · rw [List.flatMap_append, failureClosureEvents_refs] at closed
      rcases List.mem_append.mp closed with emitted | waiting
      · exact .inr emitted
      · apply Or.inl
        change ref ∈ queue.rootGroups ++ (queue.groupFailureEvents ++ failures).map _
        rw [List.map_append]
        exact List.mem_append_right _ (List.mem_append_right _ waiting)
  rcases List.mem_append.mp member with prior | noticed
  · rcases List.mem_append.mp prior with original | waiting
    · exact finish (List.mem_append_left _ original)
    · apply Or.inl
      change ref ∈ queue.rootGroups ++ (queue.groupFailureEvents ++ failures).map _
      rw [List.map_append]
      exact List.mem_append_right _ (List.mem_append_left _ waiting)
  · exact finish (List.mem_append_right _ noticed)

/-- Consuming a matching pending head moves that ref from pending support to real output. -/
theorem State.groupFailure_fifoGroupNoticeCompletion (queue : State)
    (supplied : GroupFailureEvent)
    : FifoGroupNoticeCompletion queue.groupNoticeSupport
        (queue.groupFailure supplied) := by
  cases queued : queue.groupFailureEvents with
  | nil =>
      simp only [State.groupFailure, queued]
      exact .silent (List.Subset.refl _)
  | cons first rest =>
      simp only [State.groupFailure, queued]
      split
      · intro ref member
        simp only [State.groupNoticeSupport, State.pendingGroupFailureRefs, queued,
          List.map_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          rawGroupNoticeRefs] at member
        rcases List.mem_append.mp member with root | pending
        · exact .inl (List.mem_append_left _ root)
        · rcases List.mem_cons.mp pending with same | later
          · subst ref
            exact .inr List.mem_cons_self
          · exact .inl (List.mem_append_right _ later)
      · exact .silent (List.Subset.refl _)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
