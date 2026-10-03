import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCompletionHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes

/-! Announced ancestors complete at the exact notice carrier of actual source handlers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Recover the owner-fold or drain phase without imposing a new queue premise
-----------------------------------------------------------------------------------------

/-- A task-success notice completes each announced ancestor by its actual carrier.
Witness: invert the actual healthy handler, split its indexed owner/drain output, and
use the source-history completion theorem for that phase. Earlier cancellation would
persist to the endpoint, where the caller excludes it.
-/
theorem ExecutedWork.taskSuccess_noticeAncestor_completed
    {work before occurrence result index group groups streams child dependencies ref}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    : let initial := State.initialize (Work.fromExecution work)
      let queue := initial.replayGraphEvents before
      let outputs :=
        (initial.rawEventReplay before).2
        ++ (queue.taskSuccess occurrence result).2.take (index + 1)
      (queue.taskSuccess occurrence result).2[index]?
        = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ref ∉ (queue.taskSuccess occurrence result).1.cancelledGroups
      → ref ∈ initial.rootGroups ++ outputs.flatMap rawGroupNoticeRefs
      → ref ∈ outputs.flatMap rawGroupClosureRefs := by
  intro initial queue outputs selected noticed uncancelled announced
  have priorUncancelled : ref ∉ queue.cancelledGroups :=
    fun member => uncancelled (queue.taskSuccess_cancelledGroups_subset _ _ member)
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found] at selected
  | some incoming =>
      cases healthy : queue.taskHasHealthyOwner incoming.task with
      | false =>
          rw [queue.taskSuccess_eq occurrence result incoming found] at selected
          simp [healthy] at selected
      | true =>
          let prepared := ((queue.putTaskNode
            { incoming with value := some result.value }).maybeIntegrateWork
              result.work (some occurrence)).1
          let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
          let active := folded.1.startNewWork folded.2.2
          have equation : queue.taskSuccess occurrence result
              = (active.drainReadyGroups.1, folded.2.1 ++ active.drainReadyGroups.2) := by
            rw [queue.taskSuccess_eq occurrence result incoming found]
            simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rfl
          dsimp only [outputs] at announced ⊢
          rw [equation] at selected uncancelled announced ⊢
          dsimp only at selected uncancelled announced ⊢
          by_cases inFold : index < folded.2.1.length
          · rw [List.getElem?_append_left inFold] at selected
            rw [List.take_append_of_le_length (by omega : index + 1 ≤ folded.2.1.length)]
              at announced ⊢
            exact generated.ownerNoticeAncestor_completed matching matched known ancestor
              selected noticed priorUncancelled announced
          · have inDrain : folded.2.1.length ≤ index := by omega
            rw [List.getElem?_append_right inDrain] at selected
            rw [List.take_append, List.take_of_length_le (by omega
              : folded.2.1.length ≤ index + 1), ← List.append_assoc] at announced ⊢
            have offset
                : index + 1 - folded.2.1.length = index - folded.2.1.length + 1 := by
              omega
            rw [offset] at announced ⊢
            exact generated.taskDrainNoticeAncestor_completed matching matched known
              ancestor selected noticed uncancelled announced

/-- An item handler's group-success notice completes its announced ancestors by that carrier.
Witness: a group-success output cannot be the leading item carrier; its successor index
selects the exact recursive-drain prefix, including the original leading notice frontier.
-/
theorem ExecutedWork.streamItems_groupNoticeAncestor_completed
    {work before stream items index group groups streams child dependencies ref}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    : let initial := State.initialize (Work.fromExecution work)
      let queue := initial.replayGraphEvents before
      let outputs :=
        (initial.rawEventReplay before).2
        ++ (queue.streamItems stream items).2.take (index + 1)
      (queue.streamItems stream items).2[index]?
        = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ref ∉ (queue.streamItems stream items).1.cancelledGroups
      → ref ∈ initial.rootGroups ++ outputs.flatMap rawGroupNoticeRefs
      → ref ∈ outputs.flatMap rawGroupClosureRefs := by
  intro initial queue outputs selected noticed uncancelled announced
  dsimp only [outputs] at announced ⊢
  rw [queue.streamItems_eq stream items] at selected uncancelled announced ⊢
  cases active : queue.rootStreams.contains stream.ref with
  | false =>
      simp only [active, Bool.not_false, ↓reduceIte, List.getElem?_nil, reduceCtorEq]
        at selected
  | true =>
      simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        at selected uncancelled announced ⊢
      cases index with
      | zero => cases selected
      | succ index =>
          simp only [List.take_succ_cons] at announced ⊢
          have completed := generated.streamDrainNoticeAncestor_completed matching matched
            known ancestor selected noticed uncancelled
          simp only [List.append_assoc, List.singleton_append] at completed
          exact completed announced

-----------------------------------------------------------------------------------------
-- Actual source validity supplies noncancellation, not an assumed semantic output law
-----------------------------------------------------------------------------------------

/-- Each announced ancestor of an actual group notice has completed by that exact carrier.
Witness: source validity derives ancestor health and endpoint noncancellation. Only the
task-success and item handlers can carry group notices, and both preserve the exact cut.
-/
theorem ExecutedWork.handleGraphEvent_groupNoticeAncestor_completed
    {work before event index group groups streams child dependencies ref}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (before ++ [event]))
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch before = true)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    : let initial := State.initialize (Work.fromExecution work)
      let queue := initial.replayGraphEvents before
      let outputs :=
        (initial.rawEventReplay before).2
        ++ (queue.handleGraphEvent event).2.take (index + 1)
      (queue.handleGraphEvent event).2[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ref ∈ initial.rootGroups ++ outputs.flatMap rawGroupNoticeRefs
      → ref ∈ outputs.flatMap rawGroupClosureRefs := by
  intro initial queue outputs selected noticed announced
  have matching : ∀ entry ∈ before, entry.MatchesWork work :=
    fun _ member => (valid.prefix (List.prefix_append before [_])).eachMatches member
  have matched := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
  have uncancelled := (generated.noticeAncestor_healthy_uncancelled valid started
    (List.mem_of_getElem? selected) (List.mem_map_of_mem noticed) known ancestor).2
  rw [State.replayGraphEvents_append] at uncancelled
  cases event with
  | taskSuccess occurrence result =>
      exact generated.taskSuccess_noticeAncestor_completed matching matched known ancestor
        selected noticed uncancelled announced
  | streamItems stream items =>
      exact generated.streamItems_groupNoticeAncestor_completed matching matched known ancestor
        selected noticed uncancelled announced
  | taskFailure occurrence errors =>
      exact False.elim (queue.taskFailure_noGroupSuccess occurrence errors group groups streams
        (List.mem_of_getElem? selected))
  | streamSuccess stream =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamSuccess] at member
      split at member <;> simp at member
  | streamFailure stream errors =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamFailure] at member
      split at member <;> simp at member

-----------------------------------------------------------------------------------------
-- A leading item carrier cannot borrow a closure from its later drain
-----------------------------------------------------------------------------------------

/-- A leading item notice's previously announced ancestor closed before this source input.
Witness: the actual selected item carrier is at index zero and copies the preparation
notices. Source-derived noncancellation propagates back to handler entry, where the
prepared-root completion theorem applies without using any later drain output.
-/
theorem ExecutedWork.handleGraphEvent_itemNoticeAncestor_completed
    {work before event index stream values groups streams child dependencies ref}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (before ++ [event]))
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch before = true)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    : let initial := State.initialize (Work.fromExecution work)
      let queue := initial.replayGraphEvents before
      let outputs :=
        (initial.rawEventReplay before).2 ++ (queue.handleGraphEvent event).2.take index
      (queue.handleGraphEvent event).2[index]?
        = some (.streamValues stream values groups streams)
      → child ∈ groups
      → ref ∈ initial.rootGroups ++ outputs.flatMap rawGroupNoticeRefs
      → ref ∈ outputs.flatMap rawGroupClosureRefs := by
  intro initial queue outputs selected noticed announced
  obtain ⟨owner, items, rfl⟩ := queue.handleGraphEvent_streamValues_source event selected
  obtain ⟨_, rfl, notices⟩ := queue.streamItems_noticeGroups owner items selected
  have uncancelled := (generated.noticeAncestor_healthy_uncancelled valid started
    (List.mem_of_getElem? selected) (List.mem_map_of_mem noticed) known ancestor).2
  rw [State.replayGraphEvents_append] at uncancelled
  have priorUncancelled : ref ∉ queue.cancelledGroups :=
    fun member => uncancelled (queue.streamItems_cancelledGroups_subset _ _ member)
  have matching : ∀ entry ∈ before, entry.MatchesWork work :=
    fun _ member => (valid.prefix (List.prefix_append before [_])).eachMatches member
  have matched := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
  dsimp only [outputs] at announced ⊢
  simp only [List.take_zero, List.append_nil] at announced ⊢
  exact generated.streamPrepared_noticeAncestor_completed matching matched known ancestor
    (notices ▸ noticed) priorUncancelled announced

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
