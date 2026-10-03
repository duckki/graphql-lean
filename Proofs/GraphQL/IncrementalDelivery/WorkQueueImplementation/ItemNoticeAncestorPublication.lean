import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNoticeAncestorPublication

/-! Item handlers preserve ancestor publication before their successful group notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A successful group notice in an item handler is after its object-free leading carrier.
Witness: invert the active-stream branch and the actual output index. Its exact object
prefix and final queue agree with the prepared queue's recursive drain.
-/
theorem State.streamItems_groupNotice_boundary (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    {position group groups streams}
    (selected
      : (queue.streamItems stream items).2[position]?
        = some (.groupSuccess group groups streams))
    : queue.rootStreams.contains stream.ref = true
      ∧ ∃ index,
          (queue.preparedStreamItems items).drainReadyGroups.2[index]?
            = some (.groupSuccess group groups streams)
          ∧ ((queue.streamItems stream items).2.take position).flatMap
              WorkQueueEvent.objectValues
            = ((queue.preparedStreamItems items).drainReadyGroups.2.take index).flatMap
                WorkQueueEvent.objectValues
          ∧ (queue.streamItems stream items).1
            = (queue.preparedStreamItems items).drainReadyGroups.1 := by
  rw [queue.streamItems_eq stream items] at selected ⊢
  cases active : queue.rootStreams.contains stream.ref with
  | false =>
      simp only [active, Bool.not_false, ↓reduceIte, List.getElem?_nil, reduceCtorEq] at selected
  | true =>
      simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      cases position with
      | zero => cases selected
      | succ index => exact ⟨trivial, index, selected, rfl, rfl⟩

-----------------------------------------------------------------------------------------
-- Every structural ancestor contribution precedes its child's group carrier
-----------------------------------------------------------------------------------------

/-- An item handler's group notice has already published each structural ancestor contributor.
Witness: it cannot be the current object-success input, so source accounting supplies prior
publication or a real entry buffer. Actual notice health excludes cancellation; the same
drain-prefix ledger publishes that buffer before the precise successful group carrier.
-/
theorem ExecutedWork.streamItems_groupNoticeAncestor_contributor_before
    {work before stream items published position group groups streams child dependencies
      ref address owners producer payload}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [.streamItems stream items]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch
          (before ++ [.streamItems stream items])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [.streamItems stream items]) published)
    (selected
      : (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).streamItems
          stream items).2[position]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
                WorkQueueEvent.objectValues).length
              + (((((State.initialize (Work.fromExecution work)).replayGraphEvents
                      before).streamItems
                    stream items).2.take
                    position).flatMap
                  WorkQueueEvent.objectValues).length) := by
  let initial := State.initialize (Work.fromExecution work)
  let queue := initial.replayGraphEvents before
  have refNoticed : child.ref ∈ rawGroupNoticeRefs (.groupSuccess group groups streams) :=
    List.mem_map_of_mem noticed
  have emitted := List.mem_of_getElem? selected
  obtain ⟨result, impossible | ⟨_, prior | buffered⟩⟩ :=
    generated.noticeAncestor_contributor_published_buffered_or_current valid started covered
      emitted refNoticed known ancestor task contributes
  · cases impossible
  · exact ⟨result.value, List.take_subset_take_left _ (Nat.le_add_right ..) prior⟩
  · obtain ⟨node, lookup, stored, taskOwners, nodeContributes, present⟩ := buffered
    obtain ⟨active, index, atDrain, prefixEq, finalEq⟩ :=
      queue.streamItems_groupNotice_boundary stream items selected
    have notCancelled := (generated.noticeAncestor_healthy_uncancelled valid
      (State.acceptsBatch_prefix started) emitted refNoticed known ancestor).2
    have endpoint : initial.replayGraphEvents (before ++ [.streamItems stream items])
        = (queue.preparedStreamItems items).drainReadyGroups.1 := by
      rw [State.replayGraphEvents_append]
      exact finalEq
    rw [endpoint] at notCancelled
    have delivered := generated.streamItems_drainNoticeAncestorValue_before
      (fun _ member => (valid.prefix (List.prefix_append before [_])).eachMatches member)
      (valid.eachMatches (List.mem_append_right before List.mem_cons_self)) known ancestor
      taskOwners nodeContributes stored
      (covered.atPrefixDrainOwners before (.streamItems stream items) [])
      active lookup present atDrain noticed notCancelled
    refine ⟨result.value, ?_⟩
    change (Occurrence.executionGroup address, result.value) ∈ published.take
      (((initial.rawEventReplay before).2.flatMap WorkQueueEvent.objectValues).length
        + (((queue.streamItems stream items).2.take position).flatMap
          WorkQueueEvent.objectValues).length)
    rw [prefixEq, List.take_add]
    apply List.mem_append_right
    rw [List.take_take] at delivered
    exact List.take_subset_take_left _ (Nat.min_le_left _ _) delivered

/-- Every actual successful group carrier publishes all contributors of its noticed ancestry.
Witness: the two notice-producing handlers use their exact common-ledger boundaries.
Task failure and stream completion emit no successful group carrier. This is source-to-raw
output accounting; normalized semantic dependency readiness remains a separate bridge.
-/
theorem ExecutedWork.handleGraphEvent_groupNoticeAncestor_contributor_before
    {work before event published position group groups streams child dependencies
      ref address owners producer payload}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [event]) published)
    (selected
      : (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).handleGraphEvent
          event).2[position]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
                WorkQueueEvent.objectValues).length
              + (((((State.initialize (Work.fromExecution work)).replayGraphEvents
                      before).handleGraphEvent
                    event).2.take
                    position).flatMap
                  WorkQueueEvent.objectValues).length) := by
  let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
  cases event with
  | taskSuccess occurrence result =>
      exact generated.taskSuccess_noticeAncestor_contributor_before valid started covered
        selected noticed known ancestor task contributes
  | streamItems stream items =>
      exact generated.streamItems_groupNoticeAncestor_contributor_before valid started covered
        selected noticed known ancestor task contributes
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

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
