import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OutputShape

/-! Every raw object publication is immediately followed by its triggering group's closure. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- An output-shape witness, not a scheduler or event-source premise
-----------------------------------------------------------------------------------------

/-- Classify only raw object publications; stream publications do not close their stream. -/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.IsGroupValue
    : WorkQueueEvent → Prop
  | .groupValues .. => True
  | _ => False

/-- A raw output list consists of individual non-object events and publication/closure
pairs. The witness remembers the raw triggering group, before publisher ID remapping.
-/
inductive GroupPublicationPairs : List WorkQueueEvent → Prop
  | nil : GroupPublicationPairs []
  | control (event : WorkQueueEvent) {rest}
    (nonvalue : ¬event.IsGroupValue) (later : GroupPublicationPairs rest)
    : GroupPublicationPairs (event :: rest)
  | publication (group : Execution.DeliveryNode) (values : List ExecutionGroupValue)
    (groups streams : List Execution.DeliveryNode) {rest}
    (later : GroupPublicationPairs rest)
    : GroupPublicationPairs
        (.groupValues group values :: .groupSuccess group groups streams :: rest)

/-- Concatenating complete raw output blocks never splits a publication/closure pair.
Witness: induction on the left block's shape derivation.
-/
theorem GroupPublicationPairs.append {left right}
    (first : GroupPublicationPairs left) (later : GroupPublicationPairs right)
    : GroupPublicationPairs (left ++ right) := by
  induction first with
  | nil => exact later
  | control event nonvalue _ ih => exact .control event nonvalue ih
  | publication group values groups streams _ ih =>
      exact .publication group values groups streams ih

/-- Every indexed raw object publication has its own successful closure at the next index.
Witness: invert control positions and the adjacent publication/closure constructors.
-/
theorem GroupPublicationPairs.next {events index group values}
    (pairs : GroupPublicationPairs events)
    (selected : events[index]? = some (.groupValues group values))
    : ∃ groups streams,
        events[index + 1]? = some (.groupSuccess group groups streams) := by
  induction pairs generalizing index with
  | nil => simp at selected
  | control event nonvalue later ih =>
      cases index with
      | zero => cases selected; exact False.elim (nonvalue trivial)
      | succ index => exact ih selected
  | publication owner payload groups streams later ih =>
      cases index with
      | zero => cases selected; exact ⟨groups, streams, rfl⟩
      | succ index =>
          cases index with
          | zero => cases selected
          | succ index => exact ih selected

-----------------------------------------------------------------------------------------
-- Flushes, recursive drains, and every source handler construct complete pairs
-----------------------------------------------------------------------------------------

/-- A successful group flush emits either its closure alone or its value/closure pair.
Witness: the exact selected-task output equation; no queue invariant is required.
-/
theorem State.finishGroupSuccess_publicationPairs (queue : State) (group : GroupNode)
    : GroupPublicationPairs (queue.finishGroupSuccess group).2.1 := by
  obtain ⟨selected, _, _, outputs, _, _⟩ := queue.finishGroupSuccess_publications group
  rw [outputs]
  split
  · exact .control _ (by simp [WorkQueueEvent.IsGroupValue]) .nil
  · exact .publication _ _ _ _ .nil

/-- Recursive draining preserves paired publications through successes and cached failures.
Witness: successful flushes supply pairs; failed closures are single control events.
-/
theorem State.drainReadyGroups_publicationPairs (queue : State)
    : GroupPublicationPairs queue.drainReadyGroups.2 := by
  have loop (fuel : Nat) (current : State)
      : GroupPublicationPairs (State.drainReadyGroups.go fuel current).2 := by
    induction fuel generalizing current with
    | zero => exact .nil
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact .nil
        · rename_i node selected
          cases cached : node.failure with
          | none => exact (current.finishGroupSuccess_publicationPairs node).append (ih _)
          | some errors =>
              exact (GroupPublicationPairs.control _ (by simp [State.finishGroupFailure,
                WorkQueueEvent.IsGroupValue]) .nil).append (ih _)
  exact loop _ queue

/-- A successful settlement emits whole pairs through the single-pass fold and final drain.
Witness: each fold flush and the recursive release drain preserve the same shape.
-/
theorem State.taskSuccess_publicationPairs (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : GroupPublicationPairs (queue.taskSuccess occurrence result).2 := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (prior : GroupPublicationPairs acc.2.1)
      : GroupPublicationPairs (groups.foldl successGroupStep acc).2.1 := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        dsimp only [successGroupStep]
        split
        · exact prior
        · split
          · exact prior.append (State.finishGroupSuccess_publicationPairs _ _)
          · exact prior
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskSuccess, found] using GroupPublicationPairs.nil
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact .nil
      · exact (loop _ (_, [], {}) .nil).append (State.drainReadyGroups_publicationPairs _)

/-- Task failure contributes only control events and cannot leave an unmatched publication.
Witness: the actual failure fold either retains output or appends a failed-group closure.
-/
theorem State.taskFailure_publicationPairs (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : GroupPublicationPairs (queue.taskFailure occurrence errors).2 := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : GroupPublicationPairs acc.2)
      : GroupPublicationPairs (groups.foldl step acc).2 := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        unfold step
        split
        · exact prior
        · split
          · exact prior.append (.control _ (by simp [State.finishGroupFailure,
              WorkQueueEvent.IsGroupValue]) .nil)
          · exact prior
  unfold State.taskFailure
  split
  · exact .nil
  · split
    · exact .nil
    · exact loop _ (_, []) .nil

/-- An item batch precedes a release drain whose object publications all have closures.
Witness: its leading stream event is not an object publication; reuse the drain theorem.
-/
theorem State.streamItems_publicationPairs (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : GroupPublicationPairs (queue.streamItems stream items).2 := by
  unfold State.streamItems
  split
  · exact .nil
  · exact .control _ (by simp [WorkQueueEvent.IsGroupValue])
      (State.drainReadyGroups_publicationPairs _)

/-- Every source handler returns complete publication/closure pairs.
Witness: the three publication-capable handlers above; stream closures are controls.
-/
theorem State.handleGraphEvent_publicationPairs (queue : State) (event : GraphEvent)
    : GroupPublicationPairs (queue.handleGraphEvent event).2 := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_publicationPairs occurrence result
  | taskFailure occurrence errors =>
      exact queue.taskFailure_publicationPairs occurrence errors
  | streamItems stream items => exact queue.streamItems_publicationPairs stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split
      · exact .control _ (by simp [WorkQueueEvent.IsGroupValue]) .nil
      · exact .nil
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split
      · exact .control _ (by simp [WorkQueueEvent.IsGroupValue]) .nil
      · exact .nil

-----------------------------------------------------------------------------------------
-- Actual replay retains the immediate successful carrier
-----------------------------------------------------------------------------------------

/-- Arbitrary raw source replay preserves publication/closure adjacency.
Witness: append each handler's exact output while threading the real queue state.
-/
theorem State.rawEventReplay_publicationPairs (queue : State) (events : List GraphEvent)
    : GroupPublicationPairs (queue.rawEventReplay events).2 := by
  induction events generalizing queue with
  | nil => exact .nil
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      exact (queue.handleGraphEvent_publicationPairs event).append (ih _)

/-- Batch handling never splits an emitted object's immediate successful carrier.
Witness: the raw replay theorem and the optional trailing termination control.
-/
theorem State.handleGraphEvents_publicationPairs (queue : State)
    (events : List GraphEvent)
    : GroupPublicationPairs (queue.handleGraphEvents events).2 := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact .nil
  · dsimp only
    split
    · exact (queue.rawEventReplay_publicationPairs events).append
        (.control _ (by simp [WorkQueueEvent.IsGroupValue]) .nil)
    · exact queue.rawEventReplay_publicationPairs events

/-- Every actual raw object publication has a same-group successful closure immediately
after it, independently of source validity or generated-work assumptions.
Witness: derive adjacency from the batch handler's output-shape certificate.
-/
theorem State.handleGraphEvents_groupValues_next (queue : State)
    (events : List GraphEvent) {index group values}
    (selected
      : (queue.handleGraphEvents events).2[index]? = some (.groupValues group values))
    : ∃ groups streams,
        (queue.handleGraphEvents events).2[index + 1]?
        = some (.groupSuccess group groups streams) :=
  (queue.handleGraphEvents_publicationPairs events).next selected

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
