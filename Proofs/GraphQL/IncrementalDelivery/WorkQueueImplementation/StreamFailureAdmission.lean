import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureErrors

/-! Stream failure completions satisfy the event rule under output-aligned cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The failed item supplies the causal failure at its completion's exact output cut
-----------------------------------------------------------------------------------------

/-- A stream failure's candidate cut fails its owner before the closing event.
Witness: the exact failing item contributes to this stream, and its cut is visible at
the event's prefix. No already-admitted history or failure licensing is assumed.
-/
theorem StreamFailureCuts.nodeFailed {work events failures index stream errors matching}
    (cuts : StreamFailureCuts work events failures)
    (atEvent : events[index]? = some (.streamFailure stream errors))
    : NodeFailed work matching (events.take index) failures stream.key := by
  obtain ⟨occurrence, member⟩ := cuts.covers atEvent
  obtain ⟨node, count, producer, selected, task⟩ := cuts.2 _ member
  obtain ⟨sameNode, sameCount⟩ :=
    Execution.WorkQueueEvent.streamFailure.inj (Option.some.inj (selected.symm.trans atEvent))
  subst node count
  have length : (events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp atEvent).1)
  exact NodeFailed.task task List.mem_cons_self
    (length.symm ▸ mem_failedBefore member (Nat.le_refl index))

/-- A stream failure completion satisfies every clause of EventAllowed.
Witness: its exact item gives stream metadata and causal failure, closure order gives
the exact error sum, and the caller supplies the independently proved open reference.
This is local admission; licensing the entire failure-cut list remains separate.
-/
theorem StreamFailureCuts.eventAllowed
    {work events failures index stream errors initial matching}
    (cuts : StreamFailureCuts work events failures)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (atEvent : events[index]? = some (.streamFailure stream errors))
    (opened : Open initial (events.take index) stream.key)
    : EventAllowed work initial matching (events.take index) failures
        (.streamFailure stream errors) := by
  obtain ⟨occurrence, member⟩ := cuts.covers atEvent
  obtain ⟨node, count, producer, selected, task⟩ := cuts.2 _ member
  obtain ⟨sameNode, sameCount⟩ :=
    Execution.WorkQueueEvent.streamFailure.inj (Option.some.inj (selected.symm.trans atEvent))
  subst node count
  obtain ⟨dependencies, known⟩ := (itemTask_owner_nodeAt task).2
  have length : (events.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp atEvent).1)
  simp only [EventAllowed]
  rw [nodeFailed_filter (Nat.le_refl _), failedBefore_filter _ (Nat.le_refl _), length]
  exact ⟨⟨dependencies, producer, known⟩, opened, cuts.nodeFailed atEvent,
    cuts.nodeErrors ordered atEvent⟩

-----------------------------------------------------------------------------------------
-- Actual normalized output supplies openness and closure order without admission premises
-----------------------------------------------------------------------------------------

/-- Every actual stream failure obeys the unchanged event rule for its candidate cuts.
Witness: generated metadata and source order establish Open independently; the local
cut theorem supplies causal failure and exact errors under the same supplied matching.
Object failure cuts and full FailureWitness licensing are not asserted here.
-/
theorem createWorkQueue_runNormalized_streamFailure_eventAllowed {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) (matching : PublicationMatching)
    {failures : FailureCuts}
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) failures)
    {index stream errors}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.streamFailure stream errors))
    : EventAllowed work
        (((State.initialize (Work.fromExecution work)).initialGroups
          ++ (State.initialize (Work.fromExecution work)).initialStreams).map
          Execution.DeliveryNode.key) matching
        ((((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms).take
          index) failures (.streamFailure stream errors) := by
  apply cuts.eventAllowed
    (createWorkQueue_runNormalized_atomicStreamActions_ordered valid) atEvent
  exact createWorkQueue_runNormalized_streamOpenAt generated valid atEvent
    (by simp [streamReferenceKeys])

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
