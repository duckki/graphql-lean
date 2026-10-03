import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReferences

/-! Leading item-carried notices retain contents at their actual integration boundaries. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Locate the item that introduced a notice without assuming unique notice descriptors
-----------------------------------------------------------------------------------------

/-- Accumulated output metadata does not change the queue projection of item preparation.
Witness: induction on the actual item fold; each step's queue depends only on its queue
and input item, not its accumulated notices or values.
-/
theorem streamItemFold_state (items : List StreamItem)
    (acc
      : State
        × List Execution.DeliveryNode
        × List Execution.DeliveryNode
        × List StreamItemValue)
    : (items.foldl streamItemStep acc).1
      = items.foldl State.integrateStreamItem acc.1 := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => exact ih (streamItemStep acc item)

/-- Item preparation splits at the actual first integration.
Witness: projecting the metadata fold gives the ordinary queue-state fold.
-/
theorem State.preparedStreamItems_cons (queue : State) (item : StreamItem)
    (items : List StreamItem)
    : queue.preparedStreamItems (item :: items)
      = (queue.integrateStreamItem item).preparedStreamItems items := by
  unfold State.preparedStreamItems
  rw [streamItemFold_state, streamItemFold_state]
  rfl

/-- Every accumulated group notice comes from a specific actual item-pruning boundary.
Witness: split old versus newly appended notices in the concrete fold. The prefix is
an input-list prefix, not a selected scheduler trace or a deduplicated descriptor list.
-/
theorem State.streamItemFold_noticeOrigin (queue : State) (items : List StreamItem)
    {child} (noticed : child ∈ (items.foldl streamItemStep (queue, [], [], [])).2.1)
    : ∃ before item after,
        items = before ++ item :: after
        ∧ let current := queue.preparedStreamItems before
          child
          ∈ ((current.maybeIntegrateWork item.work).1.pruneEmptyGroups
              (current.maybeIntegrateWork item.work).2.newGroups).2 := by
  have loop (more : List StreamItem)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue)
      (member : child ∈ (more.foldl streamItemStep acc).2.1)
      : child ∈ acc.2.1 ∨ ∃ before item after, more = before ++ item :: after ∧
          let current := acc.1.preparedStreamItems before
          child ∈ ((current.maybeIntegrateWork item.work).1.pruneEmptyGroups
            (current.maybeIntegrateWork item.work).2.newGroups).2 := by
    induction more generalizing acc with
    | nil => exact .inl member
    | cons item rest ih =>
        rcases ih (streamItemStep acc item) member with old | later
        · rcases List.mem_append.mp old with previous | introduced
          · exact .inl previous
          · exact .inr ⟨[], item, rest, rfl, introduced⟩
        · obtain ⟨before, next, after, shape, introduced⟩ := later
          refine .inr ⟨item :: before, next, after, ?_, ?_⟩
          · simp only [List.cons_append, shape]
          · simpa only [State.preparedStreamItems_cons, streamItemStep,
              State.integrateStreamItem] using introduced
  exact (loop items (queue, [], [], []) noticed).resolve_left (by simp)

-----------------------------------------------------------------------------------------
-- Source validity and the common replay ledger supply the contents and exclusion facts
-----------------------------------------------------------------------------------------

/-- An indexed item-value carrier is the leading event and copies the accumulated notices.
Witness: an inactive handler emits nothing; a ready drain cannot emit a stream-value
event. No uniqueness assumption on the notices or their payloads is used.
-/
theorem State.streamItems_noticeGroups (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) {index : Nat} {emitted values groups streams}
    (selected
      : (queue.streamItems stream items).2[index]?
        = some (.streamValues emitted values groups streams))
    : queue.rootStreams.contains stream.ref = true
      ∧ index = 0
      ∧ groups = (items.foldl streamItemStep (queue, [], [], [])).2.1 := by
  rw [queue.streamItems_eq stream items] at selected
  cases active : queue.rootStreams.contains stream.ref with
  | false =>
      simp only [active, Bool.not_false, ↓reduceIte, List.getElem?_nil,
        reduceCtorEq] at selected
  | true =>
      simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at selected
      cases index with
      | zero =>
          cases selected
          exact ⟨rfl, rfl, rfl⟩
      | succ index =>
          exact False.elim ((queue.preparedStreamItems items).drainReadyGroups_noStreamValues
            emitted values groups streams (List.mem_of_getElem? selected))

/-- A leading item notice has retained contents excluding all earlier object publications.
Witness: recover its actual item-pruning boundary, derive metadata for that input prefix,
and preserve earlier publication exclusions through fresh child integration. No object
output occurs during preparation, so every item's boundary uses the same strict ledger
prefix. No notice-admission or caller-supplied state invariant is assumed.
-/
theorem ExecutedWork.streamItems_leadingNoticeContents
    {work before stream items after published child}
    (generated : ExecutedWork work)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ .streamItems stream items :: after) published)
    (valid : ValidGraphEvents work (before ++ .streamItems stream items :: after))
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      child ∈ (items.foldl streamItemStep (current, [], [], [])).2.1
      → ∃ earlier item later,
          items = earlier ++ item :: later
          ∧ let boundary := (current.preparedStreamItems earlier).integrateStreamItem item
            (∃ dependencies producer, NodeAt work child .group dependencies producer)
            ∧ ∃ node,
                boundary.groupNode? child.ref = some node
                ∧ node.group.node = child
                ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
                ∧ ∀ publication ∈
                    published.take
                      (((State.initialize (Work.fromExecution work)).rawEventReplay
                          before).2.flatMap
                        WorkQueueEvent.objectValues).length,
                    publication.1 ∉ node.tasks := by
  intro current noticed
  obtain ⟨earlier, item, later, splitItems, introduced⟩ :=
    current.streamItemFold_noticeOrigin items noticed
  have included : earlier.Subset items := by
    rw [splitItems]
    exact List.subset_append_left _ _
  have itemMember : item ∈ items := by simp [splitItems]
  have prior := valid.prefix (List.prefix_append before (.streamItems stream items :: after))
  obtain ⟨matching, _, _⟩ := valid.atPrefix (show
    (before ++ [GraphEvent.streamItems stream items]).IsPrefix
      (before ++ GraphEvent.streamItems stream items :: after) from ⟨after, by simp⟩)
  have partialMatching : (GraphEvent.streamItems stream earlier).MatchesWork work :=
    fun entry member => matching entry (included member)
  obtain ⟨refs, records, support⟩ := generated.streamItems_prepared_noticeMetadata
    (fun _ member => prior.eachMatches member) partialMatching
  obtain ⟨located, node, found, same, contents⟩ :=
    State.integrateStreamItem_noticeContents generated refs records support matching
      itemMember introduced
  refine ⟨earlier, item, later, splitItems, located, node, found, same, contents, ?_⟩
  intro publication member
  obtain ⟨absent, fresh⟩ :=
    createWorkQueue_beforeHandlerMemberships covered valid publication member
  have prepared := absent.preparedStreamItems earlier (by
    intro entry entryMember task taskMember
    exact fresh task (List.mem_flatMap.mpr ⟨entry, included entryMember, taskMember⟩))
  have integrated := prepared.maybeIntegrateWork item.work (by
    intro task taskMember
    exact fresh task (List.mem_flatMap.mpr ⟨item, itemMember, taskMember⟩))
  exact ((integrated.pruneEmptyGroups _).startNewWork _) node
    (List.mem_of_find?_eq_some found)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
