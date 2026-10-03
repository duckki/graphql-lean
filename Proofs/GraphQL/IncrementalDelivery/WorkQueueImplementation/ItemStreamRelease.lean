import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeMetadata

/-! Item-produced stream notices retain a producer from their own item publication batch. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A stream-item carrier releases only streams supplied by its own items
-----------------------------------------------------------------------------------------

/-- Newly returned stream notices are exact descriptors from the supplied stream list.
Witness: fresh selection only discards candidates; task attachment returns no root notices.
No property of the old stream registry is needed for this output-only fact.
-/
theorem State.addStreams_notices_subset (queue : State) (streams : List Stream)
    (parent : Option Occurrence)
    : (queue.addStreams streams parent).2.Subset (streams.map Stream.node) := by
  have selected := freshStreams_subset queue streams
  unfold State.addStreams
  cases parent with
  | none =>
      intro node member
      obtain ⟨stream, fresh, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨stream, selected fresh, rfl⟩
  | some occurrence =>
      dsimp only
      split <;> exact (by intro node impossible; cases impossible)

/-- Immediate integration returns stream notices only from that input work's streams.
Witness: group/task registration changes the entry state, not the stream candidates.
-/
theorem State.maybeIntegrateWork_notices_subset (queue : State) (work : Work)
    (parent : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parent).2.newStreams.Subset
        (work.streams.map Stream.node) :=
  State.addStreams_notices_subset _ _ _

/-- Every stream noticed by an item handler was supplied by an item in that same input.
Witness: the item loop concatenates exactly each integration's newStreams; their descriptors
come from that item's child work. No source semantics or prior registry premise is used.
-/
theorem State.streamItems_noticeSource (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) {owner values groups streams}
    (emitted
      : Execution.WorkQueueEvent.streamValues owner values groups streams
        ∈ (queue.streamItems stream items).2)
    {child} (noticed : child ∈ streams)
    : ∃ item ∈ items, ∃ entry ∈ item.work.streams, entry.node = child := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 },
      acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams, acc.2.2.2 ++ [item.value])
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      : (more.foldl step acc).2.2.1.Subset
          (acc.2.2.1 ++ more.flatMap (fun item => item.work.streams.map Stream.node)) := by
    induction more generalizing acc with
    | nil => intro node member; exact List.mem_append_left _ member
    | cons item rest ih =>
        intro node member
        have later := ih (step acc item) member
        rcases List.mem_append.mp later with previous | remaining
        · change node ∈ acc.2.2.1 ++ (acc.1.maybeIntegrateWork item.work).2.newStreams
            at previous
          rcases List.mem_append.mp previous with old | new
          · exact List.mem_append_left _ old
          · exact List.mem_append_right _ (List.mem_append_left _
              (acc.1.maybeIntegrateWork_notices_subset item.work none new))
        · exact List.mem_append_right _ (List.mem_append_right _ remaining)
  unfold State.streamItems at emitted
  split at emitted
  · cases emitted
  · have same := (List.mem_cons.mp emitted).resolve_right
      (State.drainReadyGroups_noStreamValues _ _ _ _ _)
    have notices := (Execution.WorkQueueEvent.streamValues.inj same).2.2.2
    rw [notices] at noticed
    have member := loop items (queue, [], [], []) noticed
    obtain ⟨item, supplied, descriptor⟩ := List.mem_flatMap.mp member
    obtain ⟨entry, fromItem, same⟩ := List.mem_map.mp descriptor
    exact ⟨item, supplied, entry, fromItem, same⟩

/-- An item handler's stream-value carrier is always its first output event.
Witness: the inactive branch emits nothing; the active branch emits one carrier followed
by a group-only drain. Drain-generated stream notices therefore use different carriers.
-/
theorem State.streamItems_carrier_index (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) {index owner values groups streams}
    (atEvent
      : (queue.streamItems stream items).2[index]?
        = some (.streamValues owner values groups streams))
    : index = 0 := by
  unfold State.streamItems at atEvent
  split at atEvent
  · simp at atEvent
  · cases index with
    | zero => rfl
    | succ index =>
        exact False.elim (State.drainReadyGroups_noStreamValues _ _ _ _ _
          (List.mem_of_getElem? atEvent))

/-- Each stream notice's producer belongs to the item carrier's own occurrence list.
Witness: recover the exact supplied child descriptor, then use the source's child-lowering
match to identify its generating item. Equal item payloads never identify occurrences.
-/
theorem State.streamItems_noticeProducer {work : Execution.Work} (queue : State)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {owner values groups streams}
    (emitted
      : Execution.WorkQueueEvent.streamValues owner values groups streams
        ∈ (queue.streamItems stream items).2)
    {child} (noticed : child ∈ streams)
    : ∃ occurrence,
        NodeAt work child .stream [] (some occurrence)
        ∧ occurrence
          ∈ (GraphEvent.itemPublications (.streamItems stream items)).map Prod.fst := by
  obtain ⟨item, member, entry, supplied, same⟩ :=
    queue.streamItems_noticeSource stream items emitted noticed
  refine ⟨item.occurrence, same ▸ matching.streamItem_childStream_producer member supplied, ?_⟩
  simp only [GraphEvent.itemPublications, List.map_map, Function.comp_def]
  exact List.mem_map.mpr ⟨item, member, rfl⟩

-----------------------------------------------------------------------------------------
-- Release support is indexed by the inclusive item-publication prefix
-----------------------------------------------------------------------------------------

/-- A child stream announced by an item carrier has its producer among the item labels
published through that carrier, including its own items. `published` is the ordered item
inventory; exact payload erasure is supplied separately by the replay theorem.
-/
def ItemStreamReleasePublications (work : Execution.Work)
    (published : List ItemPublication) (events : List WorkQueueEvent)
    : Prop :=
  ∀ index owner values groups streams,
    events[index]? = some (.streamValues owner values groups streams)
    → ∀ child ∈ streams,
        ∃ occurrence,
          NodeAt work child .stream [] (some occurrence)
          ∧ occurrence
            ∈ (published.take
                ((events.take (index + 1)).flatMap WorkQueueEvent.itemValues).length).map
                Prod.fst

/-- Output without stream-value events needs no item-carrier release witness.
Witness: an indexed carrier would be a member of that output, contradicting its exclusion.
-/
theorem ItemStreamReleasePublications.of_noStreamValues {work published events}
    (absent
      : ∀ owner values groups streams,
          Execution.WorkQueueEvent.streamValues owner values groups streams ∉ events)
    : ItemStreamReleasePublications work published events := by
  intro index owner values groups streams atEvent
  exact False.elim (absent owner values groups streams (List.mem_of_getElem? atEvent))

/-- Empty output has no item-stream carrier requiring publication support.
Witness: no stream-value event belongs to the empty list.
-/
theorem ItemStreamReleasePublications.nil (work : Execution.Work)
    : ItemStreamReleasePublications work [] [] :=
  .of_noStreamValues (by simp)

/-- An accepted handler publishes each new child stream's producer in its carrier batch.
Witness: item handlers copy their complete input item list; task handlers and closures emit
no stream-value carrier. Only source matching and the existing start check are used.
-/
theorem State.handleGraphEvent_itemStreamRelease {work : Execution.Work} (queue : State)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (accepted : queue.acceptsGraphEvent event = true)
    : ItemStreamReleasePublications work event.itemPublications
        (queue.handleGraphEvent event).2 := by
  cases event with
  | taskSuccess occurrence result =>
      apply ItemStreamReleasePublications.of_noStreamValues
      intro owner values groups streams emitted
      have impossible : owner.ref ∈
          (queue.taskSuccess occurrence result).2.flatMap rawStreamReferenceRefs :=
        List.mem_flatMap.mpr ⟨_, emitted, List.mem_cons_self⟩
      rw [State.taskSuccess_streamReferences] at impossible
      cases impossible
  | taskFailure occurrence errors =>
      apply ItemStreamReleasePublications.of_noStreamValues
      intro owner values groups streams emitted
      have impossible : owner.ref ∈
          (queue.taskFailure occurrence errors).2.flatMap rawStreamReferenceRefs :=
        List.mem_flatMap.mpr ⟨_, emitted, List.mem_cons_self⟩
      rw [State.taskFailure_streamReferences] at impossible
      cases impossible
  | streamItems stream items =>
      intro index owner values groups streams atEvent child noticed
      change (queue.streamItems stream items).2[index]? = _ at atEvent
      have member := List.mem_of_getElem? atEvent
      obtain ⟨occurrence, known, source⟩ :=
        queue.streamItems_noticeProducer matching member noticed
      have zero := queue.streamItems_carrier_index stream items atEvent
      subst index
      have count := congrArg List.length (queue.streamItems_itemValues stream items accepted)
      simp only [List.length_map] at count
      refine ⟨occurrence, known, ?_⟩
      have active : queue.rootStreams.contains stream.ref = true := accepted
      have whole : ((queue.handleGraphEvent (.streamItems stream items)).2.take 1).flatMap
          WorkQueueEvent.itemValues
          = (queue.streamItems stream items).2.flatMap WorkQueueEvent.itemValues := by
        simp only [State.handleGraphEvent, State.streamItems, active, Bool.not_true,
          Bool.false_eq_true, ite_false, List.take_succ_cons, List.take_zero,
          List.flatMap_cons, List.flatMap_nil, State.drainReadyGroups_itemValues]
      rw [whole, count, List.take_length]
      exact source
  | streamSuccess stream =>
      apply ItemStreamReleasePublications.of_noStreamValues
      intro owner values groups streams
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp
  | streamFailure stream errors =>
      apply ItemStreamReleasePublications.of_noStreamValues
      intro owner values groups streams
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
