import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamLoweringCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamItemRootCoverage

/-! Root and item integration cannot omit a fresh supplied stream from their notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Immediate root integration announces exactly its registry additions
-----------------------------------------------------------------------------------------

/-- Parentless integration returns every fresh supplied stream ref as a notice.
Witness: group/task integration preserves the old stream registry before complete selection.
-/
theorem State.maybeIntegrateWork_fresh_root_notice (queue : State) (work : Work)
    {stream : Stream} (member : stream ∈ work.streams)
    (absent : queue.stream? stream.node.ref = none)
    : stream.node.ref
      ∈ (queue.maybeIntegrateWork work).2.newStreams.map Execution.DeliveryNode.ref := by
  have prior : (work.tasks.foldl State.addTask (queue.addGroups work.groups).1).stream?
      stream.node.ref = none := by
    simpa only [State.stream?,
      fold_projection State.streams State.addTask State.addTask_streams,
      State.addGroups_streams]
      using absent
  exact State.addStreams_fresh_root_notice _ work.streams member prior

/-- Immediate root integration adds exactly the refs it returns in its stream notices.
Witness: the same deduplicated selection is appended to the registry and returned as notices.
This equality permits repeated raw input refs without assuming generated-work uniqueness.
-/
theorem State.maybeIntegrateWork_root_streamRefs (queue : State) (work : Work)
    : (queue.maybeIntegrateWork work).1.streams.map (fun stream => stream.node.ref)
      = queue.streams.map (fun stream => stream.node.ref)
        ++ (queue.maybeIntegrateWork work).2.newStreams.map
            Execution.DeliveryNode.ref := by
  simp only [State.maybeIntegrateWork, State.addStreams, List.map_append, List.map_map,
    fold_projection State.streams State.addTask State.addTask_streams, State.addGroups_streams]
  rfl

/-- Every supplied root stream ref is present after immediate integration.
Witness: an old lookup retains the ref, while an absent lookup must be returned as a notice.
-/
theorem State.maybeIntegrateWork_root_streamRef_covered (queue : State) (work : Work)
    {stream : Stream} (member : stream ∈ work.streams)
    : stream.node.ref
      ∈ (queue.maybeIntegrateWork work).1.streams.map
          (fun registered => registered.node.ref) := by
  rw [queue.maybeIntegrateWork_root_streamRefs work]
  cases found : queue.stream? stream.node.ref with
  | none => exact List.mem_append_right _ (queue.maybeIntegrateWork_fresh_root_notice
      work member found)
  | some registered =>
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨registered, (State.stream?_some found).1,
          (State.stream?_some found).2⟩)

/-- Every producer-free structural stream has an initial notice, including exhausted streams.
Witness: inverse root lowering and fresh complete registration in the empty initial state.
-/
theorem NodeAt.stream_initial_notice {work node dependencies}
    (known : NodeAt work node .stream dependencies none)
    : node.ref
      ∈ (State.initialize (Work.fromExecution work)).initialStreams.map
          Execution.DeliveryNode.ref :=
  ({} : State).maybeIntegrateWork_fresh_root_notice (Work.fromExecution work)
    (NodeAt.stream_initial_input known) rfl

-----------------------------------------------------------------------------------------
-- Item batching deduplicates refs but cannot lose an unregistered input stream
-----------------------------------------------------------------------------------------

/-- An item step's registry grows by exactly its immediate returned stream notices.
Witness: pruning and starting work leave the registry unchanged after integration.
-/
theorem streamItemStep_streamRefs
    (acc
      : State
        × List Execution.DeliveryNode
        × List Execution.DeliveryNode
        × List StreamItemValue) (item : StreamItem)
    : (streamItemStep acc item).1.streams.map (fun stream => stream.node.ref)
      = acc.1.streams.map (fun stream => stream.node.ref)
        ++ (acc.1.maybeIntegrateWork item.work).2.newStreams.map
            Execution.DeliveryNode.ref := by
  simp only [streamItemStep, State.startNewWork_streams, State.pruneEmptyGroups_streams]
  exact acc.1.maybeIntegrateWork_root_streamRefs item.work

/-- All item-fold registry additions appear in the accumulated stream notice list.
Witness: each item appends the exact same selected refs to registry and notices.
-/
theorem State.streamItemFold_streamRefs (queue : State) (items : List StreamItem)
    : let prepared := items.foldl streamItemStep (queue, [], [], [])
      prepared.1.streams.map (fun stream => stream.node.ref)
      = queue.streams.map (fun stream => stream.node.ref)
        ++ prepared.2.2.1.map Execution.DeliveryNode.ref := by
  have loop (remaining : List StreamItem)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue)
      (prior : acc.1.streams.map (fun stream => stream.node.ref)
        = queue.streams.map (fun stream => stream.node.ref)
          ++ acc.2.2.1.map Execution.DeliveryNode.ref)
      : (remaining.foldl streamItemStep acc).1.streams.map (fun stream => stream.node.ref)
        = queue.streams.map (fun stream => stream.node.ref)
          ++ (remaining.foldl streamItemStep acc).2.2.1.map Execution.DeliveryNode.ref := by
    induction remaining generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih
        rw [streamItemStep_streamRefs, prior]
        simp only [streamItemStep, List.map_append, List.append_assoc]
  exact loop items (queue, [], [], []) (by simp)

/-- Every stream supplied by any item is registered by the end of preparation.
Witness: the item that supplies the ref registers it, and subsequent steps retain it.
This covers arbitrary repeated input descriptors independently of producer uniqueness.
-/
theorem State.streamItemFold_supplied_streamRef (queue : State) (items : List StreamItem)
    {item : StreamItem} (selected : item ∈ items) {stream : Stream}
    (supplied : stream ∈ item.work.streams)
    : stream.node.ref
      ∈ (items.foldl streamItemStep (queue, [], [], [])).1.streams.map
          (fun registered => registered.node.ref) := by
  have loop (remaining : List StreamItem)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue)
      (prior : item ∈ remaining
        ∨ stream.node.ref ∈ acc.1.streams.map (fun registered => registered.node.ref))
      : stream.node.ref ∈ (remaining.foldl streamItemStep acc).1.streams.map
          (fun registered => registered.node.ref) := by
    induction remaining generalizing acc with
    | nil => exact prior.resolve_left (by simp)
    | cons current rest ih =>
        apply ih
        rcases prior with incoming | registered
        · rcases List.mem_cons.mp incoming with rfl | later
          · apply Or.inr
            simpa only [streamItemStep, State.startNewWork_streams,
              State.pruneEmptyGroups_streams]
              using acc.1.maybeIntegrateWork_root_streamRef_covered item.work supplied
          · exact .inl later
        · apply Or.inr
          rw [streamItemStep_streamRefs]
          exact List.mem_append_left _ registered
  exact loop items (queue, [], [], []) (.inl selected)

/-- A supplied child stream absent before the batch appears in its accumulated notices.
Witness: complete registration and the exact registry delta force the new ref into notices.
Deduplication against an earlier item in the same batch is therefore harmless.
-/
theorem State.streamItemFold_fresh_notice (queue : State) (items : List StreamItem)
    {item : StreamItem} (selected : item ∈ items) {stream : Stream}
    (supplied : stream ∈ item.work.streams)
    (absent : queue.stream? stream.node.ref = none)
    : stream.node.ref
      ∈ (items.foldl streamItemStep (queue, [], [], [])).2.2.1.map
          Execution.DeliveryNode.ref := by
  have registered := queue.streamItemFold_supplied_streamRef items selected supplied
  rw [queue.streamItemFold_streamRefs items] at registered
  apply (List.mem_append.mp registered).resolve_left
  intro old
  obtain ⟨prior, included, same⟩ := List.mem_map.mp old
  obtain ⟨found, lookup⟩ := State.stream?_exists_of_registered
    (node := prior.node) (List.mem_map.mpr ⟨prior, included, rfl⟩)
  rw [same, absent] at lookup
  cases lookup

/-- An accepted item batch carries every fresh supplied child-stream ref in its first event.
Witness: the leading item event uses the complete accumulated notices; later draining
cannot remove an already emitted notice from the output history.
-/
theorem State.streamItems_fresh_notice {queue : State} (stream : Execution.DeliveryNode)
    (items : List StreamItem) (active : queue.rootStreams.contains stream.ref = true)
    {item : StreamItem} (selected : item ∈ items) {child : Stream}
    (supplied : child ∈ item.work.streams) (absent : queue.stream? child.node.ref = none)
    : child.node.ref
      ∈ (queue.streamItems stream items).2.flatMap rawStreamNoticeRefs := by
  rw [queue.streamItems_eq stream items]
  simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons,
    rawStreamNoticeRefs]
  exact List.mem_append_left _ (queue.streamItemFold_fresh_notice items selected supplied absent)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
