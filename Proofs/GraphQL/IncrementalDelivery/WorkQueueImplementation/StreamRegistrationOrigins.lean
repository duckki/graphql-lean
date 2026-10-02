import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents

/-! A registered stream's structural producer has already appeared in the source history. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration provenance, independent of announcement and source timing
-----------------------------------------------------------------------------------------

/-- A stream is producer-free or its structural producer occurs among `seen` identities.
`work` supplies its descriptor; `seen` records received source events, not future work.
The predicate permits ignored input identities and does not assert publication or notice.
-/
def StreamProducerSeen (work : Execution.Work) (seen : List Occurrence)
    (node : Execution.DeliveryNode)
    : Prop :=
  ∃ dependencies producer,
    NodeAt work node .stream dependencies producer
    ∧ ∀ occurrence, producer = some occurrence → occurrence ∈ seen

/-- Enlarging the received identity history preserves stream registration provenance.
Witness: retain the same structural descriptor and transport producer membership.
-/
theorem StreamProducerSeen.mono {work before after node}
    (origin : StreamProducerSeen work before node) (included : before.Subset after)
    : StreamProducerSeen work after node := by
  obtain ⟨dependencies, producer, known, seen⟩ := origin
  exact ⟨dependencies, producer, known, fun occurrence same => included (seen occurrence same)⟩

/-- A matched event's immediate child streams have producers among its own identities.
Witness: exact object/item child lowering identifies the producing success or item.
Failure and completion events register no streams.
-/
theorem GraphEvent.MatchesWork.childStreams_producerSeen {work : Execution.Work}
    {event : GraphEvent} (matching : event.MatchesWork work)
    : event.ChildStreamsSatisfy (StreamProducerSeen work event.identities.1) := by
  cases event with
  | taskSuccess occurrence result =>
      intro stream member
      obtain ⟨dependencies, known⟩ := matching.childStream_producer member
      refine ⟨dependencies, some occurrence, known, ?_⟩
      intro parent same
      exact (Option.some.inj same) ▸ List.mem_cons_self
  | streamItems stream items =>
      intro item member child supplied
      refine ⟨[], some item.occurrence,
        matching.streamItem_childStream_producer member supplied, ?_⟩
      intro parent same
      exact (Option.some.inj same) ▸ List.mem_map_of_mem member
  | taskFailure | streamSuccess | streamFailure => trivial

/-- Actual source replay registers only streams with previously received producers.
Witness: initialization registers producer-free descriptors; matched handlers extend
provenance by their own identities. No source start, freshness, or output admission is used.
-/
theorem createWorkQueue_replay_streamProducersSeen {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).StreamsSatisfy
        (StreamProducerSeen work (events.flatMap (fun event => event.identities.1))) := by
  induction valid with
  | nil =>
      intro stream member
      exact ⟨[], none, (createWorkQueue_initialStreams_nodeAt work).1 stream member,
        fun _ impossible => nomatch impossible⟩
  | @append before event valid matching fresh ready ih =>
      rw [State.replayGraphEvents_append, List.flatMap_append, List.flatMap_singleton]
      have old : ((State.initialize (Work.fromExecution work)).replayGraphEvents before).StreamsSatisfy
          (StreamProducerSeen work
            (before.flatMap (fun event => event.identities.1) ++ event.identities.1)) :=
        fun stream member => (ih stream member).mono (List.subset_append_left _ _)
      apply old.handleGraphEvent event
      have new := matching.childStreams_producerSeen
      cases event with
      | taskSuccess occurrence result =>
          exact fun stream member => (new stream member).mono (List.subset_append_right _ _)
      | streamItems stream items =>
          exact fun item member child supplied =>
            (new item member child supplied).mono (List.subset_append_right _ _)
      | taskFailure | streamSuccess | streamFailure => trivial

-----------------------------------------------------------------------------------------
-- Fresh structural producers cannot collide with any earlier registered stream key
-----------------------------------------------------------------------------------------

/-- A stream from an unseen producer has no existing registry lookup.
Witness: generated key uniqueness identifies producers of equal-key descriptors; an old
lookup would place the fresh producer among already received identities.
-/
theorem State.StreamsSatisfy.freshProducer_streamAbsent {queue : State} {work seen}
    (origins : queue.StreamsSatisfy (StreamProducerSeen work seen))
    (generated : ExecutedWork work) {node dependencies producer}
    (known : NodeAt work node .stream dependencies (some producer))
    (fresh : producer ∉ seen)
    : queue.stream? node.key = none := by
  cases found : queue.stream? node.key with
  | none => rfl
  | some stream =>
      obtain ⟨member, sameKey⟩ := State.stream?_some found
      obtain ⟨oldDependencies, oldProducer, descriptor, observed⟩ := origins stream member
      have same := generated.streamProducer_unique descriptor known sameKey
      exact False.elim (fresh (observed producer same))

/-- Every child stream of a fresh object success is absent before that input is handled.
Witness: replay registration provenance and the unique generated producer for each key.
This excludes accidental deduplication against a stream introduced by another producer.
-/
theorem ExecutedWork.replayGraphEvents_taskChildStream_absent
    {work before occurrence result} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work before)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    {stream : Stream} (member : stream ∈ result.work.streams)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents before).stream?
        stream.node.key
      = none := by
  obtain ⟨dependencies, known⟩ := matching.childStream_producer member
  exact (createWorkQueue_replay_streamProducersSeen valid).freshProducer_streamAbsent
    generated known (fresh.2.2.1 occurrence List.mem_cons_self)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
