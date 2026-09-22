import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistry

/-! Initial and registered stream descriptors retain their exact structural work metadata. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Source payloads identify each stream's generating occurrence
-----------------------------------------------------------------------------------------

/-- A stream supplied by an item result has that exact item as its structural producer.
Witness: source matching fixes the child subtree and its address; immediate stream lowering
inherits the located item's producer, without any queue-state or publication premise.
-/
theorem GraphEvent.MatchesWork.streamItem_childStream_producer
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    {child : Stream} (supplied : child ∈ item.work.streams)
    : NodeAt work child.node .stream [] (some item.occurrence) := by
  cases item with
  | mk occurrence value childWork =>
      obtain ⟨owners, producer, known, childrenWork⟩ := matching _ member
      cases occurrence with
      | executionGroup address => cases childrenWork
      | item address index =>
          obtain ⟨node, entries, enclosing, result, children, located, entry, _, _⟩ := known
          change locateWork work address = some
            ⟨.stream node entries, producer, enclosing⟩ at located
          have lowering : childWork = Work.fromExecution children (address ++ [index]) := by
            simpa [streamItemWork?, located, entry] using childrenWork.symm
          rw [lowering] at supplied
          exact workFromSpec_streams_nodeAt (Located.item located entry) supplied

/-- Each registered descriptor denotes an actual stream node, with existential source context.
The descriptor itself is retained exactly; permissive raw work need not have unique keys.
-/
def StreamLocated (work : Execution.Work) (stream : Execution.DeliveryNode) : Prop :=
  ∃ dependencies producer, NodeAt work stream .stream dependencies producer

/-- Matching source payloads supply only structurally located child stream descriptors.
Witness: successful tasks and items retain their exact child lowering; other events supply
no streams. This projection is derived from MatchesWork, not an additional source premise.
-/
theorem GraphEvent.MatchesWork.childStreamsLocated {work : Execution.Work}
    {event : GraphEvent} (matching : event.MatchesWork work)
    : event.ChildStreamsSatisfy (StreamLocated work) := by
  cases event with
  | taskSuccess occurrence result =>
      intro stream member
      obtain ⟨dependencies, known⟩ := matching.childStream_producer member
      exact ⟨dependencies, some occurrence, known⟩
  | streamItems stream items =>
      intro item member child supplied
      exact ⟨[], some item.occurrence, matching.streamItem_childStream_producer member supplied⟩
  | taskFailure | streamSuccess | streamFailure => trivial

-----------------------------------------------------------------------------------------
-- Initial notices and every registered stream have genuine structural descriptors
-----------------------------------------------------------------------------------------

/-- Every initially registered or announced stream has no structural producer or dependencies.
Witness: root lowering traverses only combine nodes; queue creation retains supplied stream
descriptors. No generated-work, source, nonempty-work, or scheduler premise is necessary.
-/
theorem createWorkQueue_initialStreams_nodeAt (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).StreamsSatisfy
        (fun node => NodeAt work node .stream [] none)
      ∧ ∀ node ∈ (State.initialize (Work.fromExecution work)).initialStreams,
          NodeAt work node .stream [] none := by
  apply createWorkQueue_streamsSatisfy
  intro stream member
  exact workFromSpec_streams_nodeAt Located.root member

/-- A generated stream whose key was initially announced cannot have a task/item producer.
Witness: initial notice metadata supplies a producer-free descriptor with that key, and
generated allocation uniqueness equates its producer with the independently known node.
-/
theorem ExecutedWork.initialStream_producerNone {work : Execution.Work}
    (generated : ExecutedWork work) {stream dependencies producer}
    (known : NodeAt work stream .stream dependencies producer)
    (initial
      : stream.key
        ∈ (State.initialize (Work.fromExecution work)).initialStreams.map
            Execution.DeliveryNode.key)
    : producer = none := by
  obtain ⟨announced, member, sameKey⟩ := List.mem_map.mp initial
  exact generated.streamProducer_unique known
    ((createWorkQueue_initialStreams_nodeAt work).2 announced member) sameKey.symm

/-- Every registered stream throughout replay has its exact descriptor in the original work.
Witness: root lowering establishes the registry; matched task/item child lowering and each
handler's descriptor-preservation proof maintain it through actual normalized batches.
Only source matching is used, with no generated-key uniqueness or start requirement.
-/
theorem createWorkQueue_runNormalized_streamsLocated {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.StreamsSatisfy
        (StreamLocated work) := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (known : acc.1.StreamsSatisfy (StreamLocated work))
      (sources : ∀ event ∈ more.flatten, event.MatchesWork work)
      : (more.foldl normalizedStep acc).1.StreamsSatisfy (StreamLocated work) := by
    induction more generalizing acc with
    | nil => exact known
    | cons batch rest ih =>
        apply ih
        · rw [normalizedStep_queue]
          exact known.handleGraphEvents batch (fun event member =>
            (sources event (List.mem_append_left _ member)).childStreamsLocated)
        · intro event member
          exact sources event (List.mem_append_right _ member)
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  apply loop batches (queue, publisher, [])
  · intro stream member
    exact ⟨[], none, (createWorkQueue_initialStreams_nodeAt work).1 stream member⟩
  · intro event member
    exact valid.event_matches member

/-- Any later group flush releases only genuine stream descriptors from its actual registry.
Witness: matching replay locates all registry entries; the flush retrieves unchanged entries
by key. This local metadata witness does not yet identify all notice carriers in the output.
-/
theorem createWorkQueue_runNormalized_releasedStreamsLocated {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (group : GroupNode)
    : ∀ node ∈
        (((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.finishGroupSuccess
          group).2.2.newStreams,
        StreamLocated work node :=
  (createWorkQueue_runNormalized_streamsLocated valid).finishGroupSuccess_notices group

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
