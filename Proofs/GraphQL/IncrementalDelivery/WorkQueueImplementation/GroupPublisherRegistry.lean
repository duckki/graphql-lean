import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublisherRegistry

/-! The actual publisher registry agrees with open notices on every generated group key. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated group keys cannot occur in either stream notices or stream references
-----------------------------------------------------------------------------------------

/-- A raw event neither announces nor references the specified key as a stream.
This projection is derived for generated group keys, not imposed on the event source.
-/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.NoStreamKey (key : Nat)
    (event : WorkQueueEvent)
    : Prop :=
  key ∉ rawStreamNoticeKeys event ∧ key ∉ rawStreamReferenceKeys event

/-- Raw replay announces only structurally located streams.
Witness: initial lowering and matching source payloads establish the retained registry
property used by the actual handler replay. No output-admission premise is needed.
-/
theorem createWorkQueue_rawEventReplay_streamNoticesLocated {work events}
    (valid : ValidGraphEvents work events)
    : ∀ output ∈ ((State.initialize (Work.fromExecution work)).rawEventReplay events).2,
        output.StreamNoticesSatisfy (StreamLocated work) := by
  have initial : (State.initialize (Work.fromExecution work)).StreamsSatisfy (StreamLocated work) :=
    fun stream member =>
      ⟨[], none, (createWorkQueue_initialStreams_nodeAt work).1 stream member⟩
  exact initial.rawEventReplay_notices events
    (fun _ member => (valid.event_matches member).childStreamsLocated)

/-- A raw stream notice's key has its exact descriptor in the original work.
Witness: invert either notice carrier and retain the descriptor supplied by metadata.
-/
theorem
    _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.StreamNoticesSatisfy.located_key
    {work event key} (known : event.StreamNoticesSatisfy (StreamLocated work))
    (notice : key ∈ rawStreamNoticeKeys event)
    : ∃ stream dependencies producer,
        stream.key = key ∧ NodeAt work stream .stream dependencies producer := by
  cases event with
  | groupSuccess group groups streams | streamValues group values groups streams =>
      obtain ⟨stream, member, same⟩ := List.mem_map.mp notice
      obtain ⟨dependencies, producer, located⟩ := known stream member
      exact ⟨stream, dependencies, producer, same, located⟩
  | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases notice

/-- Generated group keys never occur in actual raw stream notices or references.
Witness: earlier-notice accounting locates references; generated group/stream role
separation excludes both kinds of stream key without requiring notice freshness.
-/
theorem createWorkQueue_rawEventReplay_noStreamKey
    {work events group dependencies producer} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work events)
    (known : NodeAt work group .group dependencies producer)
    : ∀ output ∈ ((State.initialize (Work.fromExecution work)).rawEventReplay events).2,
        output.NoStreamKey group.key := by
  let queue := State.initialize (Work.fromExecution work)
  have noNotice output (member : output ∈ (queue.rawEventReplay events).2)
      : group.key ∉ rawStreamNoticeKeys output := by
    intro notice
    obtain ⟨stream, _, _, same, located⟩ :=
      (createWorkQueue_rawEventReplay_streamNoticesLocated valid output member).located_key notice
    exact generated.groupStreamKeysDisjoint known located same.symm
  intro output member
  refine ⟨noNotice output member, ?_⟩
  intro reference
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have earlier := (queue.rawEventReplay_streamReferencesAnnounced events).atEvent
    selected reference
  rcases List.mem_append.mp earlier with initial | noticed
  · have initialNotice := createWorkQueue_streamRoots (Work.fromExecution work) initial
    obtain ⟨stream, member, same⟩ := List.mem_map.mp initialNotice
    exact generated.groupStreamKeysDisjoint known
      ((createWorkQueue_initialStreams_nodeAt work).2 stream member) same.symm
  · obtain ⟨carrier, prior, notice⟩ := List.mem_flatMap.mp noticed
    exact noNotice carrier (List.mem_of_mem_take prior) notice

-----------------------------------------------------------------------------------------
-- Pointwise registry transport needs only freshness of the queried group key
-----------------------------------------------------------------------------------------

/-- Filtering the active list removes exactly its closing key.
Witness: invert filtered descriptor membership in both directions.
-/
theorem IncrementalPublisher.active_filter_key (nodes : List Execution.DeliveryNode)
    (closed key : Nat)
    : key ∈ (nodes.filter (fun node => node.key != closed)).map Execution.DeliveryNode.key
      ↔ key ∈ nodes.map Execution.DeliveryNode.key ∧ key ≠ closed := by
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨node, ⟨member, different⟩, rfl⟩
    exact ⟨⟨node, member, rfl⟩, by simpa using different⟩
  · rintro ⟨⟨node, member, rfl⟩, different⟩
    exact ⟨node, ⟨member, by simpa using different⟩, rfl⟩

/-- On a key unused by streams, the publisher changes membership only for group controls.
Witness: direct case analysis of the real handler, retaining new group notices and
removing the closing group. Value-owner remapping changes no active-list entry.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_active_group
    (publisher : IncrementalPublisher) (event : WorkQueueEvent) {key}
    (separate : event.NoStreamKey key)
    : key ∈ (publisher.handleWorkQueueEvent event).1.active.map Execution.DeliveryNode.key
      ↔ (key ∈ publisher.active.map Execution.DeliveryNode.key
          ∧ key ∉ rawGroupClosureKeys event)
        ∨ key ∈ rawGroupNoticeKeys event := by
  cases event <;>
    simp_all [IncrementalPublisher.handleWorkQueueEvent, rawGroupNoticeKeys,
      rawGroupClosureKeys, WorkQueueEvent.NoStreamKey, rawStreamNoticeKeys,
      rawStreamReferenceKeys, List.map_append, active_filter_key] <;> grind

/-- Stream-disjoint normalization preserves pending and completion membership for one key.
Witness: eventwise projection; the only expansion is a notice-free object-value list.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_group_key_projections
    (publisher : IncrementalPublisher) (event : WorkQueueEvent) {key}
    (separate : event.NoStreamKey key)
    : (key ∈ pendingKeys (publisher.handleWorkQueueEvent event).2
        ↔ key ∈ rawGroupNoticeKeys event)
      ∧ (key ∈ completedKeys (publisher.handleWorkQueueEvent event).2
          ↔ key ∈ rawGroupClosureKeys event) := by
  cases event <;>
    simp_all [IncrementalPublisher.handleWorkQueueEvent, rawGroupNoticeKeys,
      rawGroupClosureKeys, WorkQueueEvent.NoStreamKey, rawStreamNoticeKeys,
      rawStreamReferenceKeys, pendingKeys, completedKeys, eventPending, eventCompleted,
      List.flatMap_map, List.map_append]

/-- One fresh group-key transition preserves pointwise active/open agreement.
Witness: the handler's exact active-list equation and pending/completion projections;
fresh notices cannot resurrect a completed key or the carrier's own closing key.
-/
theorem IncrementalPublisher.registry_group_key_step (publisher : IncrementalPublisher)
    (initial : Keys) (events : List Execution.WorkQueueEvent) (event : WorkQueueEvent)
    {key}
    (registry
      : key ∈ publisher.active.map Execution.DeliveryNode.key ↔ Open initial events key)
    (separate : event.NoStreamKey key)
    (fresh
      : key ∈ rawGroupNoticeKeys event
        → key ∉ completedKeys events ∧ key ∉ rawGroupClosureKeys event)
    : key ∈ (publisher.handleWorkQueueEvent event).1.active.map Execution.DeliveryNode.key
      ↔ Open initial (events ++ (publisher.handleWorkQueueEvent event).2) key := by
  rw [publisher.handleWorkQueueEvent_active_group event separate, registry]
  obtain ⟨notices, closures⟩ :=
    publisher.handleWorkQueueEvent_group_key_projections event separate
  simp only [Open, announcedKeys, pendingKeys, completedKeys, List.flatMap_append,
    List.mem_append, not_or] at *
  grind

/-- Fresh replay preserves the publisher registry at any group key unused by stream events.
Witness: actual normalization induction threads the same publisher and output prefix;
the exclusion predicate grows precisely by each event's group closures.
-/
theorem IncrementalPublisher.registry_group_key_normalize
    (publisher : IncrementalPublisher) (initial : Keys)
    (events : List Execution.WorkQueueEvent) (raw : List WorkQueueEvent)
    {retired : Nat → Prop} {key}
    (registry
      : key ∈ publisher.active.map Execution.DeliveryNode.key ↔ Open initial events key)
    (closed : key ∈ completedKeys events → retired key)
    (separate : ∀ event ∈ raw, event.NoStreamKey key)
    (fresh : GroupNoticesFresh retired raw)
    : key ∈ (publisher.normalizeBatch raw).1.active.map Execution.DeliveryNode.key
      ↔ Open initial (events ++ (publisher.normalizeBatch raw).2) key := by
  induction raw generalizing publisher events retired with
  | nil => simpa [IncrementalPublisher.normalizeBatch] using registry
  | cons event rest ih =>
      have headSeparate := separate event List.mem_cons_self
      have current := publisher.registry_group_key_step initial events event registry headSeparate
        (fun notice => ⟨fun previous => (fresh.1 key notice).1 (closed previous),
          (fresh.1 key notice).2⟩)
      have nextClosed : key ∈ completedKeys (events ++ (publisher.handleWorkQueueEvent event).2)
          → retired key ∨ key ∈ rawGroupClosureKeys event := by
        intro member
        rw [completedKeys, List.flatMap_append, List.mem_append] at member
        exact member.elim (fun old => .inl (closed old))
          (fun now => .inr ((publisher.handleWorkQueueEvent_group_key_projections
            event headSeparate).2.mp now))
      have later := ih (publisher.handleWorkQueueEvent event).1
        (events ++ (publisher.handleWorkQueueEvent event).2) current nextClosed
        (fun next member => separate next (List.mem_cons_of_mem _ member)) fresh.2
      simpa only [IncrementalPublisher.normalizeBatch_cons, List.append_assoc] using later

/-- Every actual raw prefix has exact active/open agreement for every generated group key.
Witness: concrete group-notice freshness and generated stream-role separation discharge
the pointwise normalization proof from the publisher's true initial registry.
-/
theorem createWorkQueue_rawPrefix_groupRegistry
    {work events group dependencies producer before} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work events)
    (known : NodeAt work group .group dependencies producer)
    (isPrefix
      : before.IsPrefix
          ((State.initialize (Work.fromExecution work)).rawEventReplay events).2)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      group.key
        ∈ (publisher.normalizeBatch before).1.active.map Execution.DeliveryNode.key
      ↔ Open
          ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.key)
          (publisher.normalizeBatch before).2 group.key := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have registry := publisher.registry_group_key_normalize
    ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.key) [] before
    (IncrementalPublisher.registry_initial _ group.key) (by simp [completedKeys])
    (fun event member => createWorkQueue_rawEventReplay_noStreamKey generated valid known
      event (isPrefix.subset member))
    ((createWorkQueue_rawEventReplay_groupNoticesFresh valid).prefix isPrefix)
  simpa only [List.nil_append] using registry

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
