import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublisherRegistry

/-! The actual publisher registry agrees with open notices on every generated group ref. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated group refs cannot occur in either stream notices or stream references
-----------------------------------------------------------------------------------------

/-- A raw event neither announces nor references the specified ref as a stream.
This projection is derived for generated group refs, not imposed on the event source.
-/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.NoStreamRef
    (ref : NodeRef) (event : WorkQueueEvent)
    : Prop :=
  ref ∉ rawStreamNoticeRefs event ∧ ref ∉ rawStreamReferenceRefs event

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

/-- A raw stream notice's ref has its exact descriptor in the original work.
Witness: invert either notice carrier and retain the descriptor supplied by metadata.
-/
theorem
    _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.StreamNoticesSatisfy.located_ref
    {work event ref} (known : event.StreamNoticesSatisfy (StreamLocated work))
    (notice : ref ∈ rawStreamNoticeRefs event)
    : ∃ stream dependencies producer,
        stream.ref = ref ∧ NodeAt work stream .stream dependencies producer := by
  cases event with
  | groupSuccess group groups streams | streamValues group values groups streams =>
      obtain ⟨stream, member, same⟩ := List.mem_map.mp notice
      obtain ⟨dependencies, producer, located⟩ := known stream member
      exact ⟨stream, dependencies, producer, same, located⟩
  | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases notice

/-- Generated group refs never occur in actual raw stream notices or references.
Witness: earlier-notice accounting locates references; generated group/stream role
separation excludes both kinds of stream ref without requiring notice freshness.
-/
theorem createWorkQueue_rawEventReplay_noStreamRef
    {work events group dependencies producer} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work events)
    (known : NodeAt work group .group dependencies producer)
    : ∀ output ∈ ((State.initialize (Work.fromExecution work)).rawEventReplay events).2,
        output.NoStreamRef group.ref := by
  let queue := State.initialize (Work.fromExecution work)
  have noNotice output (member : output ∈ (queue.rawEventReplay events).2)
      : group.ref ∉ rawStreamNoticeRefs output := by
    intro notice
    obtain ⟨stream, _, _, same, located⟩ :=
      (createWorkQueue_rawEventReplay_streamNoticesLocated valid output member).located_ref notice
    exact generated.groupStreamRefsDisjoint known located same.symm
  intro output member
  refine ⟨noNotice output member, ?_⟩
  intro reference
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have earlier := (queue.rawEventReplay_streamReferencesAnnounced events).atEvent
    selected reference
  rcases List.mem_append.mp earlier with initial | noticed
  · have initialNotice := createWorkQueue_streamRoots (Work.fromExecution work) initial
    obtain ⟨stream, member, same⟩ := List.mem_map.mp initialNotice
    exact generated.groupStreamRefsDisjoint known
      ((createWorkQueue_initialStreams_nodeAt work).2 stream member) same.symm
  · obtain ⟨carrier, prior, notice⟩ := List.mem_flatMap.mp noticed
    exact noNotice carrier (List.mem_of_mem_take prior) notice

-----------------------------------------------------------------------------------------
-- Pointwise registry transport needs only freshness of the queried group ref
-----------------------------------------------------------------------------------------

/-- Filtering the active list removes exactly its closing ref.
Witness: invert filtered descriptor membership in both directions.
-/
theorem IncrementalPublisher.active_filter_ref (nodes : List Execution.DeliveryNode)
    (closed ref : NodeRef)
    : ref ∈ (nodes.filter (fun node => node.ref != closed)).map Execution.DeliveryNode.ref
      ↔ ref ∈ nodes.map Execution.DeliveryNode.ref ∧ ref ≠ closed := by
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨node, ⟨member, different⟩, rfl⟩
    exact ⟨⟨node, member, rfl⟩, by simpa using different⟩
  · rintro ⟨⟨node, member, rfl⟩, different⟩
    exact ⟨node, ⟨member, by simpa using different⟩, rfl⟩

/-- On a ref unused by streams, the publisher changes membership only for group controls.
Witness: direct case analysis of the real handler, retaining new group notices and
removing the closing group. Value-owner remapping changes no active-list entry.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_active_group
    (publisher : IncrementalPublisher) (event : WorkQueueEvent) {ref}
    (separate : event.NoStreamRef ref)
    : ref ∈ (publisher.handleWorkQueueEvent event).1.active.map Execution.DeliveryNode.ref
      ↔ (ref ∈ publisher.active.map Execution.DeliveryNode.ref
          ∧ ref ∉ rawGroupClosureRefs event)
        ∨ ref ∈ rawGroupNoticeRefs event := by
  cases event <;>
    simp_all [IncrementalPublisher.handleWorkQueueEvent, rawGroupNoticeRefs,
      rawGroupClosureRefs, WorkQueueEvent.NoStreamRef, rawStreamNoticeRefs,
      rawStreamReferenceRefs, List.map_append, active_filter_ref] <;> grind

/-- Stream-disjoint normalization preserves pending and completion membership for one ref.
Witness: eventwise projection; the only expansion is a notice-free object-value list.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_group_ref_projections
    (publisher : IncrementalPublisher) (event : WorkQueueEvent) {ref}
    (separate : event.NoStreamRef ref)
    : (ref ∈ pendingRefs (publisher.handleWorkQueueEvent event).2
        ↔ ref ∈ rawGroupNoticeRefs event)
      ∧ (ref ∈ completedRefs (publisher.handleWorkQueueEvent event).2
          ↔ ref ∈ rawGroupClosureRefs event) := by
  cases event <;>
    simp_all [IncrementalPublisher.handleWorkQueueEvent, rawGroupNoticeRefs,
      rawGroupClosureRefs, WorkQueueEvent.NoStreamRef, rawStreamNoticeRefs,
      rawStreamReferenceRefs, pendingRefs, completedRefs, eventPending, eventCompleted,
      List.flatMap_map, List.map_append]

/-- One fresh group-ref transition preserves pointwise active/open agreement.
Witness: the handler's exact active-list equation and pending/completion projections;
fresh notices cannot resurrect a completed ref or the carrier's own closing ref.
-/
theorem IncrementalPublisher.registry_group_ref_step (publisher : IncrementalPublisher)
    (initial : NodeRefs) (events : List Execution.WorkQueueEvent) (event : WorkQueueEvent)
    {ref}
    (registry
      : ref ∈ publisher.active.map Execution.DeliveryNode.ref ↔ Open initial events ref)
    (separate : event.NoStreamRef ref)
    (fresh
      : ref ∈ rawGroupNoticeRefs event
        → ref ∉ completedRefs events ∧ ref ∉ rawGroupClosureRefs event)
    : ref ∈ (publisher.handleWorkQueueEvent event).1.active.map Execution.DeliveryNode.ref
      ↔ Open initial (events ++ (publisher.handleWorkQueueEvent event).2) ref := by
  rw [publisher.handleWorkQueueEvent_active_group event separate, registry]
  obtain ⟨notices, closures⟩ :=
    publisher.handleWorkQueueEvent_group_ref_projections event separate
  simp only [Open, announcedRefs, pendingRefs, completedRefs, List.flatMap_append,
    List.mem_append, not_or] at *
  grind

/-- Fresh replay preserves the publisher registry at any group ref unused by stream events.
Witness: actual normalization induction threads the same publisher and output prefix;
the exclusion predicate grows precisely by each event's group closures.
-/
theorem IncrementalPublisher.registry_group_ref_normalize
    (publisher : IncrementalPublisher) (initial : NodeRefs)
    (events : List Execution.WorkQueueEvent) (raw : List WorkQueueEvent)
    {retired : Nat → Prop} {ref}
    (registry
      : ref ∈ publisher.active.map Execution.DeliveryNode.ref ↔ Open initial events ref)
    (closed : ref ∈ completedRefs events → retired ref)
    (separate : ∀ event ∈ raw, event.NoStreamRef ref)
    (fresh : GroupNoticesFresh retired raw)
    : ref ∈ (publisher.normalizeBatch raw).1.active.map Execution.DeliveryNode.ref
      ↔ Open initial (events ++ (publisher.normalizeBatch raw).2) ref := by
  induction raw generalizing publisher events retired with
  | nil => simpa [IncrementalPublisher.normalizeBatch] using registry
  | cons event rest ih =>
      have headSeparate := separate event List.mem_cons_self
      have current := publisher.registry_group_ref_step initial events event registry headSeparate
        (fun notice => ⟨fun previous => (fresh.1 ref notice).1 (closed previous),
          (fresh.1 ref notice).2⟩)
      have nextClosed : ref ∈ completedRefs (events ++ (publisher.handleWorkQueueEvent event).2)
          → retired ref ∨ ref ∈ rawGroupClosureRefs event := by
        intro member
        rw [completedRefs, List.flatMap_append, List.mem_append] at member
        exact member.elim (fun old => .inl (closed old))
          (fun now => .inr ((publisher.handleWorkQueueEvent_group_ref_projections
            event headSeparate).2.mp now))
      have later := ih (publisher.handleWorkQueueEvent event).1
        (events ++ (publisher.handleWorkQueueEvent event).2) current nextClosed
        (fun next member => separate next (List.mem_cons_of_mem _ member)) fresh.2
      simpa only [IncrementalPublisher.normalizeBatch_cons, List.append_assoc] using later

/-- Every actual raw prefix has exact active/open agreement for every generated group ref.
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
      group.ref
        ∈ (publisher.normalizeBatch before).1.active.map Execution.DeliveryNode.ref
      ↔ Open
          ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
          (publisher.normalizeBatch before).2 group.ref := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have registry := publisher.registry_group_ref_normalize
    ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref) [] before
    (IncrementalPublisher.registry_initial _ group.ref) (by simp [completedRefs])
    (fun event member => createWorkQueue_rawEventReplay_noStreamRef generated valid known
      event (isPrefix.subset member))
    ((createWorkQueue_rawEventReplay_groupNoticesFresh valid).prefix isPrefix)
  simpa only [List.nil_append] using registry

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
