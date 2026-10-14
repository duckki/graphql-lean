import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedStreamAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistrationOrigins
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAnnouncementReplay

/-! Producer support belongs to the retained semantic input prefix, not the discarded
callback history. Registration and announcement invariants construct that support.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

open GraphQL.IncrementalDelivery.WorkQueueSemantics
open ReferenceWorkQueue (TaskProducersSucceeded StreamProducerSeen)

-----------------------------------------------------------------------------------------
-- Registered tasks and streams retain successful structural producers
-----------------------------------------------------------------------------------------

/-- A matching handler extends task-producer support using its own successful inputs.
The permanent registry appends exact child chunks or nothing; producer uniqueness fixes
each newly registered child's prerequisite. Source readiness is not assumed here.
-/
theorem taskProducers_handleGraphEvent {work : Work} {queue : ReferenceWorkQueue.State}
    {before : List GraphEvent} {event : GraphEvent}
    (prior : TaskProducersSucceeded work queue.tasks before)
    (matching : event.MatchesWork work)
    : TaskProducersSucceeded work (queue.handleGraphEvent event).1.tasks
        (before ++ [event]) := by
  intro task member producer known
  rw [List.flatMap_append, List.flatMap_singleton]
  rcases queue.handleGraphEvent_taskChunk event with unchanged | appended
  · rw [unchanged] at member
    exact List.mem_append_left _ (prior task member producer known)
  · rw [appended] at member
    rcases List.mem_append.mp member with old | new
    · exact List.mem_append_left _ (prior task old producer known)
    · obtain ⟨source, succeeded, _, _, descriptor⟩ := matching.childTasks_producer new
      obtain ⟨_, _, other⟩ := known
      have same := Option.some.inj (descriptor.unique other).2.1
      exact List.mem_append_right _ (same ▸ succeeded)

/-- Supplied child streams have producers among successes, not merely received identities.
Failure identities therefore cannot support a later registered stream's prerequisite.
-/
theorem childStreams_successfulProducers {work : Work} {event : GraphEvent}
    (matching : event.MatchesWork work)
    : event.ChildStreamsSatisfy (StreamProducerSeen work event.successes) := by
  cases event with
  | taskSuccess occurrence result =>
      intro stream member
      obtain ⟨dependencies, known⟩ := matching.childStream_producer member
      refine ⟨dependencies, some occurrence, known, ?_⟩
      intro source same
      exact (Option.some.inj same) ▸ List.mem_cons_self
  | streamItems stream items =>
      intro item member child supplied
      refine ⟨[], some item.occurrence,
        matching.streamItem_childStream_producer member supplied, ?_⟩
      intro source same
      exact (Option.some.inj same) ▸ List.mem_map_of_mem member
  | taskFailure | streamSuccess | streamFailure => trivial

/-- Handler registration preserves stream producer support in the retained success prefix.
An ignored task success cannot register descendants, even though its payload offers them.
-/
theorem streamProducers_handleGraphEvent {work : Work} {queue : ReferenceWorkQueue.State}
    {before : List GraphEvent} {event : GraphEvent}
    (prior
      : queue.StreamsSatisfy
          (StreamProducerSeen work
            (before.flatMap ReferenceWorkQueue.GraphEvent.successes)))
    (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.StreamsSatisfy
        (StreamProducerSeen work
          ((before ++ [event]).flatMap ReferenceWorkQueue.GraphEvent.successes)) := by
  rw [List.flatMap_append, List.flatMap_singleton]
  have old : queue.StreamsSatisfy
      (StreamProducerSeen work (before.flatMap ReferenceWorkQueue.GraphEvent.successes
        ++ event.successes)) :=
    fun stream member => (prior stream member).mono (List.subset_append_left _ _)
  apply old.handleGraphEvent event
  have supplied := childStreams_successfulProducers matching
  cases event with
  | taskSuccess occurrence result =>
      exact fun stream member => (supplied stream member).mono (List.subset_append_right _ _)
  | streamItems stream items =>
      exact fun item member child included =>
        (supplied item member child included).mono (List.subset_append_right _ _)
  | taskFailure | streamSuccess | streamFailure => trivial

-----------------------------------------------------------------------------------------
-- A proof-only invariant derived at initialization and each matching handler
-----------------------------------------------------------------------------------------

/-- Concrete registration support for a retained input prefix. The announcement inventory
is reused only to link active keys to registered descriptors; it is not wire admission.
No output equivalence, resource disposition, or desired source-readiness law is included.
-/
structure SourceSupport (work : Work) (queue : ReferenceWorkQueue.State)
    (before : List GraphEvent)
    : Prop where
  tasksRegistered : queue.StartedTasksRegistered
  taskProducers : TaskProducersSucceeded work queue.tasks before
  streamProducers
    : queue.StreamsSatisfy
        (StreamProducerSeen work (before.flatMap ReferenceWorkQueue.GraphEvent.successes))
  childStreams : queue.ChildStreamsMatchWork work
  activeRegistration
    : ∃ announced,
        queue.StreamAnnouncementInventory announced ∧ queue.rootStreams.Subset announced

/-- Root lowering supplies support without any successful input or output premise. -/
theorem SourceSupport.initialize (work : Work)
    : SourceSupport work
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)) [] := by
  refine ⟨ReferenceWorkQueue.createWorkQueue_startedTasksRegistered _,
    (ReferenceWorkQueue.createWorkQueue_producerOrder work).1, ?_,
    ReferenceWorkQueue.createWorkQueue_childStreamsMatchWork _ _, ?_⟩
  · intro stream member
    exact ⟨[], none, (ReferenceWorkQueue.createWorkQueue_initialStreams_nodeAt work).1
      stream member, fun _ impossible => nomatch impossible⟩
  · exact ⟨_, ReferenceWorkQueue.createWorkQueue_streamAnnouncementInventory _,
      ReferenceWorkQueue.createWorkQueue_streamRoots _⟩

/-- Matching retained inputs construct support before the next callback is considered.
Existing announcement proofs establish registry membership, not a chosen future trace.
-/
theorem SourceSupport.handleGraphEvent {work queue before event}
    (support : SourceSupport work queue before)
    (generated : ReferenceWorkQueue.ExecutedWork work) (matching : event.MatchesWork work)
    : SourceSupport work (queue.handleGraphEvent event).1 (before ++ [event]) := by
  refine ⟨support.tasksRegistered.handleGraphEvent event,
    taskProducers_handleGraphEvent support.taskProducers matching,
    streamProducers_handleGraphEvent support.streamProducers matching,
    support.childStreams.handleGraphEvent matching, ?_⟩
  obtain ⟨announced, inventory, roots⟩ := support.activeRegistration
  refine ⟨announced ++ (queue.handleGraphEvent event).2.flatMap
      ReferenceWorkQueue.rawStreamNoticeRefs,
    inventory.handleGraphEvent support.childStreams generated matching, ?_⟩
  intro key member
  rcases List.mem_append.mp (queue.handleGraphEvent_streamRoots event member) with old | fresh
  · exact List.mem_append_left _ (roots old)
  · exact List.mem_append_right _ fresh

/-- Batch-end termination changes no registration or producer-support evidence. -/
theorem SourceSupport.withTerminated {work queue before}
    (support : SourceSupport work queue before) (terminal : Bool)
    : SourceSupport work { queue with terminated := terminal } before := by
  refine ⟨support.tasksRegistered, support.taskProducers, support.streamProducers,
    support.childStreams, ?_⟩
  obtain ⟨announced, inventory, roots⟩ := support.activeRegistration
  exact ⟨announced, ⟨inventory.unique, inventory.registered, inventory.stored,
    inventory.unreleased⟩, roots⟩

-----------------------------------------------------------------------------------------
-- Retained live callbacks cannot depend on discarded successful producers
-----------------------------------------------------------------------------------------

/-- A live task's structural producer succeeded in this exact retained source prefix. -/
theorem SourceSupport.taskProducer
    {work queue before occurrence owners producer payload node}
    (support : SourceSupport work queue before)
    (known : TaskAt work occurrence owners producer payload)
    (found : queue.taskNode? occurrence = some node)
    : ∀ source,
        producer = some source
        → source ∈ before.flatMap ReferenceWorkQueue.GraphEvent.successes := by
  obtain ⟨member, same⟩ := ReferenceWorkQueue.State.taskNode?_some found
  intro source parent
  apply support.taskProducers node.task (support.tasksRegistered node member) source
  refine ⟨owners, payload, ?_⟩
  rw [same, ← parent]
  exact known

/-- An active stream's registered descriptor fixes its successful structural producer.
Generated key uniqueness identifies the source descriptor with that registry entry.
-/
theorem SourceSupport.streamProducer {work queue before stream dependencies producer}
    (support : SourceSupport work queue before)
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (known : NodeAt work stream .stream dependencies producer)
    (active : queue.rootStreams.contains stream.ref = true)
    : ∀ source,
        producer = some source
        → source ∈ before.flatMap ReferenceWorkQueue.GraphEvent.successes := by
  obtain ⟨announced, inventory, roots⟩ := support.activeRegistration
  have registered := inventory.registered (roots (List.contains_iff_mem.mp active))
  obtain ⟨stored, member, sameKey⟩ := List.mem_map.mp registered
  obtain ⟨_, parent, descriptor, succeeded⟩ := support.streamProducers stored member
  have sameProducer := generated.streamProducer_unique descriptor known sameKey
  intro source same
  exact succeeded source (sameProducer.trans same)

/-- Freshness restricts to an ordered retained prefix without strengthening admission. -/
theorem fresh_of_sublist {before retained : List GraphEvent} {event : GraphEvent}
    (fresh : event.Fresh before) (included : retained.Sublist before)
    : event.Fresh retained := by
  refine ⟨fresh.1, fresh.2.1, ?_, ?_⟩
  · intro occurrence member used
    obtain ⟨prior, present, settled⟩ := List.mem_flatMap.mp used
    exact fresh.2.2.1 occurrence member
      (List.mem_flatMap.mpr ⟨prior, included.subset present, settled⟩)
  · intro key member used
    obtain ⟨prior, present, closed⟩ := List.mem_flatMap.mp used
    exact fresh.2.2.2 key member
      (List.mem_flatMap.mpr ⟨prior, included.subset present, closed⟩)

/-- Source readiness transports to the retained prefix: live registration supplies
producer success, item preservation supplies FIFO, and sublisting supplies nonclosure.
The raw source law fixes the original finite result, not any desired queue output.
-/
theorem SourceSupport.ready {work queue before retained event}
    (support : SourceSupport work queue retained)
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (matching : event.MatchesWork work) (ready : event.Ready work before)
    (live : queue.acceptsGraphEvent event = true) (included : retained.Sublist before)
    (items
      : ∀ key,
          ReferenceWorkQueue.GraphEvent.itemsBefore retained key
          = ReferenceWorkQueue.GraphEvent.itemsBefore before key)
    : event.Ready work retained := by
  cases event with
  | taskSuccess occurrence result =>
      obtain ⟨owners, producer, known, _, _⟩ := matching
      cases found : queue.taskNode? occurrence with
      | none => simp [ReferenceWorkQueue.State.acceptsGraphEvent, found] at live
      | some node => exact ⟨owners, producer, _, known, support.taskProducer known found⟩
  | taskFailure occurrence errors =>
      obtain ⟨owners, producer, path, known⟩ := matching
      cases found : queue.taskNode? occurrence with
      | none => simp [ReferenceWorkQueue.State.acceptsGraphEvent, found] at live
      | some node => exact ⟨owners, producer, _, known, support.taskProducer known found⟩
  | streamItems stream values =>
      obtain ⟨address, results, producer, dependencies, known, nonempty, unclosed, _, order⟩ := ready
      refine ⟨address, results, producer, dependencies, known, nonempty, ?_,
        support.streamProducer generated (.stream known) live, ?_⟩
      · intro closed
        obtain ⟨prior, present, key⟩ := List.mem_flatMap.mp closed
        exact unclosed (List.mem_flatMap.mpr ⟨prior, included.subset present, key⟩)
      · rw [items stream.ref]
        exact order
  | streamSuccess stream =>
      obtain ⟨address, results, producer, dependencies, known, _, count⟩ := ready
      exact ⟨
        address,
        results,
        producer,
        dependencies,
        known,
        support.streamProducer generated (.stream known) live,
        by rw [items stream.ref]; exact count
      ⟩
  | streamFailure stream errors =>
      obtain ⟨address, results, producer, dependencies, known, _, failure⟩ := ready
      exact ⟨
        address,
        results,
        producer,
        dependencies,
        known,
        support.streamProducer generated (.stream known) live,
        by rw [items stream.ref]; exact failure
      ⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
