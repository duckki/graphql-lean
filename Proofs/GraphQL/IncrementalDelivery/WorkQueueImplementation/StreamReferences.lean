import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAnnouncements

/-! Stream publications and closures refer to refs announced in their strict output prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Notice-before-reference accounting composes across output segments
-----------------------------------------------------------------------------------------

/-- With the supplied ref projections, each event references only initial or earlier notices.
This proof-only relation remembers prior announcements, not whether a notice remains open.
-/
def ReferencesAnnounced {α : Type} (notices references : α → NodeRefs)
    (initial : NodeRefs)
    : List α → Prop
  | [] => True
  | event :: rest =>
      (references event).Subset initial
      ∧ ReferencesAnnounced notices references (initial ++ notices event) rest

/-- Adding previously known refs preserves notice-before-reference accounting.
Witness: list induction, extending the same initial-ref inclusion with each notice list.
-/
theorem ReferencesAnnounced.mono {α : Type} {notices references : α → NodeRefs}
    {initial enlarged events}
    (known : ReferencesAnnounced notices references initial events)
    (included : initial.Subset enlarged)
    : ReferencesAnnounced notices references enlarged events := by
  induction events generalizing initial enlarged with
  | nil => trivial
  | cons event rest ih =>
      refine ⟨fun _ member => included (known.1 member), ih known.2 ?_⟩
      intro ref member
      rcases List.mem_append.mp member with old | added
      · exact List.mem_append_left _ (included old)
      · exact List.mem_append_right _ added

/-- Output that references only already-known refs satisfies strict-prefix announcement.
Witness: each head uses the original refs; its tail may additionally use that head's notices.
-/
theorem ReferencesAnnounced.of_references {α : Type} {notices references : α → NodeRefs}
    {initial events} (included : (events.flatMap references).Subset initial)
    : ReferencesAnnounced notices references initial events := by
  induction events with
  | nil => trivial
  | cons event rest ih =>
      refine ⟨?_, (ih ?_).mono (fun _ member => List.mem_append_left _ member)⟩
      · intro ref member
        exact included (List.mem_append_left _ member)
      · intro ref member
        exact included (List.mem_append_right _ member)

/-- A later segment may use every notice emitted by the earlier segment.
Witness: peel the earlier events, preserving their order and the accumulated notice refs.
-/
theorem ReferencesAnnounced.append {α : Type} {notices references : α → NodeRefs}
    {initial left right} (before : ReferencesAnnounced notices references initial left)
    (after
      : ReferencesAnnounced notices references (initial ++ left.flatMap notices) right)
    : ReferencesAnnounced notices references initial (left ++ right) := by
  induction left generalizing initial with
  | nil => simpa only [List.flatMap_nil, List.append_nil, List.nil_append] using after
  | cons event rest ih =>
      refine ⟨before.1, ih before.2 ?_⟩
      simpa only [List.flatMap_cons, List.append_assoc] using after

/-- At any selected output event, its references occur in the strict prefix's notice refs.
Witness: index induction through the same ordered notice accumulation.
-/
theorem ReferencesAnnounced.atEvent {α : Type} {notices references : α → NodeRefs}
    {initial events} (known : ReferencesAnnounced notices references initial events)
    {index event} (atEvent : events[index]? = some event)
    : (references event).Subset (initial ++ (events.take index).flatMap notices) := by
  induction events generalizing initial index with
  | nil => simp at atEvent
  | cons head rest ih =>
      cases index with
      | zero =>
          have same : head = event := Option.some.inj atEvent
          subst event
          simpa only [List.take_zero, List.flatMap_nil, List.append_nil] using known.1
      | succ index =>
          have later := ih known.2 atEvent
          simpa only [List.take_succ_cons, List.flatMap_cons, List.append_assoc] using later

/-- Stream refs used by raw value or closure events; newly announced child refs are excluded.
-/
def rawStreamReferenceRefs : WorkQueueEvent → NodeRefs
  | .streamValues stream _ _ _ | .streamSuccess stream | .streamFailure stream _ =>
      [stream.ref]
  | _ => []

/-- Stream refs used by normalized value or closure events, before wire ID allocation.
-/
def streamReferenceRefs : Execution.WorkQueueEvent → NodeRefs
  | .streamValues stream _ _ _ | .streamSuccess stream | .streamFailure stream _ =>
      [stream.ref]
  | _ => []

-----------------------------------------------------------------------------------------
-- A handler references only streams active before that handler
-----------------------------------------------------------------------------------------

/-- Successful group flushes do not reference a stream, even when they announce children.
Witness: the exact flush output contains only group values and group completion.
-/
theorem State.finishGroupSuccess_streamReferences (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).2.1.flatMap rawStreamReferenceRefs = [] := by
  obtain ⟨selected, _, _, events, _, _⟩ := queue.finishGroupSuccess_publications group
  rw [events]
  split <;> simp [rawStreamReferenceRefs]

/-- Task-failure output has no stream reference.
Witness: the contributor loop emits group failures or silently caches group errors.
-/
theorem State.taskFailure_streamReferences (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).2.flatMap rawStreamReferenceRefs = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro event member
  obtain ⟨owner, rfl⟩ := queue.taskFailure_event_failure occurrence errors event member
  rfl

/-- Recursive group draining emits no stream reference, even when it announces new streams.
Witness: successful flushes emit group events; startup notices have a separate component.
-/
theorem State.drainReadyGroups_streamReferences (queue : State)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).2.1.flatMap rawStreamReferenceRefs = [] := by
  have loop (fuel : Nat) (current : State)
      : (State.drainReadyGroups.go available fuel current).2.1.flatMap rawStreamReferenceRefs
          = [] := by
    induction fuel generalizing current with
    | zero => rfl
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · rfl
        · rename_i node selected
          simp only [List.flatMap_append, State.finishGroupSuccess_streamReferences,
            ih, List.nil_append]
  exact loop _ queue

/-- Recursive draining cannot emit a stream-value carrier, even one with no items.
Witness: such a carrier would contribute a ref to the empty stream-reference projection.
-/
theorem State.drainReadyGroups_noStreamValues (queue : State)
    (stream : Execution.DeliveryNode) (values groups streams)
    (available : List (Occurrence × Nat) := [])
    : Execution.WorkQueueEvent.streamValues stream values groups streams
      ∉ (queue.drainReadyGroups available).2.1 := by
  intro emitted
  have impossible
      : stream.ref ∈ (queue.drainReadyGroups available).2.1.flatMap rawStreamReferenceRefs :=
    List.mem_flatMap.mpr ⟨_, emitted, List.mem_cons_self⟩
  rw [State.drainReadyGroups_streamReferences _ available] at impossible
  cases impossible

/-- Task-success output has no stream reference; stream releases are notices only.
Witness: the contributor fold and final drain append only group events.
-/
theorem State.taskSuccess_streamReferences (queue : State) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).2.1.flatMap rawStreamReferenceRefs
      = [] := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      : (groups.foldl successGroupStep acc).2.1.flatMap rawStreamReferenceRefs
        = acc.2.1.flatMap rawStreamReferenceRefs := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih]
        dsimp only [successGroupStep]
        split
        · rfl
        · split
          · simp only [List.flatMap_append, State.finishGroupSuccess_streamReferences,
              List.append_nil]
          · rfl
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      simp only [List.flatMap_append, State.drainReadyGroups_streamReferences _ available,
        List.append_nil]
      exact loop _ (_, [], {})

/-- Every emitted stream reference uses a stream active at the handler's entry.
Witness: task handlers have no references; stream handlers check rootStreams before output.
Even arbitrary unaccepted host events cannot bypass that output guard.
-/
theorem State.handleGraphEvent_streamReferences (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : ((queue.handleGraphEvent event available).2.1.flatMap rawStreamReferenceRefs).Subset
        queue.rootStreams := by
  have roots : (queue.cacheTaskFailures available).rootStreams = queue.rootStreams := by
    have frame := congrArg State.rootStreams (queue.cacheTaskFailures_frame available)
    exact frame
  cases event with
  | taskSuccess occurrence result =>
      rw [State.handleGraphEvent, State.taskSuccess_streamReferences _ _ _ available]
      simp [List.Subset]
  | taskFailure occurrence errors =>
      rw [State.handleGraphEvent, State.taskFailure_streamReferences]
      simp [List.Subset]
  | streamItems stream items =>
      simp only [State.handleGraphEvent, State.streamItems, roots]
      split
      · simp [List.Subset]
      · rename_i active
        simpa [rawStreamReferenceRefs, List.Subset,
          State.drainReadyGroups_streamReferences _ available]
          using active
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess, roots]
      split
      · rename_i active
        simpa [rawStreamReferenceRefs, List.Subset] using active
      · simp [List.Subset]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure, roots]
      split
      · rename_i active
        simpa [rawStreamReferenceRefs, List.Subset] using active
      · simp [List.Subset]

  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · simp [List.Subset]
      · split <;> simp [rawStreamReferenceRefs, List.Subset]

-----------------------------------------------------------------------------------------
-- Raw event replay threads announcement support through every input inside a batch
-----------------------------------------------------------------------------------------

/-- Raw replay references only initially active streams or strictly earlier stream notices.
Witness: each handler uses its entry roots; activation accounting justifies the next roots
from the old roots and the earlier handler's actual output notices.
-/
theorem State.rawEventReplay_streamReferencesAnnounced (queue : State)
    (events : List GraphEvent) (available : List (Occurrence × Nat) := [])
    : ReferencesAnnounced rawStreamNoticeRefs rawStreamReferenceRefs queue.rootStreams
        (queue.rawEventReplay events available).2 := by
  induction events generalizing queue with
  | nil => trivial
  | cons event rest ih =>
      rw [State.rawEventReplay_cons _ _ _ available]
      exact (ReferencesAnnounced.of_references
        (queue.handleGraphEvent_streamReferences event available)).append
        ((ih _).mono (queue.handleGraphEvent_streamRoots event available))

/-- The real batch wrapper preserves prior stream references, including terminal batches.
Witness: terminated input is ignored; appending queue termination adds no reference.
-/
theorem State.handleGraphEvents_streamReferencesAnnounced
    (queue : State) (events : List GraphEvent)
    : ReferencesAnnounced rawStreamNoticeRefs rawStreamReferenceRefs queue.rootStreams
        (queue.handleGraphEvents events).2 := by
  have full := queue.rawEventReplay_streamReferencesAnnounced events
    (GraphEvent.availableFailures events)
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · trivial
  · dsimp only
    split
    · exact full.append ⟨by simp [rawStreamReferenceRefs, List.Subset], trivial⟩
    · exact full

-----------------------------------------------------------------------------------------
-- Normalization preserves prior notices for every stream reference
-----------------------------------------------------------------------------------------

/-- Normalizing an event preserves its stream-reference projection exactly.
Witness: owner selection expands only group values; all stream events remain singletons.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_streamReferences
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap streamReferenceRefs
      = rawStreamReferenceRefs event := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, rawStreamReferenceRefs,
    streamReferenceRefs, List.flatMap_map]

/-- Publisher normalization transports strict-prefix stream announcement without new premises.
Witness: normalize each head with its existing refs, then use its exact stream notices for
the recursively normalized tail. Group-value expansion cannot move a stream reference.
-/
theorem ReferencesAnnounced.normalizeBatch {initial events}
    (announced
      : ReferencesAnnounced rawStreamNoticeRefs rawStreamReferenceRefs initial events)
    (publisher : IncrementalPublisher)
    : ReferencesAnnounced streamNoticeRefs streamReferenceRefs initial
        (publisher.normalizeBatch events).2 := by
  induction events generalizing initial publisher with
  | nil => trivial
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      apply ReferencesAnnounced.append
      · apply ReferencesAnnounced.of_references
        rw [IncrementalPublisher.handleWorkQueueEvent_streamReferences]
        exact announced.1
      · rw [IncrementalPublisher.handleWorkQueueEvent_streamNotices]
        exact ih announced.2 _

/-- One normalized replay step preserves strict-prefix stream-reference support.
Witness: the batch's raw reference law, notice-preserving normalization, and entry-root
accounting compose with the previous output's announcement law.
-/
theorem normalizedStep_streamReferencesAnnounced (acc : NormalizedAcc)
    (batch : List GraphEvent) {initial : NodeRefs}
    (roots
      : acc.1.rootStreams.Subset (initial ++ acc.2.2.flatten.flatMap streamNoticeRefs))
    (announced
      : ReferencesAnnounced streamNoticeRefs streamReferenceRefs initial acc.2.2.flatten)
    : ReferencesAnnounced streamNoticeRefs streamReferenceRefs initial
        (normalizedStep acc batch).2.2.flatten := by
  rw [normalizedStep_flatten]
  exact announced.append
    (((acc.1.handleGraphEvents_streamReferencesAnnounced batch).normalizeBatch acc.2.1).mono
      roots)

/-- All actual normalized stream values and closures have strictly prior stream notices.
Witness: initialization records every active stream; the actual replay fold jointly retains
active-root accounting and notice-before-reference ordering. This holds for arbitrary work
and arbitrary input batches; it does not assert freshness, openness, or full admission.
-/
theorem createWorkQueue_runNormalized_streamReferencesAnnounced (work : Work)
    (batches : List (List GraphEvent))
    : ReferencesAnnounced streamNoticeRefs streamReferenceRefs
        ((State.initialize work).initialStreams.map Execution.DeliveryNode.ref)
        ((State.initialize work).runNormalized batches).2.flatten := by
  let initial := (State.initialize work).initialStreams.map Execution.DeliveryNode.ref
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (roots : acc.1.rootStreams.Subset
        (initial ++ acc.2.2.flatten.flatMap streamNoticeRefs))
      (announced : ReferencesAnnounced streamNoticeRefs streamReferenceRefs initial
        acc.2.2.flatten)
      : ReferencesAnnounced streamNoticeRefs streamReferenceRefs initial
          (more.foldl normalizedStep acc).2.2.flatten := by
    induction more generalizing acc with
    | nil => exact announced
    | cons batch rest ih =>
        exact ih _ (normalizedStep_streamRoots acc batch roots)
          (normalizedStep_streamReferencesAnnounced acc batch roots announced)
  let queue := State.initialize work
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  exact loop batches (queue, publisher, [])
    (by
      intro ref member
      exact List.mem_append_left _ (createWorkQueue_streamRoots work member))
    trivial

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
