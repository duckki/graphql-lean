import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamMetadata

/-! Every emitted stream notice has a structural descriptor in the original work. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every child stream descriptor announced by this raw event satisfies `property`.
References to already-active streams and newly announced groups are deliberately excluded.
-/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.StreamNoticesSatisfy
    (property : Execution.DeliveryNode → Prop) : WorkQueueEvent → Prop
  | .groupSuccess _ _ streams | .streamValues _ _ _ streams =>
      ∀ stream ∈ streams, property stream
  | _ => True

/-- Every child stream descriptor announced by this normalized event satisfies `property`.
-/
def StreamNoticesSatisfy (property : Execution.DeliveryNode → Prop)
    : Execution.WorkQueueEvent → Prop
  | .groupSuccess _ _ streams | .streamValues _ _ _ streams =>
      ∀ stream ∈ streams, property stream
  | _ => True

-----------------------------------------------------------------------------------------
-- Both release paths announce only descriptors justified by their integration state
-----------------------------------------------------------------------------------------

/-- Group-flush output announces only descriptors justified by its entry registry.
Witness: the exact output's sole carrier holds the streams returned by registry lookup.
-/
theorem State.StreamsSatisfy.finishGroupSuccess_output {queue : State} {property}
    (known : queue.StreamsSatisfy property) (group : GroupNode)
    : ∀ event ∈ (queue.finishGroupSuccess group).2.1,
        event.StreamNoticesSatisfy property := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications group
  intro event member
  rw [output] at member
  rcases List.mem_append.mp member with value | carrier
  · split at value
    · cases value
    · have same := List.mem_singleton.mp value
      subst event
      trivial
  · have same := List.mem_singleton.mp carrier
    subst event
    exact known.finishGroupSuccess_notices group

/-- Recursive drain output announces only descriptors justified by the stream registry.
Witness: successful flush notices use registry lookups; failed closures announce nothing,
and cleanup/activation leave that registry unchanged for the rest of the drain.
-/
theorem State.StreamsSatisfy.drainReadyGroups_notices {queue : State} {property}
    (known : queue.StreamsSatisfy property)
    : ∀ event ∈ queue.drainReadyGroups.2, event.StreamNoticesSatisfy property := by
  have loop (fuel : Nat) (current : State) (registry : current.StreamsSatisfy property)
      : ∀ event ∈ (State.drainReadyGroups.go fuel current).2,
          event.StreamNoticesSatisfy property := by
    induction fuel generalizing current with
    | zero => simp [State.drainReadyGroups.go]
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · simp
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              intro event member
              rcases List.mem_append.mp member with first | later
              · exact registry.finishGroupSuccess_output node event first
              · apply ih _ ?_ event later
                intro stream stored
                rw [State.startNewWork_streams, State.finishGroupSuccess_streams] at stored
                exact registry stream stored
          | some errors =>
              intro event member
              rcases List.mem_append.mp member with first | later
              · have same := List.mem_singleton.mp first
                subst event
                trivial
              · exact ih (current.removeGroup node.group.node.key) registry event later
  exact loop _ queue known

/-- Task-success output retains descriptor properties through every contributor flush.
Witness: one loop invariant carries the registry and all emitted notices together; the
task's integration establishes new descriptors before contributor flushes and draining.
-/
theorem State.StreamsSatisfy.taskSuccess_notices {queue : State} {property}
    (known : queue.StreamsSatisfy property) (occurrence : Occurrence)
    (result : TaskResult)
    (supplied : ∀ stream ∈ result.work.streams, property stream.node)
    : ∀ event ∈ (queue.taskSuccess occurrence result).2,
        event.StreamNoticesSatisfy property := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (registry : acc.1.StreamsSatisfy property)
      (notices : ∀ event ∈ acc.2.1, event.StreamNoticesSatisfy property)
      : (groups.foldl successGroupStep acc).1.StreamsSatisfy property
        ∧ ∀ event ∈ (groups.foldl successGroupStep acc).2.1,
            event.StreamNoticesSatisfy property := by
    induction groups generalizing acc with
    | nil => exact ⟨registry, notices⟩
    | cons group rest ih =>
        dsimp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ registry notices
        · rename_i node found
          let decremented := acc.1.putGroupNode { node with pending := node.pending - 1 }
          have updated : decremented.StreamsSatisfy property := registry
          split
          · apply ih
            · intro stream member
              rw [State.finishGroupSuccess_streams] at member
              exact updated stream member
            · intro event member
              rcases List.mem_append.mp member with old | emitted
              · exact notices event old
              · exact updated.finishGroupSuccess_output _ event emitted
          · exact ih _ updated notices
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      have installed : (queue.putTaskNode { node with value := some result.value }).StreamsSatisfy
          property := known
      have integrated := installed.maybeIntegrateWork result.work (some occurrence) supplied
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · intro event impossible
        cases impossible
      obtain ⟨registry, notices⟩ := loop node.task.groups (_, [], {}) integrated.1
        (by intro event impossible; cases impossible)
      intro event member
      rcases List.mem_append.mp member with first | later
      · exact notices event first
      · apply State.StreamsSatisfy.drainReadyGroups_notices ?_ event later
        intro stream stored
        rw [State.startNewWork_streams] at stored
        exact registry stream stored

/-- Item-batch notices retain the properties of each sequentially integrated child stream.
Witness: accumulate released descriptors with the registry invariant; the leading item
event uses its accumulated notices and subsequent drain events use the preserved registry.
-/
theorem State.StreamsSatisfy.streamItems_notices {queue : State} {property}
    (known : queue.StreamsSatisfy property) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (supplied : ∀ item ∈ items, ∀ child ∈ item.work.streams, property child.node)
    : ∀ event ∈ (queue.streamItems stream items).2,
        event.StreamNoticesSatisfy property := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 },
      acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams, acc.2.2.2 ++ [item.value])
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (registry : acc.1.StreamsSatisfy property)
      (notices : ∀ node ∈ acc.2.2.1, property node)
      (inputs : ∀ item ∈ more, ∀ child ∈ item.work.streams, property child.node)
      : (more.foldl step acc).1.StreamsSatisfy property
        ∧ ∀ node ∈ (more.foldl step acc).2.2.1, property node := by
    induction more generalizing acc with
    | nil => exact ⟨registry, notices⟩
    | cons item rest ih =>
        have integrated := registry.maybeIntegrateWork item.work none
          (inputs item List.mem_cons_self)
        apply ih
        · intro child member
          change child ∈ (State.startNewWork
            ((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
              (acc.1.maybeIntegrateWork item.work).2.newGroups).1 _).streams at member
          rw [State.startNewWork_streams, State.pruneEmptyGroups_streams] at member
          exact integrated.1 child member
        · intro node member
          change node ∈ acc.2.2.1 ++ (acc.1.maybeIntegrateWork item.work).2.newStreams at member
          rcases List.mem_append.mp member with old | new
          · exact notices node old
          · exact integrated.2 node new
        · intro next member
          exact inputs next (List.mem_cons_of_mem _ member)
  unfold State.streamItems
  split
  · simp
  · intro event member
    obtain ⟨registry, notices⟩ := loop items (queue, [], [], []) known
      (by intro node impossible; cases impossible) supplied
    rcases List.mem_cons.mp member with same | later
    · subst event
      exact notices
    · exact registry.drainReadyGroups_notices event later

/-- Every handler emits only stream notices justified by its old or supplied descriptors.
Witness: task/item release proofs; failure and closure handlers announce no streams.
-/
theorem State.StreamsSatisfy.handleGraphEvent_notices {queue : State} {property}
    (known : queue.StreamsSatisfy property) (event : GraphEvent)
    (supplied : event.ChildStreamsSatisfy property)
    : ∀ output ∈ (queue.handleGraphEvent event).2,
        output.StreamNoticesSatisfy property := by
  cases event with
  | taskSuccess occurrence result =>
      exact known.taskSuccess_notices occurrence result supplied
  | taskFailure occurrence errors =>
      intro output member
      cases output with
      | groupSuccess group groups streams =>
          exact False.elim (queue.taskFailure_noGroupSuccess occurrence errors group groups streams
            member)
      | streamValues stream values groups streams =>
          have impossible : stream.key ∈
              (queue.taskFailure occurrence errors).2.flatMap rawStreamReferenceKeys :=
            List.mem_flatMap.mpr ⟨_, member, List.mem_cons_self⟩
          rw [State.taskFailure_streamReferences] at impossible
          cases impossible
      | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination
        =>
          trivial
  | streamItems stream items => exact known.streamItems_notices stream items supplied
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [WorkQueueEvent.StreamNoticesSatisfy]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [WorkQueueEvent.StreamNoticesSatisfy]

-----------------------------------------------------------------------------------------
-- Event replay, normalization, and atomization retain all stream notice metadata
-----------------------------------------------------------------------------------------

/-- Raw event replay emits only stream notices justified by retained or supplied descriptors.
Witness: each next handler inherits the updated registry and the remaining source metadata.
-/
theorem State.StreamsSatisfy.rawEventReplay_notices {queue : State} {property}
    (known : queue.StreamsSatisfy property) (events : List GraphEvent)
    (supplied : ∀ event ∈ events, event.ChildStreamsSatisfy property)
    : ∀ output ∈ (queue.rawEventReplay events).2,
        output.StreamNoticesSatisfy property := by
  induction events generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      intro output member
      rcases List.mem_append.mp member with head | tail
      · exact known.handleGraphEvent_notices event (supplied event List.mem_cons_self)
          output head
      · exact ih (known.handleGraphEvent event (supplied event List.mem_cons_self))
          (fun next member => supplied next (List.mem_cons_of_mem _ member)) output tail

/-- A whole raw batch emits only justified stream notices, including at termination.
Witness: raw replay retains metadata; the optional terminal marker adds no notice.
-/
theorem State.StreamsSatisfy.handleGraphEvents_notices {queue : State} {property}
    (known : queue.StreamsSatisfy property) (events : List GraphEvent)
    (supplied : ∀ event ∈ events, event.ChildStreamsSatisfy property)
    : ∀ output ∈ (queue.handleGraphEvents events).2,
        output.StreamNoticesSatisfy property := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · simp
  · dsimp only
    split
    · intro output member
      rcases List.mem_append.mp member with prior | terminal
      · exact known.rawEventReplay_notices events supplied output prior
      · have same := List.mem_singleton.mp terminal
        subst output
        trivial
    · exact known.rawEventReplay_notices events supplied

/-- Normalizing a raw event preserves every stream-notice descriptor property.
Witness: the publisher copies notice lists unchanged; owner remapping emits only group values.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_streamNoticesSatisfy
    {property}
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    (known : event.StreamNoticesSatisfy property)
    : ∀ output ∈ (publisher.handleWorkQueueEvent event).2,
        StreamNoticesSatisfy property output := by
  cases event <;> simp_all [IncrementalPublisher.handleWorkQueueEvent,
    WorkQueueEvent.StreamNoticesSatisfy, StreamNoticesSatisfy]

/-- Stateful batch normalization preserves stream-notice metadata in all output events.
Witness: apply the one-event result before recursively normalizing the remaining batch.
-/
theorem IncrementalPublisher.normalizeBatch_streamNoticesSatisfy {property}
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    (known : ∀ event ∈ events, event.StreamNoticesSatisfy property)
    : ∀ output ∈ (publisher.normalizeBatch events).2,
        StreamNoticesSatisfy property output := by
  induction events generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      intro output member
      rcases List.mem_append.mp member with head | tail
      · exact publisher.handleWorkQueueEvent_streamNoticesSatisfy event
          (known event List.mem_cons_self) output head
      · exact ih _ (fun next member => known next (List.mem_cons_of_mem _ member)) output tail

/-- Every stream notice in actual normalized replay names a node of the original work.
Witness: integrate exact source child descriptors, retain registry provenance at every
handler boundary, and transport each emitted notice through publisher normalization.
No generated-key uniqueness, start law, or abstract admission premise is assumed.
-/
theorem createWorkQueue_runNormalized_streamNoticesLocated {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ∀ event ∈
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten,
        StreamNoticesSatisfy (StreamLocated work) event := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (registry : acc.1.StreamsSatisfy (StreamLocated work))
      (notices : ∀ event ∈ acc.2.2.flatten, StreamNoticesSatisfy (StreamLocated work) event)
      (sources : ∀ event ∈ more.flatten, event.MatchesWork work)
      : ∀ event ∈ (more.foldl normalizedStep acc).2.2.flatten,
          StreamNoticesSatisfy (StreamLocated work) event := by
    induction more generalizing acc with
    | nil => exact notices
    | cons batch rest ih =>
        have supplied : ∀ event ∈ batch, event.ChildStreamsSatisfy (StreamLocated work) :=
          fun event member => (sources event (List.mem_append_left _ member)).childStreamsLocated
        apply ih
        · rw [normalizedStep_queue]
          exact registry.handleGraphEvents batch supplied
        · rw [normalizedStep_flatten]
          intro event member
          rcases List.mem_append.mp member with prior | next
          · exact notices event prior
          · exact acc.2.1.normalizeBatch_streamNoticesSatisfy _
              (registry.handleGraphEvents_notices batch supplied) event next
        · intro event member
          exact sources event (List.mem_append_right _ member)
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  apply loop batches (queue, publisher, [])
  · intro stream member
    exact ⟨[], none, (createWorkQueue_initialStreams_nodeAt work).1 stream member⟩
  · intro event impossible; cases impossible
  · intro event member; exact valid.event_matches member

/-- Atomic splitting retains the property of every child stream notice.
Witness: object atoms have no notices, and earlier stream atoms have none; the final stream
atom and unchanged control events retain their original child lists.
-/
theorem publicationAtoms_streamNoticesSatisfy {property}
    (event : Execution.WorkQueueEvent) (known : StreamNoticesSatisfy property event)
    : ∀ atom ∈ publicationAtoms event, StreamNoticesSatisfy property atom := by
  cases event with
  | groupValues group values => simp [publicationAtoms, StreamNoticesSatisfy]
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => simp [publicationAtoms, streamPublicationAtoms]
      | case2 =>
          simpa [publicationAtoms, streamPublicationAtoms, StreamNoticesSatisfy] using known
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, StreamNoticesSatisfy] using ih known
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simpa [publicationAtoms] using known

/-- Every stream notice in the actual atomic history retains its structural metadata.
Witness: actual normalized notice provenance followed by notice-preserving atomization.
-/
theorem createWorkQueue_runNormalized_atomicStreamNoticesLocated {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ∀ event ∈
        (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms),
        StreamNoticesSatisfy (StreamLocated work) event := by
  intro event member
  obtain ⟨original, emitted, atom⟩ := List.mem_flatMap.mp member
  exact publicationAtoms_streamNoticesSatisfy original
    (createWorkQueue_runNormalized_streamNoticesLocated valid original emitted) event atom

-----------------------------------------------------------------------------------------
-- The joint matching now supplies stream-release metadata rather than requiring it
-----------------------------------------------------------------------------------------

/-- One actual-output matching gives fresh ordered values and locates every group-released
stream with its already-published structural producer.
Witness: combine the same joint release matching with universal stream-notice metadata;
the latter is matching-independent, so no new occurrence choice or source premise is made.
This still leaves item-produced notice readiness, later reference readiness, cancellation,
owner/notice licensing, and terminal accounting before a full Explains witness.
-/
theorem createWorkQueue_runNormalized_locatedStreamReleaseMatching {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (atoms.take index) (matching index)
              ∧ ∀ address first second,
                  matching index = .item address second
                  → first < second
                  → Published matching (atoms.take index) (.item address first))
        ∧ (∀ index group groups streams,
            atoms[index]? = some (.groupSuccess group groups streams)
            → ∀ stream ∈ streams,
                ∃ dependencies occurrence,
                  NodeAt work stream .stream dependencies (some occurrence)
                  ∧ Published matching (atoms.take index) occurrence) := by
  obtain ⟨matching, batching, values, release⟩ :=
    createWorkQueue_runNormalized_streamReleaseMatching generated valid started
  refine ⟨matching, batching, values, ?_⟩
  intro index group groups streams atEvent stream member
  obtain ⟨dependencies, producer, located⟩ :=
    createWorkQueue_runNormalized_atomicStreamNoticesLocated valid _
      (List.mem_of_getElem? atEvent) stream member
  obtain ⟨occurrence, same, published⟩ :=
    release index group groups streams atEvent stream member dependencies producer located
  exact ⟨dependencies, occurrence, same ▸ located, published⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
