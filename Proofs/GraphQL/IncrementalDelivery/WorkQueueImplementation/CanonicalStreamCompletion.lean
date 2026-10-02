import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalGroupCompletion

/-! Stream and combined announced-node completion on the canonical conformance history. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Stream notices and closures retain their exact inventories through publication
-----------------------------------------------------------------------------------------

/-- Stream keys completed by a normalized event, excluding group completions. -/
def streamClosureKeys : Execution.WorkQueueEvent → Keys
  | .streamSuccess stream | .streamFailure stream _ => [stream.key]
  | _ => []

/-- Publisher normalization preserves stream completions in their original order.
Witness: only stream success/failure events contribute a key and each is copied unchanged.
-/
theorem IncrementalPublisher.normalizeBatch_streamClosureKeys
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.flatMap streamClosureKeys
      = events.flatMap rawStreamClosureKeys := by
  have single (current : IncrementalPublisher) (event : WorkQueueEvent)
      : (current.handleWorkQueueEvent event).2.flatMap streamClosureKeys
        = rawStreamClosureKeys event := by
    cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, streamClosureKeys,
      rawStreamClosureKeys, List.flatMap_map]
  induction events generalizing publisher with
  | nil => rfl
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      simp only [List.flatMap_append, single, ih, List.flatMap_cons]

/-- Atomic expansion preserves all stream completions, independently of payload length.
Witness: value atoms cannot close streams and control events remain singletons.
-/
theorem publicationAtoms_streamClosureKeys (event : Execution.WorkQueueEvent)
    : (publicationAtoms event).flatMap streamClosureKeys = streamClosureKeys event := by
  cases event with
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => rfl
      | case2 => rfl
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, streamClosureKeys] using ih
  | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
    | workQueueTermination => simp [publicationAtoms, streamClosureKeys, List.flatMap_map]

/-- Normalizing and atomizing legal raw output retains its exact stream-notice inventory.
Witness: nonempty payload preservation plus the publisher's unchanged notice lists.
-/
theorem atomicStreamNotices (publisher : IncrementalPublisher)
    (events : List WorkQueueEvent) (nonempty : ∀ event ∈ events, event.NonemptyValues)
    : ((publisher.normalizeBatch events).2.flatMap publicationAtoms).flatMap
        streamNoticeKeys
      = events.flatMap rawStreamNoticeKeys := by
  have expand (outputs : List Execution.WorkQueueEvent)
      (shape : ∀ event ∈ outputs, NonemptyValues event)
      : (outputs.flatMap publicationAtoms).flatMap streamNoticeKeys
        = outputs.flatMap streamNoticeKeys := by
    induction outputs with
    | nil => rfl
    | cons event rest ih =>
        simp only [List.flatMap_cons, List.flatMap_append,
          publicationAtoms_streamNotices event (shape event List.mem_cons_self),
          ih (fun next member => shape next (List.mem_cons_of_mem _ member))]
  rw [expand _ (publisher.normalizeBatch_nonemptyValues events nonempty).2,
    IncrementalPublisher.normalizeBatch_streamNotices]

/-- Every stream-only closure is a scheduler completion.
Witness: both stream-close constructors contribute the same key to eventCompleted.
-/
theorem streamClosureKeys_subset_completed (events : List Execution.WorkQueueEvent)
    : (events.flatMap streamClosureKeys).Subset (completedKeys events) := by
  intro key member
  obtain ⟨event, emitted, closed⟩ := List.mem_flatMap.mp member
  refine List.mem_flatMap.mpr ⟨event, emitted, ?_⟩
  cases event <;> simp_all [streamClosureKeys, eventCompleted]

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- All announced nodes complete when the actual queue terminates
-----------------------------------------------------------------------------------------

/-- Every initial or carried stream notice completes in a terminated canonical history.
Witness: exact raw stream tracking, empty final roots, and both publisher inventory bridges.
No generated-work or abstract output-admission premise is required for the stream case.
-/
theorem streamNoticeKeys_terminalCompleted {work inputs key} {w : Witness}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (noticed
      : key
        ∈ (initialQueue work).initialStreams.map Execution.DeliveryNode.key
          ++ w.events.flatMap streamNoticeKeys)
    : key ∈ completedKeys w.events := by
  have exactHistory := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  have notices
      : w.events.flatMap streamNoticeKeys
        = ((initialQueue work).rawEventReplay inputs.flatten).2.flatMap rawStreamNoticeKeys := by
    rw [exactHistory, atomicStreamNotices _ _
      ((initialQueue work).rawEventReplay_nonemptyValues inputs.flatten valid.nonemptyItems)]
  have closures
      : w.events.flatMap streamClosureKeys
        = ((initialQueue work).rawEventReplay inputs.flatten).2.flatMap rawStreamClosureKeys := by
    rw [exactHistory, List.flatMap_assoc]
    simp only [publicationAtoms_streamClosureKeys,
      IncrementalPublisher.normalizeBatch_streamClosureKeys]
  rw [notices] at noticed
  have closed := createWorkQueue_terminalStreamCompleted started ended noticed
  apply streamClosureKeys_subset_completed
  rwa [closures]

/-- Every announced key, group or stream, actually completes when canonical replay ends.
Witness: split actual notices by their two carrier lists and combine concrete group and
stream completion. No lifecycle checker, scheduler admission, or terminal accounting is
assumed, so this can discharge the announced branch of the conformance node leaf.
-/
theorem announced_terminalCompleted {work inputs key} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (announced : key ∈ announcedKeys (initialKeys work) w.events)
    : key ∈ completedKeys w.events := by
  have groupDone
      (noticed : key ∈ (initialQueue work).rootGroups ++ w.events.flatMap groupNoticeKeys)
      : key ∈ completedKeys w.events := by
    rcases groupNoticeKeys_tracked generated valid started history key noticed with active | closed
    · have empty := (createWorkQueue_terminalRoots (Work.fromExecution work) inputs ended).1
      rw [empty] at active
      cases active
    · exact groupClosureKeys_subset_completed w.events closed
  have streamDone := streamNoticeKeys_terminalCompleted (key := key) valid started history ended
  rcases List.mem_append.mp announced with initial | carried
  · rw [initialKeys, List.map_append] at initial
    rcases List.mem_append.mp initial with group | stream
    · apply groupDone
      apply List.mem_append_left
      rwa [createWorkQueue_rootGroups]
    · exact streamDone (List.mem_append_left _ stream)
  · obtain ⟨event, emitted, noticed⟩ := List.mem_flatMap.mp carried
    cases event <;> simp only [eventPending] at noticed
    case groupSuccess owner groups streams | streamValues owner values groups streams =>
      rw [List.map_append] at noticed
      rcases List.mem_append.mp noticed with group | stream
      · exact groupDone (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, emitted, group⟩))
      · exact streamDone (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, emitted, stream⟩))
    all_goals cases noticed

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
