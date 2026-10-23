import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingFailureFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainClosureBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Closing descriptors retain registration-record provenance for arbitrary raw work. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A raw group completion uses a registration descriptor; other events are unchecked.
This alone does not prove contributor status; taskless ancestor records are also permitted.
-/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.GroupClosureRecordLocated
    (work : Execution.Work) : WorkQueueEvent → Prop
  | .groupSuccess group _ _ | .groupFailure group _ =>
      ∃ dependencies, GroupRecordAt work group dependencies
  | _ => True

/-- The normalized counterpart checks only successful and failed group-closing descriptors.
-/
def GroupClosureRecordLocated (work : Execution.Work) : Execution.WorkQueueEvent → Prop
  | .groupSuccess group _ _ | .groupFailure group _ =>
      ∃ dependencies, GroupRecordAt work group dependencies
  | _ => True

-----------------------------------------------------------------------------------------
-- Success and failure handlers close only group nodes found in their actual registry
-----------------------------------------------------------------------------------------

/-- A group flush closes precisely its supplied group, retaining that node's provenance.
Witness: the exact flush output has only object values followed by this group completion.
-/
theorem State.finishGroupSuccess_groupClosureRecordLocated {work : Execution.Work}
    (queue : State) (group : GroupNode)
    (known : ∃ dependencies, GroupRecordAt work group.group.node dependencies)
    : ∀ event ∈ (queue.finishGroupSuccess group).2.1,
        event.GroupClosureRecordLocated work := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications group
  intro event member
  rw [output] at member
  rcases List.mem_append.mp member with value | closure
  · split at value
    · cases value
    · have same := List.mem_singleton.mp value
      subst event
      trivial
  · have same := List.mem_singleton.mp closure
    subst event
    exact known

/-- Task failure closes only looked-up groups; cached latent errors add no event.
Witness: retain registry provenance through initial task removal and every owner branch.
-/
theorem State.GroupNodesMatchWork.taskFailure_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (occurrence : Occurrence) (errors : Nat)
    : ∀ event ∈ (queue.taskFailure occurrence errors).2,
        event.GroupClosureRecordLocated work := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [WorkQueueEvent.groupFailure failure.group failure.errors])
        else acc
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (known : acc.1.GroupNodesMatchWork work)
      (output : ∀ event ∈ acc.2, event.GroupClosureRecordLocated work)
      : ∀ event ∈ (groups.foldl step acc).2, event.GroupClosureRecordLocated work := by
    induction groups generalizing acc with
    | nil => exact output
    | cons group rest ih =>
        rw [List.foldl_cons]
        unfold step
        split
        · exact ih _ known output
        · rename_i node found
          have located := known node (List.mem_of_find?_eq_some found)
          split
          · apply ih _ (known.finishGroupFailure node errors)
            intro event member
            rcases List.mem_append.mp member with earlier | closed
            · exact output event earlier
            · have same := List.mem_singleton.mp closed
              subst event
              exact located
          · exact ih _ known output
  unfold State.taskFailure
  split
  · simp
  · exact loop _ (_, []) registered (by intro event impossible; cases impossible)

/-- A startup failure retains the looked-up registration descriptor before removal.
Witness: the local notice copies the selected group's descriptor exactly.
-/
theorem State.GroupNodesMatchWork.startGroup_failureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (ref : NodeRef) (available : List (Occurrence × Nat) := [])
    : ∀ failure ∈ (queue.startGroup ref available).2,
        ∃ dependencies, GroupRecordAt work failure.group dependencies := by
  have cached := registered.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · simp
  · rename_i node found
    split
    · simp
    · intro failure member
      have same := List.mem_singleton.mp member
      subst failure
      exact cached node (List.mem_of_find?_eq_some found)

/-- The startup fold preserves descriptor provenance for every queued failure.
Witness: each notice is justified before that group is removed; surviving registry records
justify the next startup step. Stream activation leaves the local notice list unchanged.
-/
theorem State.GroupNodesMatchWork.startNewWork_failureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (released : NewWork) (available : List (Occurrence × Nat) := [])
    : ∀ failure ∈ (queue.startNewWork released available).2,
        ∃ dependencies, GroupRecordAt work failure.group dependencies := by
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let (next, queued) := acc.1.startGroup ref available
    (next, acc.2 ++ queued)
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (registry : acc.1.GroupNodesMatchWork work)
      (known : ∀ failure ∈ acc.2,
        ∃ dependencies, GroupRecordAt work failure.group dependencies)
      : ∀ failure ∈ (refs.foldl step acc).2,
          ∃ dependencies, GroupRecordAt work failure.group dependencies := by
    induction refs generalizing acc with
    | nil => exact known
    | cons ref rest ih =>
        apply ih
        · intro node member
          exact registry node ((acc.1.startGroup_groupNodes_sublist ref available).subset member)
        · intro failure member
          exact (List.mem_append.mp member).elim (known failure)
            (registry.startGroup_failureRecords ref available failure)
  exact loop _ (_, []) registered (by simp)

/-- Immediate and queued completions both retain registration descriptors. -/
private def ClosureRecords (work : Execution.Work)
    (result : State × List WorkQueueEvent × List GroupFailureEvent)
    : Prop :=
  (∀ event ∈ result.2.1, event.GroupClosureRecordLocated work)
  ∧ ∀ failure ∈ result.2.2, ∃ dependencies, GroupRecordAt work failure.group dependencies

/-- Recursive draining retains descriptors for successful and queued failed completions.
Witness: a successful lookup justifies the flush; activation collects its own descriptor
witnesses before removal, and the surviving registry justifies recursion.
-/
theorem State.GroupNodesMatchWork.drainReadyGroups_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (available : List (Occurrence × Nat) := [])
    : ClosureRecords work (queue.drainReadyGroups available) := by
  have loop (fuel : Nat) (current : State) (registry : current.GroupNodesMatchWork work)
      : ClosureRecords work (State.drainReadyGroups.go available fuel current) := by
    induction fuel generalizing current with
    | zero =>
        exact ⟨by simp [State.drainReadyGroups.go], by simp [State.drainReadyGroups.go]⟩
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact ⟨by simp, by simp⟩
        · rename_i node selected
          have found := State.readyGroup_sound selected
          have located := registry node (List.mem_of_find?_eq_some found.1)
          have retained := (registry.finishGroupSuccess node).startNewWork
            (current.finishGroupSuccess node).2.2 available
          have queued := (registry.finishGroupSuccess node).startNewWork_failureRecords
            (current.finishGroupSuccess node).2.2 available
          obtain ⟨outputs, later⟩ := ih _ retained
          exact ⟨fun event member => (List.mem_append.mp member).elim
              (current.finishGroupSuccess_groupClosureRecordLocated node located event)
              (outputs event),
            fun failure member => (List.mem_append.mp member).elim
              (queued failure) (later failure)⟩
  exact loop _ queue registered

/-- Task success closes only groups with registration descriptors from its integration state.
Witness: the actual single-pass contributor fold looks up each closing node, while the
registry invariant survives decrements, flushes, integration, and the final recursive drain.
-/
theorem State.GroupNodesMatchWork.taskSuccess_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    {occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ClosureRecords work (queue.taskSuccess occurrence result available) := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (known : acc.1.GroupNodesMatchWork work)
      (output : ∀ event ∈ acc.2.1, event.GroupClosureRecordLocated work)
      : (groups.foldl successGroupStep acc).1.GroupNodesMatchWork work
        ∧ ∀ event ∈ (groups.foldl successGroupStep acc).2.1,
            event.GroupClosureRecordLocated work := by
    induction groups generalizing acc with
    | nil => exact ⟨known, output⟩
    | cons group rest ih =>
        dsimp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ known output
        · rename_i node found
          have located := known node (List.mem_of_find?_eq_some found)
          have updated := known.putGroupNode { node with pending := node.pending - 1 } located
          split
          · apply ih
            · exact updated.finishGroupSuccess _
            · intro event member
              rcases List.mem_append.mp member with earlier | closed
              · exact output event earlier
              · exact State.finishGroupSuccess_groupClosureRecordLocated _ _ located event closed
          · exact ih _ updated output
  cases found : queue.taskNode? occurrence with
  | none => exact ⟨by simp [State.taskSuccess, found], by simp [State.taskSuccess, found]⟩
  | some node =>
      have installed : State.GroupNodesMatchWork
          (queue.putTaskNode { node with value := some result.value }) work := registered
      have integrated := installed.maybeIntegrateWork result.work
        (fun group member => matching.taskChildGroups_recordAt member) (some occurrence)
      rw [queue.taskSuccess_eq occurrence result node found available]
      obtain ⟨registry, output⟩ := loop node.task.groups (_, [], {}) integrated
        (by intro event impossible; cases impossible)
      let folded := node.task.groups.foldl successGroupStep
        (((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1, [], {})
      have queued := registry.startNewWork_failureRecords folded.2.2 available
      obtain ⟨drained, later⟩ :=
        (registry.startNewWork folded.2.2 available).drainReadyGroups_groupClosureRecords available
      exact ⟨fun event member => (List.mem_append.mp member).elim
          (output event) (drained event),
        fun failure member => (List.mem_append.mp member).elim
          (queued failure) (later failure)⟩

/-- An item handler's final drain closes only groups located in its integration state.
Witness: each matched item's child work preserves registry provenance before the drain;
the leading stream-value event itself closes no group.
-/
theorem State.GroupNodesMatchWork.streamItems_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ClosureRecords work (queue.streamItems stream items available) := by
  have loop (more : List StreamItem) (subset : more.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue × List GroupFailureEvent)
      (prior : acc.1.GroupNodesMatchWork work)
      (queued : ∀ failure ∈ acc.2.2.2.2,
        ∃ dependencies, GroupRecordAt work failure.group dependencies)
      : State.GroupNodesMatchWork
          (more.foldl (fun acc item => streamItemStep acc item available) acc).1 work
        ∧ ∀ failure ∈ (more.foldl
            (fun acc item => streamItemStep acc item available) acc).2.2.2.2,
            ∃ dependencies, GroupRecordAt work failure.group dependencies := by
    induction more generalizing acc with
    | nil => exact ⟨prior, queued⟩
    | cons item rest ih =>
        let integratedWork := acc.1.maybeIntegrateWork item.work
        let pruned := integratedWork.1.pruneEmptyGroups integratedWork.2.newGroups
        let released : NewWork := { integratedWork.2 with newGroups := pruned.2 }
        have integrated := (prior.maybeIntegrateWork item.work
          (fun group member => matching.streamItem_childGroups_recordAt
            (subset List.mem_cons_self) member)).pruneEmptyGroups integratedWork.2.newGroups
        apply ih (fun _ member => subset (List.mem_cons_of_mem _ member))
        · exact integrated.startNewWork released available
        · intro failure member
          exact (List.mem_append.mp member).elim (queued failure)
            (integrated.startNewWork_failureRecords released available failure)
  rw [queue.streamItems_eq stream items available]
  split
  · exact ⟨by simp, by simp⟩
  · obtain ⟨registry, queued⟩ := loop items (fun _ member => member)
      (queue, [], [], [], []) registered (by simp)
    obtain ⟨outputs, later⟩ := registry.drainReadyGroups_groupClosureRecords available
    refine ⟨?_, fun failure member => (List.mem_append.mp member).elim
      (queued failure) (later failure)⟩
    intro event member
    rcases List.mem_cons.mp member with same | rest
    · subst event; trivial
    · exact outputs event rest

/-- Pending controls retain descriptors from the registry at their enqueue transition. -/
def State.QueuedGroupRecords (queue : State) (work : Execution.Work) : Prop :=
  ∀ failure ∈ queue.groupFailureEvents,
    ∃ dependencies, GroupRecordAt work failure.group dependencies

/-- Each matching handler emits group completions only for known registration records.
Witness: task handlers and item-triggered drains retain provenance; stream closures add none.
-/
theorem State.GroupNodesMatchWork.handleGraphEvent_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (queued : queue.QueuedGroupRecords work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ClosureRecords work (queue.handleGraphEvent event available) := by
  have cached := registered.cacheTaskFailures available
  cases event with
  | taskSuccess => exact cached.taskSuccess_groupClosureRecords matching available
  | taskFailure occurrence errors =>
      exact ⟨
        cached.taskFailure_groupClosureRecords occurrence errors,
        by simp [State.handleGraphEvent]
      ⟩
  | streamItems stream items =>
      exact cached.streamItems_groupClosureRecords matching available
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [ClosureRecords, WorkQueueEvent.GroupClosureRecordLocated]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [ClosureRecords, WorkQueueEvent.GroupClosureRecordLocated]

  | groupFailure supplied =>
      refine ⟨?_, by simp [State.handleGraphEvent]⟩
      intro output emitted
      cases output <;> try trivial
      case groupSuccess group groups streams =>
        simp only [State.handleGraphEvent, State.groupFailure] at emitted
        split at emitted
        · cases emitted
        · split at emitted <;> simp at emitted
      case groupFailure group errors =>
        obtain ⟨rest, head⟩ := (queue.cacheTaskFailures available).groupFailure_origin supplied emitted
        rw [State.cacheTaskFailures_groupFailureEvents] at head
        exact queued ⟨group, errors⟩ (by rw [head]; exact List.mem_cons_self)

-----------------------------------------------------------------------------------------
-- Preserve closing-node provenance through replay, normalization, and atomic expansion
-----------------------------------------------------------------------------------------

/-- Dispatch retains descriptor evidence after consuming or appending internal controls. -/
theorem State.GroupNodesMatchWork.dispatchGraphEvent_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (queued : queue.QueuedGroupRecords work) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : (queue.dispatchGraphEvent event available).1.QueuedGroupRecords work
      ∧ ∀ output ∈ (queue.dispatchGraphEvent event available).2,
          output.GroupClosureRecordLocated work := by
  have localFacts := registered.handleGraphEvent_groupClosureRecords queued event matching available
  refine ⟨?_, localFacts.1⟩
  intro failure member
  change failure ∈ (queue.handleGraphEvent event available).1.groupFailureEvents
    ++ (queue.handleGraphEvent event available).2.2 at member
  exact (List.mem_append.mp member).elim
    (fun old => queued failure (queue.handleGraphEvent_groupFailureEvents_subset event available old))
    (localFacts.2 failure)

/-- Realized FIFO replay retains both queued and emitted closing-node provenance. -/
theorem State.GroupNodesMatchWork.rawEventReplay_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (queued : queue.QueuedGroupRecords work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.rawEventReplay events available).1.QueuedGroupRecords work
      ∧ ∀ output ∈ (queue.rawEventReplay events available).2,
          output.GroupClosureRecordLocated work := by
  induction events generalizing queue with
  | nil => exact ⟨queued, by simp [State.rawEventReplay]⟩
  | cons event rest ih =>
      have matched := matching event List.mem_cons_self
      have current := registered.dispatchGraphEvent_groupClosureRecords queued event matched available
      have next : (queue.dispatchGraphEvent event available).1.GroupNodesMatchWork work :=
        registered.handleGraphEvent event matched available
      obtain ⟨waiting, later⟩ := ih next current.1
        (fun next member => matching next (List.mem_cons_of_mem _ member))
      rw [State.rawEventReplay_cons queue event rest available]
      exact ⟨waiting, fun output member => (List.mem_append.mp member).elim
        (current.2 output) (later output)⟩

/-- Batch termination retains queued descriptors and adds no closing group descriptor. -/
theorem State.GroupNodesMatchWork.handleGraphEvents_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (queued : queue.QueuedGroupRecords work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.QueuedGroupRecords work
      ∧ ∀ output ∈ (queue.handleGraphEvents events).2,
          output.GroupClosureRecordLocated work := by
  have raw := registered.rawEventReplay_groupClosureRecords queued events matching
    (GraphEvent.availableFailures events)
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact ⟨queued, by simp⟩
  · dsimp only
    split
    · refine ⟨raw.1, ?_⟩
      intro output member
      rcases List.mem_append.mp member with earlier | terminal
      · exact raw.2 output earlier
      · obtain rfl := List.mem_singleton.mp terminal
        trivial
    · exact raw

/-- Publisher normalization cannot change a closing group's descriptor.
Witness: closure constructors are copied; group-value owner remapping creates no closure.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_groupClosureRecords {work event}
    (publisher : IncrementalPublisher)
    (known : WorkQueueEvent.GroupClosureRecordLocated work event)
    : ∀ output ∈ (publisher.handleWorkQueueEvent event).2,
        GroupClosureRecordLocated work output := by
  cases event <;> simp_all [IncrementalPublisher.handleWorkQueueEvent,
    GroupClosureRecordLocated, WorkQueueEvent.GroupClosureRecordLocated]

/-- The normalized batch retains every raw closing group's structural descriptor.
Witness: append the unchanged closing nodes throughout the actual publisher fold.
-/
theorem IncrementalPublisher.normalizeBatch_groupClosureRecords {work events}
    (publisher : IncrementalPublisher)
    (known : ∀ event ∈ events, WorkQueueEvent.GroupClosureRecordLocated work event)
    : ∀ output ∈ (publisher.normalizeBatch events).2,
        GroupClosureRecordLocated work output := by
  induction events generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      intro output member
      rcases List.mem_append.mp member with first | later
      · exact publisher.handleWorkQueueEvent_groupClosureRecords (known event List.mem_cons_self)
          output first
      · exact ih _ (fun next member => known next (List.mem_cons_of_mem _ member)) output later

/-- Every group closure in actual normalized output has a registration descriptor.
Witness: joint registry/output induction through real input batching and normalization,
initialized by the work-lowering provenance theorem. Only matched source payloads are used.
-/
theorem createWorkQueue_runNormalized_groupClosureRecordsLocated {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ∀ event ∈
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten,
        GroupClosureRecordLocated work event := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (registry : acc.1.GroupNodesMatchWork work)
      (queued : acc.1.QueuedGroupRecords work)
      (output : ∀ event ∈ acc.2.2.flatten, GroupClosureRecordLocated work event)
      (matching : ∀ batch ∈ more, ∀ event ∈ batch, event.MatchesWork work)
      : ∀ event ∈ (more.foldl normalizedStep acc).2.2.flatten,
          GroupClosureRecordLocated work event := by
    induction more generalizing acc with
    | nil => exact output
    | cons batch rest ih =>
        have batchMatch := matching batch List.mem_cons_self
        rw [List.foldl_cons]
        apply ih
        · rw [normalizedStep_queue]
          exact registry.handleGraphEvents batch batchMatch
        · rw [normalizedStep_queue]
          exact (registry.handleGraphEvents_groupClosureRecords queued batch batchMatch).1
        · have emitted := acc.2.1.normalizeBatch_groupClosureRecords
            (registry.handleGraphEvents_groupClosureRecords queued batch batchMatch).2
          dsimp only [normalizedStep]
          split
          · exact output
          · intro event member
            simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
              List.append_nil, List.mem_append] at member
            exact member.elim (output event) (emitted event)
        · exact fun batch member => matching batch (List.mem_cons_of_mem _ member)
  exact loop batches
    (_, _, [])
    (createWorkQueue_groupNodesMatchWork work)
    (by
      intro failure member; rw [State.initialize_groupFailureEvents] at member; cases member)
    (by simp)
    (fun batch member event within =>
      valid.eachMatches (List.mem_flatten.mpr ⟨batch, member, within⟩))

/-- Splitting values preserves closing-node provenance because it introduces no closures.
Witness: object/item expansion has only value atoms; control events stay unchanged.
-/
theorem GroupClosureRecordLocated.atoms {work event}
    (known : GroupClosureRecordLocated work event)
    : ∀ atom ∈ publicationAtoms event, GroupClosureRecordLocated work atom := by
  cases event with
  | groupValues => simp [publicationAtoms, GroupClosureRecordLocated]
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => simp [publicationAtoms, streamPublicationAtoms]
      | case2 =>
          simp [publicationAtoms, streamPublicationAtoms, GroupClosureRecordLocated]
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, GroupClosureRecordLocated] using ih
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simpa only [publicationAtoms, List.mem_singleton, forall_eq] using known

/-- Every actual atomic group closure has a registration descriptor in the original work.
Witness: preserve normalized closure provenance through the unchanged atomic value split.
-/
theorem createWorkQueue_runNormalized_atomicGroupClosureRecordsLocated
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : ∀ event ∈
        ((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten.flatMap
          publicationAtoms,
        GroupClosureRecordLocated work event := by
  intro event member
  obtain ⟨carrier, emitted, within⟩ := List.mem_flatMap.mp member
  exact (createWorkQueue_runNormalized_groupClosureRecordsLocated valid carrier emitted).atoms
    event within

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
