import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActions

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

/-- Recursive draining closes only groups with descriptors from the live registry.
Witness: each selected root has a successful node lookup; cleanup and activation preserve
registry provenance before the next success or cached-failure closure.
-/
theorem State.GroupNodesMatchWork.drainReadyGroups_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    : ∀ event ∈ queue.drainReadyGroups.2, event.GroupClosureRecordLocated work := by
  have loop (fuel : Nat) (current : State) (registry : current.GroupNodesMatchWork work)
      : ∀ event ∈ (State.drainReadyGroups.go fuel current).2,
          event.GroupClosureRecordLocated work := by
    induction fuel generalizing current with
    | zero => simp [State.drainReadyGroups.go]
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · simp
        · rename_i node selected
          have member : node ∈ current.groupNodes := by
            obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
            cases found : current.groupNode? key with
            | none => simp [found] at choice
            | some candidate =>
                simp only [found] at choice
                change (if _ then some candidate else none) = some node at choice
                split at choice
                · cases Option.some.inj choice
                  exact List.mem_of_find?_eq_some found
                · contradiction
          have located := registry node member
          cases cached : node.failure with
          | none =>
              intro event emitted
              rcases List.mem_append.mp emitted with first | later
              · exact current.finishGroupSuccess_groupClosureRecordLocated node located event first
              · exact ih _ ((registry.finishGroupSuccess node).startNewWork _) event later
          | some errors =>
              intro event emitted
              rcases List.mem_append.mp emitted with first | later
              · have same := List.mem_singleton.mp first
                subst event
                exact located
              · exact ih _ (registry.finishGroupFailure node errors) event later
  exact loop _ queue registered

/-- Task success closes only groups with registration descriptors from its integration state.
Witness: the actual single-pass contributor fold looks up each closing node, while the
registry invariant survives decrements, flushes, integration, and the final recursive drain.
-/
theorem State.GroupNodesMatchWork.taskSuccess_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    {occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : ∀ event ∈ (queue.taskSuccess occurrence result).2,
        event.GroupClosureRecordLocated work := by
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
  | none => simp [State.taskSuccess, found]
  | some node =>
      have installed : State.GroupNodesMatchWork
          (queue.putTaskNode { node with value := some result.value }) work := registered
      have integrated := installed.maybeIntegrateWork result.work
        (fun group member => matching.taskChildGroups_recordAt member) (some occurrence)
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · intro event impossible
        cases impossible
      obtain ⟨registry, output⟩ := loop node.task.groups (_, [], {}) integrated
        (by intro event impossible; cases impossible)
      intro event emitted
      rcases List.mem_append.mp emitted with first | later
      · exact output event first
      · exact (registry.startNewWork _).drainReadyGroups_groupClosureRecords event later

/-- Task failure closes only looked-up groups; cached latent errors add no event.
Witness: retain registry provenance through initial task removal and every owner branch.
-/
theorem State.GroupNodesMatchWork.taskFailure_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (occurrence : Occurrence) (errors : Nat)
    : ∀ event ∈ (queue.taskFailure occurrence errors).2,
        event.GroupClosureRecordLocated work := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.key with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.key then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
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
          · exact ih _ (known.putGroupNode _ located) output
  unfold State.taskFailure
  split
  · simp
  · split
    · intro event impossible
      cases impossible
    exact loop _ (_, []) (registered.removeTask occurrence)
      (by intro event impossible; cases impossible)

/-- An item handler's final drain closes only groups located in its integration state.
Witness: each matched item's child work preserves registry provenance before the drain;
the leading stream-value event itself closes no group.
-/
theorem State.GroupNodesMatchWork.streamItems_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : ∀ event ∈ (queue.streamItems stream items).2,
        event.GroupClosureRecordLocated work := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have loop (more : List StreamItem) (subset : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : acc.1.GroupNodesMatchWork work)
      : (more.foldl step acc).1.GroupNodesMatchWork work := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih (fun _ member => subset (List.mem_cons_of_mem _ member))
        exact ((prior.maybeIntegrateWork item.work
          (fun group member => matching.streamItem_childGroups_recordAt
            (subset List.mem_cons_self) member)).pruneEmptyGroups _).startNewWork _
  unfold State.streamItems
  split
  · simp
  · intro event emitted
    rcases List.mem_cons.mp emitted with same | later
    · subst event
      trivial
    · have registry := loop items (fun _ member => member) (queue, [], [], []) registered
      exact registry.drainReadyGroups_groupClosureRecords event later

/-- Each matching handler emits group completions only for known registration records.
Witness: task handlers and item-triggered drains retain provenance; stream closures add none.
-/
theorem State.GroupNodesMatchWork.handleGraphEvent_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : ∀ output ∈ (queue.handleGraphEvent event).2,
        output.GroupClosureRecordLocated work := by
  cases event with
  | taskSuccess => exact registered.taskSuccess_groupClosureRecords matching
  | taskFailure occurrence errors =>
      exact registered.taskFailure_groupClosureRecords occurrence errors
  | streamItems stream items =>
      exact registered.streamItems_groupClosureRecords matching
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [WorkQueueEvent.GroupClosureRecordLocated]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [WorkQueueEvent.GroupClosureRecordLocated]

-----------------------------------------------------------------------------------------
-- Preserve closing-node provenance through replay, normalization, and atomic expansion
-----------------------------------------------------------------------------------------

/-- Eventwise replay retains closing-node provenance through each handler's actual state.
Witness: handler output provenance together with the existing registry preservation theorem.
-/
theorem State.GroupNodesMatchWork.rawEventReplay_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : ∀ event ∈ (queue.rawEventReplay events).2,
        event.GroupClosureRecordLocated work := by
  induction events generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      intro output member
      rcases List.mem_append.mp member with first | later
      · exact registered.handleGraphEvent_groupClosureRecords event
          (matching event List.mem_cons_self) output first
      · exact ih (registered.handleGraphEvent event (matching event List.mem_cons_self))
          (fun next member => matching next (List.mem_cons_of_mem _ member)) output later

/-- The real batch wrapper emits only located group closures, including terminal batches.
Witness: eventwise replay; ignored input and queue termination add no group completion.
-/
theorem State.GroupNodesMatchWork.handleGraphEvents_groupClosureRecords {queue : State}
    {work : Execution.Work} (registered : queue.GroupNodesMatchWork work)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : ∀ event ∈ (queue.handleGraphEvents events).2,
        event.GroupClosureRecordLocated work := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · simp
  · have known := registered.rawEventReplay_groupClosureRecords events matching
    dsimp only
    split
    · intro event member
      rcases List.mem_append.mp member with earlier | terminal
      · exact known event earlier
      · have same := List.mem_singleton.mp terminal
        subst event
        trivial
    · exact known

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
        · have emitted := acc.2.1.normalizeBatch_groupClosureRecords
            (registry.handleGraphEvents_groupClosureRecords batch batchMatch)
          dsimp only [normalizedStep]
          split
          · exact output
          · intro event member
            simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
              List.append_nil, List.mem_append] at member
            exact member.elim (output event) (emitted event)
        · exact fun batch member => matching batch (List.mem_cons_of_mem _ member)
  exact loop batches (_, _, []) (createWorkQueue_groupNodesMatchWork work) (by simp)
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
