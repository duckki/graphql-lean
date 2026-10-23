import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeControlCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeTracking
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeAncestorHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupSourceEventFrames

/-! Announced startup notice ancestors complete at their actual source carrier cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- An ancestor ref cannot be supplied by an unrelated stream's announcement
-----------------------------------------------------------------------------------------

/-- An announced defer ancestor comes from initial groups or prior group notices.
Witness: generated ref roles exclude every initial or carried stream descriptor, including
taskless ancestor records. Only actual output provenance is used, not notice admission.
-/
theorem startup_groupNoticeAncestor_announced_group
    {work inputs index child dependencies ref} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (_matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (announced : ref ∈ announcedRefs (initialRefs work) (w.events.take index))
    : ref
      ∈ ((initialQueue work).initialGroups.map Execution.DeliveryNode.ref)
        ++ (w.events.take index).flatMap groupNoticeRefs := by
  rcases List.mem_append.mp announced with initial | pending
  · rw [initialRefs, List.map_append] at initial
    rcases List.mem_append.mp initial with group | stream
    · apply List.mem_append_left
      exact group
    · obtain ⟨stream, member, same⟩ := List.mem_map.mp stream
      exact False.elim (generated.groupRecord_ancestor_ne_stream known ancestor
        ((createWorkQueue_initialStreams_nodeAt work).2 stream member) same.symm)
  · obtain ⟨event, prior, notice⟩ := List.mem_flatMap.mp pending
    have inWitness := List.mem_of_mem_take prior
    obtain ⟨position, selected⟩ := List.mem_iff_getElem?.mp inWitness
    have atFull := (Witness.startup_event startup history selected).1
    have streamKnown := State.startup_runNormalized_atomicStreamNoticesLocated startup valid event
      (List.mem_of_getElem? atFull)
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨event, prior, ?_⟩
    cases event <;> simp only [eventPending] at notice
    case groupSuccess group groups streams | streamValues group values groups streams =>
      rw [List.map_append] at notice
      rcases List.mem_append.mp notice with groupNotice | streamNotice
      · exact groupNotice
      · obtain ⟨stream, member, same⟩ := List.mem_map.mp streamNotice
        obtain ⟨enclosing, producer, located⟩ := streamKnown stream member
        exact False.elim (generated.groupRecord_ancestor_ne_stream known ancestor located
          same.symm)
    all_goals cases notice

/-- A previously announced group ref has a structural task contributor.
Initial roots project their initial descriptors. Earlier canonical notices retain their
generated descriptors through normalization and publication atomization.
-/
theorem startup_announcedGroup_contributor {work inputs index ref} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (_matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (announced
      : ref
        ∈ ((initialQueue work).initialGroups.map Execution.DeliveryNode.ref)
          ++ (w.events.take index).flatMap groupNoticeRefs)
    : ∃ occurrence owners, TaskHasOwners work occurrence owners ∧ ref ∈ owners := by
  rcases List.mem_append.mp announced with initial | prior
  · obtain ⟨group, member, same⟩ := List.mem_map.mp initial
    obtain ⟨dependencies, known⟩ := generated.initialGroups_nodeAt member
    obtain ⟨occurrence, owners, payload, task, contributes⟩ := known.group_task
    exact ⟨occurrence, owners, ⟨none, payload, task⟩, same ▸ contributes⟩
  · obtain ⟨event, earlier, mentioned⟩ := List.mem_flatMap.mp prior
    obtain ⟨position, selected⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take earlier)
    have located := State.startup_runNormalized_atomicGroupNoticesLocated generated startup valid
      event
      (List.mem_of_getElem? (Witness.startup_event startup history selected).1)
    apply Execution.WorkQueueEvent.GroupNoticesLocated.contributor located
    cases event <;> exact mentioned

private theorem batchRejections_match {work inputs earlier batch later}
    (valid : ValidGraphEvents work (List.flatten inputs))
    (split : inputs = earlier ++ batch :: later)
    : ∀ occurrence errors,
        (occurrence, errors) ∈ GraphEvent.availableFailures batch
        → (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
  intro occurrence errors member
  obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
  cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  apply valid.eachMatches
  rw [split, List.flatten_append, List.flatten_cons]
  exact List.mem_append_right _ (List.mem_append_left _ received)

-----------------------------------------------------------------------------------------
-- Discharge the concrete announced-or-completed status alternative
-----------------------------------------------------------------------------------------

/-- An announced ancestor completes by the actual canonical group-success notice carrier.
Witness: role separation identifies its group announcement; the joint raw-prefix bridge
and source-history completion theorem transport its closure through the same carrier.
-/
theorem startup_groupNoticeAncestor_completed
    {work inputs index group groups streams child dependencies ref} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (announced : ref ∈ announcedRefs (initialRefs work) (w.events.take index))
    : ref ∈ completedRefs (w.events.take index ++ [.groupSuccess group [] []]) := by
  have groupNotice := startup_groupNoticeAncestor_announced_group generated startup matched valid
    history known
    ancestor announced
  obtain ⟨occurrence, owners, task, contributes⟩ :=
    startup_announcedGroup_contributor generated startup matched valid history groupNotice
  obtain ⟨position, atRaw, notices, closures⟩ :=
    Witness.startup_groupNotice_sourceControls startup valid started history selected
  obtain ⟨earlier, batch, later, fifo, event, tail, offset, split, batchEq, atHandler, prefixEq⟩ :=
    ((State.initialize (Work.fromExecution work)
      startup)).rawBatches_immediate_rawCut inputs atRaw
      (by intro group errors impossible; cases impossible) (by intro impossible; cases impossible)
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  obtain ⟨sourceValid, _, source, _⟩ := generated.startup_uncancelledFrames_atBatchEvent startup
    matched canonical valid
    started earlier batch later fifo event tail split batchEq
  have tracking := State.startup_batchPrefix_groupNoticeTracking work startup earlier fifo
    (GraphEvent.availableFailures batch)
  have inclusive : (((State.initialize (Work.fromExecution work)
    startup)).rawBatches inputs).2.take (position + 1) =
      (((State.initialize (Work.fromExecution work) startup)).rawBatches earlier).2 ++
        ((((State.initialize (Work.fromExecution work) startup)).replayBatches
          earlier).rawEventReplay fifo
          (GraphEvent.availableFailures batch)).2 ++
        (((((State.initialize (Work.fromExecution work) startup)).replayBatches
          earlier).replayGraphEvents fifo
          (GraphEvent.availableFailures batch)).handleGraphEvent event
          (GraphEvent.availableFailures batch)).2.1.take (offset + 1) := by
    simp only [List.take_add_one, atRaw, atHandler, Option.toList_some, prefixEq, List.append_assoc]
  have closed := source.groupNoticeAncestor_completed tracking generated canonical sourceValid
    (GraphEvent.availableFailures batch) (batchRejections_match valid split) task contributes
    atHandler noticed known ancestor (by
      rw [← inclusive]
      rw [notices] at groupNotice
      exact (List.mem_append.mp groupNotice).elim (List.mem_append_left _)
        (fun member => List.mem_append_right _ (List.mem_flatMap.mpr (by
          obtain ⟨event, prior, contains⟩ := List.mem_flatMap.mp member
          exact ⟨event, List.take_subset_take_left _ (Nat.le_succ position) prior, contains⟩))))
  rw [← inclusive, List.take_add_one, atRaw] at closed
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton,
    rawGroupClosureRefs] at closed
  apply groupClosureRefs_subset_completed
  have kept : ref ∈ (w.events.take index).flatMap groupClosureRefs ++ [group.ref] := by
    rcases List.mem_append.mp closed with earlier | carrier
    · exact List.mem_append_left _ (closures earlier)
    · exact List.mem_append_right _ carrier
  simpa only [List.flatMap_append, List.flatMap_singleton, groupClosureRefs] using kept

/-- An announced ancestor of an item-carried group notice completes strictly before it.
Witness: the item carrier's joint raw boundary retains group controls, and its source
completion theorem rules out using any closure from the current handler's later drain.
-/
theorem startup_itemGroupNoticeAncestor_completed
    {work inputs index owner values groups streams child dependencies ref} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (announced : ref ∈ announcedRefs (initialRefs work) (w.events.take index))
    : ref ∈ completedRefs (w.events.take index) := by
  have groupNotice := startup_groupNoticeAncestor_announced_group generated startup matched valid
    history known
    ancestor announced
  obtain ⟨occurrence, owners, task, contributes⟩ :=
    startup_announcedGroup_contributor generated startup matched valid history groupNotice
  obtain ⟨position, rawValues, atRaw, notices, closures⟩ :=
    Witness.startup_itemNotice_sourceControls startup valid started history selected
      (List.mem_append_left _ noticed)
  obtain ⟨earlier, batch, later, fifo, event, tail, offset, split, batchEq, atHandler, prefixEq⟩ :=
    ((State.initialize (Work.fromExecution work)
      startup)).rawBatches_immediate_rawCut inputs atRaw
      (by intro group errors impossible; cases impossible) (by intro impossible; cases impossible)
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  obtain ⟨sourceValid, _, source, _⟩ := generated.startup_uncancelledFrames_atBatchEvent startup
    matched canonical valid
    started earlier batch later fifo event tail split batchEq
  have tracking := State.startup_batchPrefix_groupNoticeTracking work startup earlier fifo
    (GraphEvent.availableFailures batch)
  have closed := source.itemNoticeAncestor_completed tracking generated canonical sourceValid
    (GraphEvent.availableFailures batch) (batchRejections_match valid split) task contributes
    atHandler noticed known ancestor (by rwa [notices, prefixEq] at groupNotice)
  rw [← prefixEq] at closed
  exact groupClosureRefs_subset_completed _ (closures closed)

-----------------------------------------------------------------------------------------
-- The scheduler's dependency clause now follows from the unchanged source laws
-----------------------------------------------------------------------------------------

/-- Every ancestor of an actual group-success notice is ready at its frozen carrier cut.
Witness: canonical publication accounting supplies all ancestor tasks, supported
publication supplies health, and the exact completion bridge closes any announced ref.
Unannounced ancestors use silent accounting, including taskless registration shells.
-/
theorem startup_groupNoticeAncestor_dependencySatisfied
    {work inputs index group groups streams child dependencies} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (support : PublicationSupport work w.matching w.events w.failures)
    (failures : AnnouncedFailures work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    : ∀ ref ∈ dependencies,
        DependencySatisfied work (initialRefs work) w.matching
          (w.events.take index ++ [.groupSuccess group [] []])
          (w.failures.filter (fun entry => entry.1 ≤ index)) ref := by
  classical
  intro ref ancestor
  apply dependencySatisfied_noticeCarrier_of_status selected
    (startup_groupNoticeAncestor_healthy generated startup matched valid started history ledger
      support failures
      selected noticed known ref ancestor)
    (startup_groupNoticeAncestor_nodeAccounted generated startup matched valid started history
      ledger selected
      noticed known ancestor _)
  by_cases announced : ref ∈ announcedRefs (initialRefs work) (w.events.take index)
  · exact .inl (startup_groupNoticeAncestor_completed generated startup matched valid started
      history selected
      noticed known ancestor announced)
  · exact .inr announced

/-- Every ancestor of an item-carried group notice is ready at its frozen carrier cut.
Witness: its tasks and any announced closure precede the source item's leading carrier.
The shared semantic health theorem remains valid through the final item atom with frozen
failure cuts. No completion from the handler's later recursive drain is used.
-/
theorem startup_itemGroupNoticeAncestor_dependencySatisfied
    {work inputs index owner values groups streams child dependencies} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (support : PublicationSupport work w.matching w.events w.failures)
    (failures : AnnouncedFailures work w)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    : ∀ ref ∈ dependencies,
        DependencySatisfied work (initialRefs work) w.matching
          (w.events.take index ++ [.streamValues owner values [] []])
          (w.failures.filter (fun entry => entry.1 ≤ index)) ref := by
  classical
  intro ref ancestor
  apply dependencySatisfied_noticeCarrier_of_status selected
    (startup_itemGroupNoticeAncestor_healthy generated startup matched valid started history
      ledger support failures
      selected noticed known ref ancestor)
    (startup_itemGroupNoticeAncestor_nodeAccounted generated startup matched valid started
      history ledger selected
      noticed known ancestor _)
  by_cases announced : ref ∈ announcedRefs (initialRefs work) (w.events.take index)
  · left
    have closed := startup_itemGroupNoticeAncestor_completed generated startup matched valid
      started history selected
      noticed known ancestor announced
    simpa only [completedRefs, List.flatMap_append, List.flatMap_singleton,
      withoutChildNotices, eventCompleted, List.append_nil] using closed
  · exact .inr announced

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
