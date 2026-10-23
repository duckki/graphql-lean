import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActualSourceFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SnapshotItemPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProjectedOutputCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeRegistrationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeItemBoundary

/-! Item producers are published by their actual batched object or notice carrier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem itemProducer_prefix_of_sourceCut
    {work batches earlier batch later fifo event tail node dependencies source ordinal
      count}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (List.flatten batches))
    (started : inputsStarted work batches = true)
    (split : batches = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ event :: tail)
    (known : NodeAt work node .group dependencies (some (.item source ordinal)))
    (registered
      : node.ref
        ∈ ((((State.initialize (Work.fromExecution work)).replayBatches
              earlier).replayGraphEvents
              fifo (GraphEvent.availableFailures batch)).handleGraphEvent
            event (GraphEvent.availableFailures batch)).1.registeredGroups)
    (size
      : count
        = (((State.initialize (Work.fromExecution work)).rawBatches earlier).2.flatMap
            WorkQueueEvent.itemValues).length
          + ((((State.initialize (Work.fromExecution work)).replayBatches
                earlier).rawEventReplay
                fifo (GraphEvent.availableFailures batch)).2.flatMap
              WorkQueueEvent.itemValues).length
          + (((((State.initialize (Work.fromExecution work)).replayBatches
                  earlier).replayGraphEvents
                fifo (GraphEvent.availableFailures batch)).handleGraphEvent
                event (GraphEvent.availableFailures batch)).2.1.flatMap
              WorkQueueEvent.itemValues).length)
    : Occurrence.item source ordinal
      ∈ ((batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
          count := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frames := generated.uncancelledFrames_atBatchEvent canonical valid started earlier
    batch later fifo event tail split batchEq
  have seen := frames.2.2.2.regions.group_itemProducer_seen generated known registered
  have observed := frames.1.itemSuccess_publication (frames.1.itemIdentity_success seen)
  let initial := State.initialize (Work.fromExecution work)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  have starts := split ▸ started
  rw [inputsStarted_eq_batchesStarted, State.batchesStarted_append, Bool.and_eq_true] at starts
  obtain ⟨_, accepted, _⟩ := boundary.batchesStarted_cons batch later starts.2
  have batchValid : ValidGraphEvents work (earlier.flatten ++ batch) :=
    valid.prefix ⟨later.flatten, by simp [split, List.append_assoc]⟩
  have priorValid : ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [split]⟩
  have fifoPrefix : fifo.IsPrefix batch := ⟨event :: tail, batchEq.symm⟩
  have priorItems := initial.rawBatches_itemValues earlier (before := []) priorValid starts.1
  have fifoItems := boundary.rawEventReplay_itemValues_of_eachItemAccepted fifo available
    (fun front stream items itemPrefix =>
      State.acceptsBatch_streamItems_live batchValid accepted (itemPrefix.trans fifoPrefix))
  have incomingItems := (boundary.replayGraphEvents fifo available
    ).handleGraphEvent_itemValues_of_itemsStarted event (by
      intro stream items same
      subst event
      exact State.acceptsBatch_streamItems_live batchValid accepted
        ⟨tail, by simp [batchEq]⟩) available
  have sourceCount : count = ((earlier.flatten ++ fifo ++ [event]).flatMap
      GraphEvent.itemPublications).length := by
    rw [size, priorItems, fifoItems, incomingItems]
    simp only [List.length_map, List.flatMap_append, List.length_append, List.flatMap_singleton]
  rw [sourceCount]
  have sourcePrefix : (earlier.flatten ++ fifo ++ [event]).IsPrefix batches.flatten :=
    ⟨tail ++ later.flatten, by simp [split, batchEq, List.append_assoc]⟩
  obtain ⟨suffix, same⟩ := sourcePrefix
  rw [← same, List.flatMap_append (xs := earlier.flatten ++ fifo ++ [event]),
    List.map_append, ← List.length_map (f := Prod.fst),
    List.take_left]
  exact observed

/-- An item-produced releasing group puts its producer before the actual object block. -/
theorem ExecutedWork.rawBatches_groupValues_itemProducer_prefix
    {work batches index group values node dependencies source ordinal}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (List.flatten batches))
    (started : inputsStarted work batches = true)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawBatches batches).2[index]?
        = some (.groupValues group values))
    (known : NodeAt work node .group dependencies (some (.item source ordinal)))
    (sameRef : node.ref = group.ref)
    : Occurrence.item source ordinal
      ∈ ((batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
          (((((State.initialize (Work.fromExecution work)).rawBatches batches).2.take
              index).flatMap
              WorkQueueEvent.itemValues).length) := by
  let initial := State.initialize (Work.fromExecution work)
  obtain ⟨earlier, batch, later, fifo, event, tail, position, split, batchEq, atHandler, count⟩ :=
    initial.rawBatches_immediate_projectedCut WorkQueueEvent.itemValues batches selected
      (by intro _ _ impossible; cases impossible) (by intro impossible; cases impossible)
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frames := generated.uncancelledFrames_atBatchEvent canonical valid started earlier
    batch later fifo event tail split batchEq
  let current := (initial.replayBatches earlier).replayGraphEvents fifo
    (GraphEvent.availableFailures batch)
  obtain ⟨groups, streams, carrier⟩ :=
    (current.handleGraphEvent_publicationPairs event (GraphEvent.availableFailures batch)).next
      atHandler
  obtain ⟨_, _, retired⟩ := State.handleGraphEvent_successfulRetirements frames.2.2.1.parent
    frames.2.2.1.cancellations generated canonical event
    (frames.1.eachMatches (List.mem_append_right _ List.mem_cons_self))
    (GraphEvent.availableFailures batch) group groups streams (List.mem_of_getElem? carrier)
  have prefixItems := current.handleGraphEvent_items_before_groupValues_atSnapshot event
    (GraphEvent.availableFailures batch) atHandler
  have size := count.trans (congrArg (fun values =>
    (((initial.rawBatches earlier).2.flatMap WorkQueueEvent.itemValues).length
      + (((initial.replayBatches earlier).rawEventReplay fifo
        (GraphEvent.availableFailures batch)).2.flatMap WorkQueueEvent.itemValues).length)
      + values.length) prefixItems)
  exact itemProducer_prefix_of_sourceCut generated valid started split batchEq known
    (sameRef.symm ▸ retired.retired.1) size

/-- A noticed group's item producer is published by that actual carrier's inclusive prefix. -/
theorem ExecutedWork.rawBatches_groupNotice_itemProducer_prefix
    {work batches index output node dependencies source ordinal}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (List.flatten batches))
    (started : inputsStarted work batches = true)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawBatches batches).2[index]?
        = some output)
    (known : NodeAt work node .group dependencies (some (.item source ordinal)))
    (noticed : node.ref ∈ rawGroupNoticeRefs output)
    : Occurrence.item source ordinal
      ∈ ((batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
          (((((State.initialize (Work.fromExecution work)).rawBatches batches).2.take
              (index + 1)).flatMap
              WorkQueueEvent.itemValues).length) := by
  let initial := State.initialize (Work.fromExecution work)
  have notStartup : ∀ group errors, output ≠ .groupFailure group errors := by
    intro group errors same
    subst output
    cases noticed
  have notTermination : output ≠ .workQueueTermination := by
    intro same
    subst output
    cases noticed
  obtain ⟨earlier, batch, later, fifo, event, tail, position, split, batchEq, atHandler, count⟩ :=
    initial.rawBatches_immediate_projectedCut WorkQueueEvent.itemValues batches selected
      notStartup notTermination
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frames := generated.uncancelledFrames_atBatchEvent canonical valid started earlier
    batch later fifo event tail split batchEq
  let current := (initial.replayBatches earlier).replayGraphEvents fifo
    (GraphEvent.availableFailures batch)
  have registered := current.handleGraphEvent_groupNoticesRegistered frames.2.2.1.parent.keys
    frames.2.2.1.parent.live frames.2.2.1.parent.tasks frames.2.2.1.parent.registration event
    (frames.1.eachMatches (List.mem_append_right _ List.mem_cons_self))
    (GraphEvent.availableFailures batch) output (List.mem_of_getElem? atHandler)
  have prefixItems := congrArg List.length
    (current.handleGraphEvent_items_through_output_atSnapshot event
      (GraphEvent.availableFailures batch) atHandler)
  have size : (((initial.rawBatches batches).2.take (index + 1)).flatMap
      WorkQueueEvent.itemValues).length
      = ((initial.rawBatches earlier).2.flatMap WorkQueueEvent.itemValues).length
        + (((initial.replayBatches earlier).rawEventReplay fifo
            (GraphEvent.availableFailures batch)).2.flatMap WorkQueueEvent.itemValues).length
        + ((current.handleGraphEvent event (GraphEvent.availableFailures batch)).2.1.flatMap
            WorkQueueEvent.itemValues).length := by
    change (initial.rawBatches batches).2[index]? = some output at selected
    change (current.handleGraphEvent event (GraphEvent.availableFailures batch)).2.1[position]?
      = some output at atHandler
    rw [List.take_add_one, atHandler] at prefixItems
    rw [List.take_add_one, selected]
    simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton,
      List.length_append] at prefixItems ⊢
    rw [count]
    rw [Nat.add_assoc, prefixItems]
  exact itemProducer_prefix_of_sourceCut generated valid started split batchEq known
    (registered.ref noticed) size

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
