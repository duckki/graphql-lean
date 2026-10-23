import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CarrierOutputCuts

/-! Structural carrier coverage uses one ledger at actual host-batch and FIFO cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every structural contributor precedes its carrier in the original batched ledger.
The carrier's actual handler cut fixes both its source frame and its ledger slice;
strict local coverage then joins the earlier prefix at that same object-value offset. -/
theorem ExecutedWork.rawBatches_groupContributor_covered
    {work batches published index group groups streams address owners producer payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (covered
      : (State.initialize (Work.fromExecution work)).BatchClosuresCovered batches
          published)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawBatches batches).2[index]?
        = some (.groupSuccess group groups streams))
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : group.ref ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawBatches batches).2.take
                index).flatMap
              WorkQueueEvent.objectValues).length := by
  let initial := State.initialize (Work.fromExecution work)
  obtain ⟨earlier, batch, later, fifo, source, tail, position, split, batchEq, atHandler,
    count⟩ := initial.rawBatches_groupSuccess_handlerCut batches selected
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := generated.ownerPublicationFrame_atBatchPrefix canonical valid started covered
    earlier batch later fifo split ⟨source :: tail, batchEq.symm⟩
  let current := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let offset := ((initial.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
  let fifoCount := ((current.rawEventReplay fifo available).2.flatMap
    WorkQueueEvent.objectValues).length
  let batchCount := ((current.handleGraphEvents batch).2.flatMap WorkQueueEvent.objectValues).length
  let carrierCount := ((((current.replayGraphEvents fifo available).handleGraphEvent source
    available).2.1.take position).flatMap WorkQueueEvent.objectValues).length
  have batchCovered := (State.BatchClosuresCovered.atBatch earlier batch later
    (split ▸ covered)).1
  have atFifo := State.ReplayClosuresCovered.afterPrefix fifo (source :: tail)
    (show current.ReplayClosuresCovered (fifo ++ source :: tail)
      ((published.drop offset).take batchCount) available from batchEq ▸ batchCovered)
  have handlerCovered := State.ReplayClosuresCovered.prefix [source] tail atFifo
  have sourceValid : ValidGraphEvents work (earlier.flatten ++ fifo ++ [source]) :=
    valid.prefix ⟨tail ++ later.flatten, by simp [split, batchEq, List.append_assoc]⟩
  have sourceAccepted : (current.replayGraphEvents fifo available).acceptsGraphEvent source
      = true := State.handleGraphEvent_accepts_of_emitted available (List.mem_of_getElem? atHandler)
  have licensed : ∀ occurrence errors, (occurrence, errors) ∈ available →
      (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    apply valid.eachMatches
    rw [split, List.flatten_append, List.flatten_cons]
    exact List.mem_append_right _ (List.mem_append_left _ received)
  obtain ⟨value, delivered⟩ := frame.successfulCarrier_structuralContributor_covered generated
    canonical source (by simpa only [List.append_assoc] using sourceValid) sourceAccepted
    available licensed handlerCovered atHandler known contributes
  refine ⟨value, ?_⟩
  rw [count]
  change (Occurrence.executionGroup address, value)
    ∈ published.take (offset + fifoCount + carrierCount)
  rw [List.take_add]
  rcases delivered with before | within
  · exact List.mem_append_left _ before
  · apply List.mem_append_right
    change (Occurrence.executionGroup address, value)
      ∈ (((published.drop offset).take batchCount).drop fifoCount).take carrierCount at within
    rw [List.drop_take, List.drop_drop, List.take_take] at within
    exact List.take_subset_take_left _ (Nat.min_le_left _ _) within

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
