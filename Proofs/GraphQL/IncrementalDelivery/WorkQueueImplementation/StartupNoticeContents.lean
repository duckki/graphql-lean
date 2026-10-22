import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupNoticeCarrierCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupCarrierOutputCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupSourceEventFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicItemNoticeContents

/-! Canonical group carriers retain concrete unpublished contents at actual source cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- Every canonical group notice retains unpublished tasks.
Witness: the actual source boundary supplies the carrier's object rank and its exact
owner-fold or pre-startup drain contents. The common
publication ledger supplies nonpublication without assuming the child's notice admission.
-/
theorem startup_groupGroupNotice_unpublished
    {work inputs w index group groups streams child}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (objects : GroupPublicationAdmission work w)
    (ready : StreamPublicationReady work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    : RetainedNoticeContents work w.matching (w.events.take index)
        (failedBefore w.failures index) inputs.flatten child := by
  obtain ⟨published, batches, matching, _⟩ := ledger
  obtain ⟨atFull, beforeEq⟩ := Witness.startup_event startup history selected
  obtain ⟨position, atRaw, atomicCount⟩ :=
    State.startup_runNormalized_groupSuccess_rawPrefix startup atFull
  obtain ⟨earlier, batch, later, fifo, event, tail, localIndex, split, batchEq, emitted,
    count⟩ := ((State.initialize (Work.fromExecution work)
      startup)).rawBatches_groupSuccess_handlerCut inputs atRaw
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  obtain ⟨sourceValid, _, source, _⟩ := generated.startup_uncancelledFrames_atBatchEvent startup
    matched canonical
    valid started earlier batch later fifo event tail split batchEq
  let boundary := ((State.initialize (Work.fromExecution work)
    startup)).replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let current := boundary.replayGraphEvents fifo available
  have cut := startup_batchHandlerMembershipCut startup batches valid started split batchEq
  have sourceCut := startup_batchPublicationCut startup batches valid started earlier batch later
    fifo split
    ⟨event :: tail, batchEq.symm⟩
  have prior : (earlier.flatten ++ fifo).IsPrefix inputs.flatten :=
    ⟨event :: tail ++ later.flatten, by simp [split, batchEq, List.append_assoc]⟩
  have producers : TaskProducersSucceeded work (current.cacheTaskFailures available).tasks
      inputs.flatten := by
    rw [State.cacheTaskFailures_tasks]
    exact sourceCut.1.mono prior.subset
  have input : event ∈ inputs.flatten := by
    rw [split, List.flatten_append, List.flatten_cons, batchEq]
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_append_right _ List.mem_cons_self))
  apply source.groupNotice_unpublished generated canonical (valid.eachMatches input) cut
    producers input matching objects ready emitted noticed
  rw [← beforeEq, atomicCount, count]
  simp only [List.flatMap_append, List.length_append]

/-- Every actual item-carried group notice retains concrete unpublished task memberships.
The exact batch/FIFO boundary supplies source metadata and the same ledger prefix. Item
origin inversion locates the introducing pruning boundary before cached startup removal. -/
theorem startup_itemGroupNotice_contents
    {work inputs w index owner values groups streams child}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (objects : GroupPublicationAdmission work w)
    (ready : StreamPublicationReady work w)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups)
    : RetainedNoticeContents work w.matching (w.events.take index)
        (failedBefore w.failures index) inputs.flatten child := by
  obtain ⟨earlier, batch, later, fifo, stream, items, tail, split, batchEq, _, notices, count⟩ :=
    Witness.startup_itemNotice_sourceBoundary startup started history selected
      (List.mem_append_left _ noticed)
  obtain ⟨published, batches, matching, _⟩ := ledger
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  obtain ⟨sourceValid, _, source, _⟩ := generated.startup_uncancelledFrames_atBatchEvent startup
    matched canonical
    valid started earlier batch later fifo (.streamItems stream items) tail split batchEq
  let boundary := ((State.initialize (Work.fromExecution work)
    startup)).replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let current := boundary.replayGraphEvents fifo available
  have cut := startup_batchHandlerMembershipCut startup batches valid started split batchEq
  have sourceCut := startup_batchPublicationCut startup batches valid started earlier batch later
    fifo split
    ⟨.streamItems stream items :: tail, batchEq.symm⟩
  have prior : (earlier.flatten ++ fifo).IsPrefix inputs.flatten :=
    ⟨.streamItems stream items :: tail ++ later.flatten,
      by simp [split, batchEq, List.append_assoc]⟩
  have producers : TaskProducersSucceeded work (current.cacheTaskFailures available).tasks
      inputs.flatten := by
    rw [State.cacheTaskFailures_tasks]
    exact sourceCut.1.mono prior.subset
  have input : GraphEvent.streamItems stream items ∈ inputs.flatten := by
    rw [split, List.flatten_append, List.flatten_cons, batchEq]
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_append_right _ List.mem_cons_self))
  apply source.streamItems_leadingNotice_contents generated canonical
    (sourceValid.eachMatches (List.mem_append_right _ List.mem_cons_self)) cut producers
    input matching objects ready (notices ▸ noticed)
  simpa only [List.flatMap_append, List.length_append] using count

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
