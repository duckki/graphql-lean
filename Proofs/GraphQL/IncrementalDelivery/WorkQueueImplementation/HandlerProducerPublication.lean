import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamProducerPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerPublication

/-! All actual source handlers preserve strict ancestor-producer publication order. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every raw object block has its ancestor-supported object producer strictly before it.
Witness: task successes and item arrivals use their exact preparation/drain certificates.
Failures and stream closures cannot emit object blocks. The supplied common ledger and
source premises are unchanged; no activation or intermediate-state premise is required.
-/
theorem ExecutedWork.handleGraphEvent_ancestorProducer_beforeValue
    {work before event published position group values address owners source
      payload dependencies ref parentOwners parentProducer parentPayload}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [event]) published)
    (selected
      : (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).handleGraphEvent
          event).2[position]?
        = some (.groupValues group values))
    (known
      : TaskAt work (.executionGroup address) owners
          (some (.executionGroup source)) payload)
    (contributes : group.ref ∈ owners)
    (record : GroupRecordAt work group dependencies) (ancestor : ref ∈ dependencies)
    (parentKnown
      : TaskAt work (.executionGroup source) parentOwners parentProducer parentPayload)
    (parentContributes : ref ∈ parentOwners)
    : ∃ value,
        (Occurrence.executionGroup source, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
                WorkQueueEvent.objectValues).length
              + (((((State.initialize (Work.fromExecution work)).replayGraphEvents
                      before).handleGraphEvent
                    event).2.take
                    position).flatMap
                  WorkQueueEvent.objectValues).length) := by
  let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
  cases event with
  | taskSuccess occurrence result =>
      exact generated.taskSuccess_ancestorProducer_beforeValue valid started covered selected
        known contributes record ancestor parentKnown parentContributes
  | streamItems stream items =>
      exact generated.streamItems_ancestorProducer_beforeValue valid started covered selected
        known contributes record ancestor parentKnown parentContributes
  | taskFailure occurrence errors =>
      obtain ⟨groups, streams, next⟩ :=
        (queue.handleGraphEvent_publicationPairs (.taskFailure occurrence errors)).next selected
      exact False.elim (queue.taskFailure_noGroupSuccess occurrence errors group groups streams
        (List.mem_of_getElem? next))
  | streamSuccess stream =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamSuccess] at member
      split at member <;> simp at member
  | streamFailure stream errors =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamFailure] at member
      split at member <;> simp at member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
