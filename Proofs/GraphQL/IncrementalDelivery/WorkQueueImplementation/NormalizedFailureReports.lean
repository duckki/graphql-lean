import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureReportReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationSupport

/-! Concrete cleanup reports survive owner normalization on the shared replay witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Publisher normalization and atomic expansion preserve each exact group report origin.
Witness: positive counts, descriptors, and failure-control membership are copied unchanged;
only successful publication owners are normalized.
-/
theorem GroupFailureReported.normalized {events group dependencies}
    (reported : GroupFailureReported events group dependencies)
    (publisher : IncrementalPublisher)
    : GroupFailureReported ((publisher.normalizeBatch events).2.flatMap publicationAtoms)
        group dependencies := by
  obtain ⟨reporter, errors, positive, emitted, ancestor⟩ := reported
  exact ⟨reporter, errors, positive,
    (publisher.normalizeBatch_atomicGroupFailure_mem events).mpr emitted, ancestor⟩

/-- Every final cancellation marker has a positive report in the canonical atom history.
Witness: generated raw replay derives report origins independently of admission;
started replay has the same state and exactly the normalized raw nonterminal output.
The concrete termination flag changes no marker, descriptor, or reported error count.
-/
theorem ExecutedWork.runNormalized_cancelledRecordsReported {work : Execution.Work}
    (generated : ExecutedWork work) (inputs : List (List GraphEvent))
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : let queue := State.initialize (Work.fromExecution work)
      (queue.runNormalized inputs).1.CancelledRecordsReported work
        (queue.nonterminalAtoms inputs) := by
  intro queue
  have raw := generated.rawEventReplay_cancelledRecordsReported inputs.flatten
    (fun _ member => valid.eachMatches member)
  dsimp only at raw
  rw [State.rawEventReplay_state] at raw
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  intro node dependencies known cancelled
  have reported := raw node dependencies known cancelled
  rw [createWorkQueue_nonterminalAtoms_flattened inputs started]
  exact reported.normalized _

namespace ConformancePlan

/-- A cancelled contributor supplies a covering attachment report on the common witness.
Witness: concrete cancellation provenance survives normalization; execution-derived paths
turn its same-group or full-ancestor ref into a scope covering the selected object task.
No terminal-reporting premise, alternate matching, or terminal-state premise is used.
-/
theorem cancelledContributor_task_reported {work inputs address owners producer payload}
    {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    {group dependencies birth} (record : NodeAt work group .group dependencies birth)
    (contributes : group.ref ∈ owners)
    (cancelled : group.ref ∈ ((initialQueue work).runNormalized inputs).1.cancelledGroups)
    : FailureReportedFor w.events payload.path := by
  have reported := generated.runNormalized_cancelledRecordsReported inputs valid started
    group dependencies (groupRecordAt_of_nodeAt record) cancelled
  rw [← history] at reported
  exact generated.groupReport_covers_task explained known record contributes reported

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
