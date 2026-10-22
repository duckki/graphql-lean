import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalFailedContributors

/-! Actual accepted failure cuts supply structural owners for terminal reporting. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An accepted failure's actual task contributors receive a positive terminal report. -/
theorem terminal_acceptedContributor_reported
    {work inputs earlier batch later fifo after occurrence errors task} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (splitInputs : inputs = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ .taskFailure occurrence errors :: after)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    {group dependencies} (record : GroupRecordAt work group dependencies)
    (found
      : (((initialQueue work).replayBatches earlier).replayGraphEvents fifo
          (GraphEvent.availableFailures batch)).taskNode?
          occurrence
        = some task)
    (contributes : group.ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    : GroupFailureReported w.events group dependencies := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have source := (generated.uncancelledFrames_atBatchEvent canonical valid started earlier batch
    later fifo (.taskFailure occurrence errors) after splitInputs batchEq).2.2.1
  have lookup := State.taskNode?_some found
  obtain ⟨_, payload, producer, _, descriptor⟩ :=
    (source.pending.matching task.task (source.pending.started task lookup.1)).1
  have failed : occurrence ∈ GraphEvent.failureSettlements inputs.flatten := by
    apply List.mem_reverse.mpr
    refine List.mem_flatMap.mpr ⟨GraphEvent.taskFailure occurrence errors, ?_, List.mem_cons_self⟩
    rw [splitInputs, List.flatten_append, List.flatten_cons, batchEq]
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_append_right _ List.mem_cons_self))
  exact terminal_failedContributor_reported generated valid started history ended
    ⟨producer, payload, lookup.2 ▸ descriptor⟩ contributes failed record

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
