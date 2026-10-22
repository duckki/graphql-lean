import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SelectedFailureCauses
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureAncestorReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceHandlerBoundaries

/-! Actual failed group completions retain their exact cause under informative selection. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A failed output group's ancestry is healthy under the exact visible object candidates.
Witness: recover the actual source handler and its visible failure ledger from the same
atomic position; source-boundary ancestry health transports through reversal of that ledger.
-/
theorem createWorkQueue_sourceObjectFailureCuts_failureAncestorHealth
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {index group errors}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      GroupAncestorsHealthy work
        (failedBefore
          (sourceObjectFailureCuts 0
            (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2))
          index)
        group.ref := by
  dsimp only
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have starts : queue.batchesStarted batches = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  have annotated : ((queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd)[index]?
      = some (.groupFailure group errors) := by
    rwa [(queue.sourceRunBlocks_agrees batches).2]
  obtain ⟨before, source, after, currentPublisher, localIndex, inputEq, selected, visible⟩ :=
    queue.sourceRunBlocks_atomicHandler publisher batches starts annotated (by intro same; cases same)
  have prior : (before ++ [source]).IsPrefix batches.flatten := ⟨after, by
    simp only [inputEq, List.append_assoc, List.singleton_append]⟩
  have accepted := queue.batchesStarted_acceptsBatch batches starts
  have beforeStarted : queue.acceptsBatch before = true := by
    apply State.acceptsBatch_prefix (after := source :: after)
    rwa [← inputEq]
  have emitted := (currentPublisher.normalizeBatch_atomicGroupFailure_mem _).mp
    (List.mem_of_getElem? selected)
  have healthy := generated.replayGraphEvents_next_failureAncestorsHealthy
    (valid.prefix prior) beforeStarted group errors emitted
  rw [← visible] at healthy
  intro record dependencies known same ancestor member invalid
  exact healthy record dependencies known same ancestor member
    (invalid.mono (fun _ recorded => List.mem_reverse.mpr recorded))

/-- Every actual failed group output keeps its exact positive cause under selected cuts.
Witness: generated ancestry health rules out inherited cancellation; the unit-cause proof
lets an earlier selected contributor explain a redundant source rejection's completion.
-/
theorem createWorkQueue_selectedObjectFailureCuts_nodeFailureCause
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {index group errors}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let candidates :=
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
      NodeFailureCause work
        (failedBefore (selectObjectFailureCuts work [] candidates) index) group.ref
        errors := by
  dsimp only
  obtain ⟨dependencies, producer, known⟩ :=
    createWorkQueue_runNormalized_atomicGroupClosuresLocated generated valid _
      (List.mem_of_getElem? atEvent)
  apply generated.selectObjectFailureCuts_nodeFailureCause
    (sourceObjectFailureCuts_ordered _ _) known
    (fun entry member => ?_)
    (createWorkQueue_sourceObjectFailureCuts_failureAncestorHealth generated valid started atEvent)
    (createWorkQueue_sourceObjectFailureCuts_nodeErrors generated valid started atEvent)
  obtain ⟨_, owners, producer, path, errors, task, _⟩ :=
    createWorkQueue_eligibleObjectFailureCuts_origin generated valid entry member
  exact ⟨owners, producer, _, task, rfl⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
