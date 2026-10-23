import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupPublicationMatching
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupSourceEventFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupSuccessfulRetirements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulSettlementAcceptance

/-! Canonical object publications originate at actual accepted storing boundaries. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A supplied success with a contributor that remains uncancelled was processed at its
actual cached source cut. An initially eligible but retired callback has no memberships,
which contradicts the source frame's uncancelled owner accounting for that contributor.
-/
theorem ExecutedWork.startup_taskSuccess_sourceCut_of_uncancelledOwner
    {work inputs occurrence result owners producer payload ref}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (supplied : GraphEvent.taskSuccess occurrence result ∈ inputs.flatten)
    (known : TaskAt work occurrence owners producer payload) (contributes : ref ∈ owners)
    (uncancelled
      : ref
        ∉ (((State.initialize (Work.fromExecution work) startup)).runNormalized
            inputs).1.cancelledGroups)
    : ∃ earlier batch later fifo tail node,
        inputs = earlier ++ batch :: later
        ∧ batch = fifo ++ .taskSuccess occurrence result :: tail
        ∧ (((((State.initialize (Work.fromExecution work) startup)).replayBatches
              earlier).replayGraphEvents
              fifo (GraphEvent.availableFailures batch)).cacheTaskFailures
            (GraphEvent.availableFailures batch)).taskNode?
            occurrence
          = some node := by
  obtain ⟨batch, listed, received⟩ := List.mem_flatten.mp supplied
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp listed
  obtain ⟨fifo, tail, batchEq⟩ := List.mem_iff_append.mp received
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  obtain ⟨sourceValid, accepted, frame, _⟩ := generated.startup_uncancelledFrames_atBatchEvent
    startup matched canonical
    valid started earlier batch later fifo (.taskSuccess occurrence result) tail split batchEq
  obtain ⟨priorValid, matching, fresh⟩ := validGraphEvents_last sourceValid
  let initial := (State.initialize (Work.fromExecution work) startup)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let current := boundary.replayGraphEvents fifo available
  have tracked : current.StartedTaskDisposition occurrence
      ∧ ∃ task ∈ current.tasks, task.occurrence = occurrence := by
    obtain ⟨seen, seenPrefix, eligible⟩ := accepted
    have priorFrame := generated.startup_uncancelledFrame_atBatchPrefix canonical startup matched earlier batch later seen
      (split ▸ valid) (split ▸ started)
      (seenPrefix.trans ⟨.taskSuccess occurrence result :: tail, batchEq.symm⟩)
    change ((boundary.replayGraphEvents seen available).taskNode? occurrence).isSome = true at eligible
    cases found : (boundary.replayGraphEvents seen available).taskNode? occurrence with
    | none => simp [found] at eligible
    | some node =>
        obtain ⟨remaining, history⟩ := seenPrefix
        have disposition := priorFrame.pending.startedTaskDisposition_atPrefix found
          priorFrame.producers priorFrame.producerOrder remaining
          (by simpa [history, List.append_assoc] using priorValid) available
        change (boundary.replayGraphEvents fifo available).StartedTaskDisposition occurrence
          ∧ ∃ task ∈ (boundary.replayGraphEvents fifo available).tasks, task.occurrence = occurrence
        rw [← history, State.replayGraphEvents_append boundary seen remaining available]
        exact ⟨
          disposition,
          node.task,
          (boundary.replayGraphEvents seen available).replayGraphEvents_tasks_subset
            remaining available
            (priorFrame.pending.started node (List.mem_of_find?_eq_some found)),
          (State.taskNode?_some found).2
        ⟩
  have starts : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rw [← split, ← inputsStartedWithStartup_eq_batchesStarted]
    exact started
  rw [State.batchesStarted_append, Bool.and_eq_true] at starts
  obtain ⟨running, _, _⟩ := boundary.batchesStarted_cons batch later starts.2
  obtain ⟨terminal, core⟩ := boundary.handleGraphEvents_stateCore batch running
  have batchIncludes : current.cancelledGroups.Subset
      (boundary.handleGraphEvents batch).1.cancelledGroups := by
    rw [core]
    change current.cancelledGroups.Subset
      (boundary.replayGraphEvents batch available).cancelledGroups
    rw [batchEq, State.replayGraphEvents_append _ _ _ available]
    exact current.replayGraphEvents_cancelledGroups_subset
      (.taskSuccess occurrence result :: tail) available
  have future := (boundary.handleGraphEvents batch).1.runNormalized_cancelledGroups_subset later
  rw [State.runNormalized_replayBatches] at future
  have finalEq : (initial.runNormalized inputs).1
      = (boundary.handleGraphEvents batch).1.replayBatches later := by
    simp only [initial, boundary, State.runNormalized_replayBatches, split,
      State.replayBatches,
      List.foldl_append, List.foldl_cons]
  have currentUncancelled : ref ∉ current.cancelledGroups := by
    intro member
    apply uncancelled
    rw [finalEq]
    exact future (batchIncludes member)
  obtain ⟨liveNode, liveLookup⟩ := frame.taskNode_of_uncancelledOwner tracked known
    (fun settled => fresh.2.2.1 occurrence List.mem_cons_self
      (GraphEvent.groupSettlements_subsetIdentities _ settled)) contributes currentUncancelled
  have cached : (current.cacheTaskFailures available).acceptsGraphEvent
      (.taskSuccess occurrence result) = true := by
    rw [State.cacheTaskFailures_acceptsGraphEvent]
    change (current.taskNode? occurrence).isSome = true
    rw [liveLookup]
    rfl
  cases found : (current.cacheTaskFailures available).taskNode? occurrence with
  | none => simp only [State.acceptsGraphEvent, found, Option.isSome_none,
      Bool.false_eq_true] at cached
  | some node => exact ⟨earlier, batch, later, fifo, tail, node, split, batchEq, found⟩

namespace ConformancePlan

/-- Every canonical object atom has a matching success at an actual cached storing cut. -/
theorem Witness.startup_groupPublication_processed {work inputs w index owner payload}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (selected : w.events[index]? = some (.groupValues owner payload))
    : ∃ earlier batch later fifo result tail node,
        inputs = earlier ++ batch :: later
        ∧ batch = fifo ++ .taskSuccess (w.matching index) result :: tail
        ∧ (GraphEvent.taskSuccess (w.matching index) result).MatchesWork work
        ∧ (((((State.initialize (Work.fromExecution work) startup)).replayBatches
              earlier).replayGraphEvents
              fifo (GraphEvent.availableFailures batch)).cacheTaskFailures
            (GraphEvent.availableFailures batch)).taskNode?
            (w.matching index)
          = some node := by
  obtain ⟨origin⟩ := Witness.startup_groupPublication_origin startup started history selected
  have savedLedger := ledger
  obtain ⟨_, _, exactLedger, _⟩ := savedLedger
  have raw := origin.rawValue_atRank
  dsimp only at raw
  rw [(Witness.startup_rawBatches_canonical startup history selected).2] at raw
  obtain ⟨result, supplied, _, matching⟩ := exactLedger.source_at selected raw
  obtain ⟨producer, known⟩ := Witness.startup_groupPublication_taskAt startup started history
    ledger selected origin
  have contributes := State.startup_rawBatches_publicationContributors startup valid
    origin.group origin.values origin.members.1 origin.value origin.members.2
  obtain ⟨carrier, _⟩ := Witness.startup_rawBatches_nonterminal startup history origin.carrier
    (by intro impossible; cases impossible)
  obtain ⟨atFull, _⟩ := Witness.startup_event startup history carrier
  obtain ⟨sourceIndex, atSource, _⟩ := publicationAtoms_groupSuccess_prefix _ atFull
  obtain ⟨dependencies, descriptor, retirement⟩ :=
    generated.startup_runNormalized_successfulGroupRetirements startup matched
    valid started (List.mem_of_getElem? atSource)
  obtain ⟨earlier, batch, later, fifo, tail, node, split, batchEq, found⟩ :=
    generated.startup_taskSuccess_sourceCut_of_uncancelledOwner startup matched valid started
      supplied known contributes
      retirement.uncancelled
  exact ⟨earlier, batch, later, fifo, result, tail, node, split, batchEq, matching, found⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
