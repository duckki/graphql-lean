import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupObjectStreamSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamSourceBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupCausalFailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveObjectStreamHealth

/-! Actual startup stream actions retain healthy successful object support. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Selected object causes retain initial or actual source provenance, even when a report
exposes a rejection before its callback. This inventory does not assert callback consumption. -/
theorem InitialStartup.informativeObjectFailureCuts_source_subset
    (startup : InitialStartup) (work : Execution.Work) (batches : List (List GraphEvent))
    (cut : Nat)
    : (failedBefore (startup.informativeObjectFailureCuts work batches) cut).Subset
        (startup.failures.map Prod.fst
          ++ GraphEvent.failureSettlements batches.flatten) := by
  classical
  let initial := State.initialize (Work.fromExecution work) startup
  let refs := (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  let blocks := (initial.sourceRunBlocks publisher batches).2.2
  let observations := startup.reportingObservations work refs ++ blocks.filterMap Prod.fst
  have received occurrence errors (member : GraphEvent.taskFailure occurrence errors ∈ observations)
      : occurrence ∈ startup.failures.map Prod.fst ++ GraphEvent.failureSettlements batches.flatten := by
    rcases List.mem_append.mp member with early | source
    · exact List.mem_append_left _ (List.mem_map_of_mem
        (InitialStartup.mem_reportingObservations.mp early).1)
    · apply List.mem_append_right
      exact List.mem_reverse.mpr (List.mem_flatMap.mpr
        ⟨_, (initial.sourceRunBlocks_inputs publisher batches).subset source, List.mem_cons_self⟩)
  intro occurrence member
  have reported := failedBefore_mono (selectObjectFailureCuts_sublist work [] _).subset cut member
  have available := prependInitialReporting_failedBefore_subset (startup.reportingCuts work refs)
    (startup.objectAvailabilityCuts work batches) cut reported
  rcases List.mem_append.mp available with early | later
  · have selected : occurrence ∈ startup.reportingOccurrences work refs := by
      simpa [InitialStartup.reportingCuts, List.map_map] using early
    exact List.mem_append_left _ (InitialStartup.mem_reportingOccurrences.mp selected).1
  · obtain ⟨entry, selected, same⟩ := List.mem_map.mp later
    have candidate := (firstReportingCuts_sublist [] _).subset (List.mem_filter.mp selected).1
    have partition := interleaveFailureCuts_partition (sourceObjectFailureCuts 0 blocks)
      (groupReportCandidateCuts work observations 0 (blocks.flatMap Prod.snd))
    rw [← same]
    rcases List.mem_append.mp (partition.mem_iff.mp candidate) with report | source
    · obtain ⟨_, group, errors, count, _, _, part⟩ := groupReportCandidateCuts_origin report
      have sources : GroupFailureSources work observations group.ref errors := by
        apply Classical.byContradiction
        intro absent
        simp only [groupReportSourceParts, dite_eq_right absent, List.not_mem_nil] at part
      exact received entry.2 count ((groupReportSourceParts_spec sources).2.2.2 entry.2 count part).1
    · obtain ⟨errors, source⟩ := sourceObjectFailureCuts_source source
      exact received entry.2 errors (List.mem_append_right _ source)

/-- The actual startup batch/FIFO cut supplies active successful stream support. -/
theorem ExecutedWork.startup_activeObjectStreamHealthy_atSourceCut
    {work batches received input stream dependencies source closing matching events
      failures}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    (action : input.streamAction = some (stream.ref, closing))
    (cut
      : ∃ earlier batch later fifo tail,
          batches = earlier ++ batch :: later
          ∧ batch = fifo ++ input :: tail
          ∧ received = earlier.flatten ++ fifo)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (objectsRecorded
      : ∀ occurrence owners producer path result,
          TaskAt work occurrence owners producer (.object path result)
          → occurrence ∈ failedBefore failures events.length
          → occurrence
            ∈ startup.failures.map Prod.fst
              ++ GraphEvent.failureSettlements batches.flatten)
    (itemsSafe
      : ∀ address index,
          Occurrence.item address index ∈ received.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item address index))
    (contributors
      : ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → stream.ref ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    : ¬TaskCancelled work matching events failures (.executionGroup source)
      ∧ ¬NodeFailed work matching events failures stream.ref := by
  obtain ⟨earlier, batch, later, fifo, tail, split, batchEq, beforeEq⟩ := cut
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := generated.startup_objectStreamFrame_atBatchPrefix canonical startup matched
    earlier batch later fifo
    (split ▸ valid) (split ▸ started) ⟨input :: tail, batchEq.symm⟩
  have batchValid : ValidGraphEvents work (earlier.flatten ++ batch) :=
    valid.prefix ⟨later.flatten, by simp [split, List.append_assoc]⟩
  have checked : ((State.initialize (Work.fromExecution work) startup)).batchesStarted
      (earlier ++ batch :: later) = true := by
    rw [← split, ← inputsStartedWithStartup_eq_batchesStarted]
    exact started
  have accepted := State.acceptsBatch_streamAction_live (fifo := fifo) (event := input) batchValid
    (((State.initialize (Work.fromExecution work) startup)).batchesStarted_eachBatch
      earlier batch later
      checked) ⟨tail, by simp [batchEq]⟩ ⟨(stream.ref, closing), action⟩
  have active : stream.ref ∈
      ((((State.initialize (Work.fromExecution work) startup)).replayBatches
      earlier).replayGraphEvents fifo (GraphEvent.availableFailures batch)).rootStreams := by
    cases input <;> simp only [GraphEvent.streamAction] at action
    all_goals try contradiction
    all_goals
      have refEq := (Prod.mk.inj (Option.some.inj action)).1
      simpa [State.acceptsGraphEvent, refEq] using accepted
  have prior : received.IsPrefix batches.flatten := by
    refine ⟨input :: (tail ++ later.flatten), ?_⟩
    simp only [split, List.flatten_append, List.flatten_cons, batchEq, beforeEq,
      List.append_assoc, List.cons_append]
  let initial := State.initialize (Work.fromExecution work) startup
  let entry := initial.replayBatches earlier
  have checkedParts : initial.batchesStarted earlier = true
      ∧ entry.batchesStarted (batch :: later) = true := by
    simpa only [State.batchesStarted_append, Bool.and_eq_true] using checked
  have running := (entry.batchesStarted_cons batch later checkedParts.2).1
  have retiredHealthy : (entry.replayGraphEvents fifo (GraphEvent.availableFailures batch)
      ).UncancelledRetiredHealthy work
        (startup.failures.map Prod.fst ++ GraphEvent.failureSettlements batches.flatten) := by
    intro node ancestors record retired uncancelled invalid
    have retainedRetirement : UncancelledRetirement
        (entry.replayGraphEvents fifo (GraphEvent.availableFailures batch)) node.ref :=
      ⟨retired, uncancelled⟩
    have suffix := retainedRetirement.replayGraphEvents (input :: tail) (GraphEvent.availableFailures batch)
    have whole : UncancelledRetirement
        (entry.replayGraphEvents batch (GraphEvent.availableFailures batch)) node.ref := by
      rw [← State.replayGraphEvents_append entry fifo (input :: tail)
        (GraphEvent.availableFailures batch), ← batchEq] at suffix
      exact suffix
    obtain ⟨terminal, same⟩ := entry.handleGraphEvents_stateCore batch running
    have atEnd := whole.withTerminated terminal
    rw [← same] at atEnd
    have final := atEnd.replayBatches later
    have finalFrame := generated.startup_runNormalized_frame canonical startup matched
      batches valid started
    have health := (finalFrame.retiredHealth_withInitialFailures generated canonical matched valid).1
    have stateEq : (initial.runNormalized batches).1
        = (entry.handleGraphEvents batch).1.replayBatches later := by
      rw [State.runNormalized_replayBatches, split, State.replayBatches_append]
      rfl
    rw [stateEq] at health
    exact health node ancestors record final.retired final.uncancelled invalid
  rw [← beforeEq] at frame
  exact frame.activeObjectStreamHealthy_of_itemSafety generated canonical
    (valid.prefix prior) known active failedPayloads retiredHealthy objectsRecorded
    itemsSafe contributors

/-- A nonfailure stream atom is healthy whenever strictly earlier source items are safe.
Both initial availability and later source cuts are retained without consuming a synthetic
initial callback or assuming output admission.
-/
theorem ExecutedWork.startup_atomicObjectStreamHealthy_of_earlierItems
    {work batches streams failures matching stream dependencies source index event
      closing}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    (cuts
      : StreamFailureCuts work
          ((((State.initialize (Work.fromExecution work) startup)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) streams)
    (partition
      : failures.Perm (streams ++ startup.informativeObjectFailureCuts work batches))
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    (selected
      : ((((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (action : streamAction event = some (stream.ref, closing))
    (nonfailure : ∀ node errors, event ≠ .streamFailure node errors)
    : let atoms :=
        (((State.initialize (Work.fromExecution work) startup)).runNormalized
          batches).2.flatten.flatMap
          publicationAtoms
      ∃ before input after,
        batches.flatten = before ++ input :: after
        ∧ input.streamAction = some (stream.ref, closing)
        ∧ (before.flatMap GraphEvent.itemPublications).length
          ≤ ((atoms.take index).flatMap normalizedItemValues).length
        ∧ ((∀ address ordinal,
              Occurrence.item address ordinal ∈ before.flatMap GraphEvent.successes
              → ¬TaskCancelled work matching (atoms.take index) failures
                  (.item address ordinal))
            → ¬TaskCancelled work matching (atoms.take index) failures
                (.executionGroup source)
              ∧ ¬NodeFailed work matching (atoms.take index) failures stream.ref) := by
  let queue := (State.initialize (Work.fromExecution work) startup)
  let objects := startup.informativeObjectFailureCuts work batches
  let atoms :=
    (queue.runNormalized batches).2.flatten.flatMap
      publicationAtoms
  have objectKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨owners, producer, path, errors, descriptor⟩ :=
      startup.objectReportingCuts_objectOrigin matched generated valid entry
        ((selectObjectFailureCuts_sublist work [] _).subset member)
    exact ⟨owners, producer, path, errors, descriptor⟩
  have failedPayloads : ∀ cut occurrence,
      (cut, occurrence) ∈ failures
      → ∃ owners producer payload,
          TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true := by
    intro cut occurrence member
    rcases List.mem_append.mp (partition.mem_iff.mp member) with fromStream | fromObject
    · obtain ⟨owner, errors, parent, _, descriptor⟩ := cuts.2 _ fromStream
      exact ⟨_, _, _, descriptor, rfl⟩
    · obtain ⟨owners, parent, path, errors, descriptor⟩ := objectKnown _ fromObject
      exact ⟨_, _, _, descriptor, rfl⟩
  obtain ⟨before, input, after, split, sameAction, actualCut, _ledger, count⟩ :=
    startup_atomicStream_sourcePrefix startup valid started selected action
  refine ⟨before, input, after, split, sameAction, count, ?_⟩
  intro itemsSafe
  have length : (atoms.take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  apply generated.startup_activeObjectStreamHealthy_atSourceCut startup matched valid
    started known sameAction actualCut failedPayloads ?_ itemsSafe ?_
  · intro occurrence owners producer path result descriptor member
    rw [length] at member
    have objectMember := (cuts.object_mem_iff partition descriptor).mp member
    exact startup.informativeObjectFailureCuts_source_subset work batches index objectMember
  · intro occurrence owners descriptor owner member
    rw [length] at member
    exact cuts.no_failure_at_action_mixed partition objectKnown generated
      (State.startup_runNormalized_atomicStreamActions_ordered startup valid)
      known selected action nonfailure descriptor owner member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
