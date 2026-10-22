import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupObjectReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamSourceOrder

/-! Actual startup output has one complete error inventory across group and stream reports. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Joint object reporting entries always retain object-failure descriptors. -/
theorem InitialStartup.objectReportingCuts_objectOrigin {work : Execution.Work}
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : ∀ entry ∈ startup.objectReportingCuts work batches,
        ∃ owners producer path errors,
          TaskAt work entry.2 owners producer (.object path (.error errors)) := by
  let initial := State.initialize (Work.fromExecution work) startup
  let refs := (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  intro entry member
  change entry ∈ prependInitialReporting (startup.reportingCuts work refs) _ at member
  rcases List.mem_append.mp member with early | later
  · obtain ⟨occurrence, included, same⟩ := List.mem_map.mp early
    obtain ⟨⟨other, errors⟩, supplied, identity⟩ := List.mem_map.mp
      (InitialStartup.mem_reportingOccurrences.mp included).1
    dsimp only at identity
    subst other
    obtain ⟨owners, path, known⟩ := InitialStartup.matched_rootFailure matched supplied
    rw [← same]
    exact ⟨owners, none, path, errors, known⟩
  · obtain ⟨owners, producer, path, errors, known⟩ :=
      generated.startup_objectAvailability_objectOrigin startup matched valid
        (List.mem_filter.mp later).1
    exact ⟨owners, producer, path, errors, known⟩

/-- Exact stream completion sources supply ordered failed-item cuts and reachability.
This does not assert prior announcements or absence of causal cancellation.
-/
theorem ExecutedWork.startup_streamFailureCuts_origins {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∃ failures : FailureCuts,
        StreamFailureCuts work events failures
        ∧ (failures.map Prod.snd).Nodup
        ∧ ∀ entry ∈ failures, Reachable work entry.2 := by
  dsimp only
  let initial := State.initialize (Work.fromExecution work) startup
  let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
  let property := fun index occurrence =>
    StreamFailureOrigin work events (index, occurrence) ∧ Reachable work occurrence
  obtain ⟨failures, positions, evidence⟩ :=
    choose_indexed_witnesses (streamFailurePositions events) property (by
      intro index member
      obtain ⟨stream, errors, atFailure⟩ := mem_streamFailurePositions.mp member
      have source := initial.runNormalized_startup_streamCompletion_source batches
        (List.mem_of_getElem? atFailure) rfl
      obtain ⟨address, ordinal, producer, known, reachable, _⟩ :=
        valid.streamFailure_itemInventory generated source
      exact ⟨.item address ordinal, ⟨stream, errors, producer, atFailure, known⟩, reachable⟩)
  have cuts : StreamFailureCuts work events failures :=
    ⟨positions, fun entry member => (evidence entry member).1⟩
  exact ⟨failures, cuts,
    cuts.unique (State.startup_runNormalized_atomicStreamActions_ordered startup valid),
    fun entry member => (evidence entry member).2⟩

/-- One fresh mixed inventory explains every exact group aggregate and stream cause.
Initial availability is retained once, later duplicate object observations reuse it,
and stream entries keep their actual output positions. Causal licensing is separate.
-/
theorem ExecutedWork.startup_completeFailureInventory_for_streams {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true) {streams : FailureCuts}
    (cuts
      : let initial := State.initialize (Work.fromExecution work) startup
        StreamFailureCuts work
          ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms)
          streams)
    (reaches : ∀ entry ∈ streams, Reachable work entry.2)
    : let initial := State.initialize (Work.fromExecution work) startup
      let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      CompleteFailureInventory work events
        (mergeFailureCuts (startup.objectReportingCuts work batches) streams) := by
  dsimp only
  let initial := State.initialize (Work.fromExecution work) startup
  let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
  let objects := startup.objectReportingCuts work batches
  obtain ⟨objectWitness, objectCauses⟩ :=
    generated.startup_objectReportingWitness startup matched valid started
  have metadata := reporting_metadata objectWitness
  have origins := startup.objectReportingCuts_objectOrigin matched generated valid
  have partition := mergeFailureCuts_partition objects streams
  refine ⟨
    mergeFailureCuts_ordered metadata.1 (cuts.ordered.imp Nat.le_of_lt),
    cuts.mixed_unique (State.startup_runNormalized_atomicStreamActions_ordered startup valid)
      metadata.2 origins partition, ?_, ?_, ?_⟩
  · intro entry member
    rcases List.mem_append.mp (partition.mem_iff.mp member) with stream | object
    · obtain ⟨node, errors, producer, _, known⟩ := cuts.2 entry stream
      exact ⟨Nat.le_of_lt (cuts.bound stream), reaches entry stream,
        [node.ref], producer, _, known, rfl⟩
    · obtain ⟨bound, owners, producer, payload, known, failed, reachable, _⟩ :=
        reporting_entry objectWitness object
      exact ⟨bound, reachable, owners, producer, payload, known, failed⟩
  · intro index group errors selected
    exact nodeFailureCauses_group_mixed (objectCauses index group errors selected) partition
  · intro index stream errors selected
    obtain ⟨occurrence, member⟩ := cuts.covers selected
    obtain ⟨node, count, producer, atFailure, known⟩ := cuts.2 _ member
    obtain ⟨rfl, rfl⟩ := Execution.WorkQueueEvent.streamFailure.inj
      (Option.some.inj (atFailure.symm.trans selected))
    have cause := cuts.nodeErrors (State.startup_runNormalized_atomicStreamActions_ordered
      startup valid) selected (generated.taskFailure_positive known rfl)
    apply cause.mono
    intro occurrence present
    exact (failedBefore_partition partition index).mem_iff.mpr (List.mem_append_left _ present)

/-- Every actual startup prefix has one complete mixed diagnostic inventory.
Its stream cuts and object availability come from this same source replay.
-/
theorem ExecutedWork.startup_completeFailureInventory {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∃ failures : FailureCuts, CompleteFailureInventory work events failures := by
  obtain ⟨streams, cuts, _, reaches⟩ := generated.startup_streamFailureCuts_origins startup valid
  exact ⟨_, generated.startup_completeFailureInventory_for_streams startup matched valid started
    cuts reaches⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
