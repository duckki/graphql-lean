import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupCompleteFailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SelectedFailureCuts

/-! Startup causal selection preserves group invalidation and separate aggregate availability. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Select informative object causes from the fresh joint reporting inventory.
This changes no source event, output, diagnostic total or executable queue state.
-/
noncomputable def InitialStartup.informativeObjectFailureCuts (startup : InitialStartup)
    (work : Execution.Work) (batches : List (List GraphEvent))
    : FailureCuts :=
  selectObjectFailureCuts work [] (startup.objectReportingCuts work batches)

private theorem aggregate_invalidated {work failed ref errors}
    (causes : NodeFailureCauses work failed ref errors)
    : GroupInvalidated work failed ref := by
  obtain ⟨causes, nonempty, _, supported, _⟩ := causes
  cases causes with
  | nil => exact False.elim (nonempty rfl)
  | cons cause rest =>
      obtain ⟨available, owners, producer, payload, known, contributes, _, _⟩ :=
        supported cause.1 cause.2 List.mem_cons_self
      exact .task ⟨producer, payload, known⟩ contributes available

/-- Selected startup object causes and actual stream cuts form one causal inventory.
The selection retains the same output positions and all group invalidation, while exact
aggregate totals remain in the separate reporting inventory. This does not license
causal settlements against prior cancellation or prove event admission.
-/
theorem ExecutedWork.startup_causalFailureInventory_for_streams {work : Execution.Work}
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
      CausalFailureInventory work events
        (mergeFailureCuts (startup.informativeObjectFailureCuts work batches)
          streams) := by
  dsimp only
  let initial := State.initialize (Work.fromExecution work) startup
  let reportedObjects := startup.objectReportingCuts work batches
  let objects := startup.informativeObjectFailureCuts work batches
  have selected : objects.Sublist reportedObjects := selectObjectFailureCuts_sublist work [] _
  obtain ⟨witness, groupCauses⟩ :=
    generated.startup_objectReportingWitness startup matched valid started
  have metadata := reporting_metadata witness
  have objectKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    exact startup.objectReportingCuts_objectOrigin matched generated valid entry
      (selected.subset member)
  have partition := mergeFailureCuts_partition objects streams
  refine ⟨
    mergeFailureCuts_ordered (metadata.1.sublist selected)
      (cuts.ordered.imp Nat.le_of_lt),
    cuts.mixed_unique
      (State.startup_runNormalized_atomicStreamActions_ordered startup valid)
      (metadata.2.sublist (selected.map Prod.snd)) objectKnown partition,
    ?_,
    ?_,
    ?_
  ⟩
  · intro entry member
    rcases List.mem_append.mp (partition.mem_iff.mp member) with stream | object
    · obtain ⟨node, errors, producer, _, known⟩ := cuts.2 entry stream
      exact ⟨Nat.le_of_lt (cuts.bound stream), reaches entry stream,
        [node.ref], producer, _, known, rfl⟩
    · obtain ⟨bound, owners, producer, payload, known, failed, reachable, _⟩ :=
        reporting_entry witness (selected.subset object)
      exact ⟨bound, reachable, owners, producer, payload, known, failed⟩
  · intro index group errors atEvent
    have invalid := aggregate_invalidated (groupCauses index group errors atEvent)
    have retained := (selectObjectFailureCuts_failedBefore_groupInvalidated work []
      reportedObjects index group.ref metadata.1).mp (by simpa only [List.nil_append] using invalid)
    simp only [List.nil_append] at retained
    apply retained.mono
    intro occurrence member
    exact (failedBefore_partition partition index).mem_iff.mpr (List.mem_append_right _ member)
  · intro index stream errors atEvent
    exact cuts.nodeErrors_mixed partition objectKnown generated
      (State.startup_runNormalized_atomicStreamActions_ordered startup valid) atEvent

/-- Actual startup replay has compatible causal and complete diagnostic inventories.
Every causal entry uses reporting availability at the same or an earlier output cut.
Contributor announcements and absence of prior cancellation are independent of these
inventory certificates.
-/
theorem ExecutedWork.startup_failureInventories {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∃ failures reported : FailureCuts,
        CausalFailureInventory work events failures
        ∧ CompleteFailureInventory work events reported
        ∧ CausalFailuresAvailable failures reported := by
  obtain ⟨streams, cuts, _, reaches⟩ := generated.startup_streamFailureCuts_origins startup valid
  refine ⟨_, _, generated.startup_causalFailureInventory_for_streams startup matched valid
    started cuts reaches, generated.startup_completeFailureInventory_for_streams startup matched
      valid started cuts reaches, ?_⟩
  have selected := selectObjectFailureCuts_sublist work []
    (startup.objectReportingCuts work batches)
  have causalPartition := mergeFailureCuts_partition
    (startup.informativeObjectFailureCuts work batches) streams
  have reportPartition := mergeFailureCuts_partition
    (startup.objectReportingCuts work batches) streams
  intro cut occurrence member
  refine ⟨cut, ?_, Nat.le_refl _⟩
  rcases List.mem_append.mp (causalPartition.mem_iff.mp member) with stream | object
  · exact reportPartition.mem_iff.mpr (List.mem_append_left _ stream)
  · exact reportPartition.mem_iff.mpr (List.mem_append_right _ (selected.subset object))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
