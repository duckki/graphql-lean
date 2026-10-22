import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupCausalFailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamAnnouncements

/-! Startup causal and diagnostic inventories retain their own prior contributor notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Joint object/stream reporting has the prior announcements required by its own cuts. -/
theorem ExecutedWork.startup_reportingWitness_for_streams {work : Execution.Work}
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
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      FailureReportingWitness work refs events
        (mergeFailureCuts (startup.objectReportingCuts work batches) streams) := by
  apply (generated.startup_completeFailureInventory_for_streams startup matched valid
    started cuts reaches).failureReportingWitness
  intro entry member
  have partition := mergeFailureCuts_partition (startup.objectReportingCuts work batches) streams
  rcases List.mem_append.mp (partition.mem_iff.mp member) with stream | object
  · obtain ⟨node, errors, producer, selected, known⟩ := cuts.2 entry stream
    exact ⟨[node.ref], ⟨producer, _, known⟩, node.ref, List.mem_cons_self,
      State.startup_runNormalized_streamAnnouncedAt startup valid selected List.mem_cons_self⟩
  · have witness := (generated.startup_objectReportingWitness startup matched valid started).1
    obtain ⟨_, owners, producer, payload, known, _, _, ref, owns, announced⟩ :=
      reporting_entry witness object
    exact ⟨owners, ⟨producer, payload, known⟩, ref, owns, announced⟩

private theorem announced_take_mono {events : List Execution.WorkQueueEvent}
    {initial : NodeRefs} {earlier later : Nat} {ref : NodeRef}
    (announced : ref ∈ announcedRefs initial (events.take earlier))
    (before : earlier ≤ later)
    : ref ∈ announcedRefs initial (events.take later) := by
  rcases List.mem_append.mp announced with first | carried
  · exact List.mem_append_left _ first
  · obtain ⟨event, included, noticed⟩ := List.mem_flatMap.mp carried
    have nested : event ∈ (events.take later).take earlier := by
      simpa only [List.take_take, Nat.min_eq_left before] using included
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨event, List.mem_of_mem_take nested, noticed⟩)

/-- Actual startup replay has compatible, announced causal and diagnostic inventories.
Reporting availability may precede a causal settlement; its contributor's historical
notice remains valid at the later cut. Absence of prior cancellation remains independent.
-/
theorem ExecutedWork.startup_announcedFailureInventories {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∃ streams failures reported : FailureCuts,
        StreamFailureCuts work events streams
        ∧ failures
          = mergeFailureCuts (startup.informativeObjectFailureCuts work batches) streams
        ∧ reported = mergeFailureCuts (startup.objectReportingCuts work batches) streams
        ∧ CausalFailureInventory work events failures
        ∧ CompleteFailureInventory work events reported
        ∧ FailureReportingWitness work refs events reported
        ∧ CausalFailuresAvailable failures reported
        ∧ ∀ entry ∈ failures,
            ∃ owners,
              TaskHasOwners work entry.2 owners
              ∧ ∃ ref ∈ owners, ref ∈ announcedRefs refs (events.take entry.1) := by
  obtain ⟨streams, cuts, _, reaches⟩ := generated.startup_streamFailureCuts_origins startup valid
  let objects := startup.objectReportingCuts work batches
  let causes := startup.informativeObjectFailureCuts work batches
  have report := generated.startup_reportingWitness_for_streams startup matched valid started
    cuts reaches
  have available : CausalFailuresAvailable (mergeFailureCuts causes streams)
      (mergeFailureCuts objects streams) := by
    have selected := selectObjectFailureCuts_sublist work [] objects
    have causalPartition := mergeFailureCuts_partition causes streams
    have reportPartition := mergeFailureCuts_partition objects streams
    intro cut occurrence member
    refine ⟨cut, ?_, Nat.le_refl _⟩
    rcases List.mem_append.mp (causalPartition.mem_iff.mp member) with stream | object
    · exact reportPartition.mem_iff.mpr (List.mem_append_left _ stream)
    · exact reportPartition.mem_iff.mpr (List.mem_append_right _ (selected.subset object))
  refine ⟨
    streams,
    _,
    _,
    cuts,
    rfl,
    rfl,
    generated.startup_causalFailureInventory_for_streams startup matched valid
      started cuts reaches,
    generated.startup_completeFailureInventory_for_streams startup matched
      valid started cuts reaches,
    report,
    available,
    ?_
  ⟩
  intro entry member
  obtain ⟨cut, supplied, earlier⟩ := available entry.1 entry.2 member
  obtain ⟨_, owners, producer, payload, known, _, _, ref, owns, announced⟩ :=
    reporting_entry report supplied
  exact ⟨
    owners,
    ⟨producer, payload, known⟩,
    ref,
    owns,
    announced_take_mono announced earlier
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
