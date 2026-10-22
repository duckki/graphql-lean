import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupFailureTotals
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialReportingMerge
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupClosureNotices

/-! One fresh available reporting inventory covers every startup-aware failed group. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Source-label freshness supplies distinct later reporting occurrences,
independently of startup. -/
theorem State.startup_sourceObjectFailureCuts_unique {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      let publisher : IncrementalPublisher :=
        { active := initial.initialGroups ++ initial.initialStreams }
      ((sourceObjectFailureCuts 0 (initial.sourceRunBlocks publisher batches).2.2).map
        Prod.snd).Nodup := by
  dsimp only
  rw [sourceObjectFailureCuts_occurrences]
  apply List.Nodup.sublist ?_ valid.identities_nodup.1
  exact ((State.sourceRunBlocks_inputs _ _ _).filterMap
    GraphEvent.objectFailure?).trans (GraphEvent.objectFailures_sublist _)

/-- Each later reporting entry retains its exact failed descriptor,
reachability and output bound. -/
theorem ExecutedWork.startup_sourceObjectFailureCuts_origin {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      let publisher : IncrementalPublisher :=
        { active := initial.initialGroups ++ initial.initialStreams }
      ∀ entry ∈ sourceObjectFailureCuts 0 (initial.sourceRunBlocks publisher batches).2.2,
        entry.1
          ≤ ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).length
        ∧ ∃ owners producer path errors,
            TaskAt work entry.2 owners producer (.object path (.error errors))
            ∧ Reachable work entry.2 := by
  dsimp only
  intro entry member
  obtain ⟨errors, source⟩ := sourceObjectFailureCuts_source member
  have received := (State.sourceRunBlocks_inputs _ _ _).subset source
  obtain ⟨owners, producer, path, known⟩ := valid.eachMatches received
  refine ⟨?_, owners, producer, path, errors, known,
    valid.taskFailure_reachable generated received⟩
  have bound := (sourceObjectFailureCuts_bounds _ _ entry member).2
  simpa only [Nat.zero_add, (State.sourceRunBlocks_withPublisher_agrees _ _ _).2.2,
    State.runNormalized] using bound

/-- Later source failure cuts are licensed for reporting at their own actual output positions.
No prior-cancellation claim is made about reporting availability.
-/
theorem ExecutedWork.startup_sourceObjectFailureCuts_reportingWitness
    {work : Execution.Work} (generated : ExecutedWork work) (startup : InitialStartup)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      let publisher : IncrementalPublisher :=
        { active := initial.initialGroups ++ initial.initialStreams }
      let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      FailureReportingWitness work refs events
        (sourceObjectFailureCuts 0 (initial.sourceRunBlocks publisher batches).2.2) := by
  dsimp only
  intro before cut occurrence after split
  let initial := State.initialize (Work.fromExecution work) startup
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  have member : (cut, occurrence) ∈ sourceObjectFailureCuts 0
      (initial.sourceRunBlocks publisher batches).2.2 := by
    rw [show sourceObjectFailureCuts 0
      (initial.sourceRunBlocks publisher batches).2.2
      = before ++ (cut, occurrence) :: after from split]
    simp
  obtain ⟨bound, owners, producer, path, errors, known, reachable⟩ :=
    generated.startup_sourceObjectFailureCuts_origin startup valid _ member
  obtain ⟨otherOwners, owner, ⟨_, _, descriptor⟩, contributes, announced⟩ :=
    State.startup_sourceObjectFailureCuts_announcedOwner startup valid started member
  rw [← (known.unique descriptor).1] at contributes
  have ordered := sourceObjectFailureCuts_ordered 0
    (initial.sourceRunBlocks publisher batches).2.2
  have distinct := State.startup_sourceObjectFailureCuts_unique startup valid
  dsimp only at distinct
  rw [split] at ordered
  rw [split, List.map_append, List.map_cons] at distinct
  refine ⟨bound, ?_, ?_, owners, producer, _, known, rfl, reachable,
    owner, contributes, announced⟩
  · intro earlier included
    exact (List.pairwise_append.mp ordered).2.2 earlier included _ List.mem_cons_self
  · intro prior
    exact (List.nodup_append.mp distinct).2.2 _ prior _ List.mem_cons_self rfl

/-- Source callbacks and report causes retain their actual availability cuts.
Initial observations license cause provenance without becoming runtime input events. -/
noncomputable def InitialStartup.objectAvailabilityCandidates (startup : InitialStartup)
    (work : Execution.Work) (batches : List (List GraphEvent))
    : FailureCuts :=
  let initial := State.initialize (Work.fromExecution work) startup
  let refs :=
    (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  let blocks := (initial.sourceRunBlocks publisher batches).2.2
  interleaveFailureCuts (sourceObjectFailureCuts 0 blocks)
    (groupReportCandidateCuts work
      (startup.reportingObservations work refs ++ blocks.filterMap Prod.fst) 0
      (blocks.flatMap Prod.snd))

/-- Each occurrence is retained at its first demonstrated callback or report availability. -/
noncomputable def InitialStartup.objectAvailabilityCuts (startup : InitialStartup)
    (work : Execution.Work) (batches : List (List GraphEvent))
    : FailureCuts :=
  firstReportingCuts [] (startup.objectAvailabilityCandidates work batches)

/-- Availability candidates retain their original nondecreasing output positions. -/
theorem InitialStartup.objectAvailabilityCandidates_ordered (startup : InitialStartup)
    (work : Execution.Work) (batches : List (List GraphEvent))
    : (startup.objectAvailabilityCandidates work batches).Pairwise
        (fun left right => left.1 ≤ right.1) :=
  interleaveFailureCuts_ordered (sourceObjectFailureCuts_ordered _ _)
    (groupReportCandidateCuts_ordered _ _ _ _)

/-- Each later availability entry has its reachable failed descriptor and prior owner notice. -/
theorem ExecutedWork.startup_objectAvailability_reportingWitness {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      FailureReportingWitness work refs events
        (startup.objectAvailabilityCuts work batches) := by
  dsimp only
  let initial := State.initialize (Work.fromExecution work) startup
  let refs := (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  let blocks := (initial.sourceRunBlocks publisher batches).2.2
  let observations := startup.reportingObservations work refs ++ blocks.filterMap Prod.fst
  have output : blocks.flatMap Prod.snd =
      (initial.runNormalized batches).2.flatten.flatMap publicationAtoms :=
    (initial.sourceRunBlocks_withPublisher_agrees publisher batches).2.2
  have ordered := (startup.objectAvailabilityCandidates_ordered work batches).sublist
    (firstReportingCuts_sublist [] _)
  have distinct := firstReportingCuts_distinct [] (startup.objectAvailabilityCandidates work batches)
  have sourceWitness := generated.startup_sourceObjectFailureCuts_reportingWitness startup valid started
  intro before cut occurrence after split
  have member : (cut, occurrence) ∈ startup.objectAvailabilityCuts work batches := by simp [split]
  have raw := (firstReportingCuts_sublist [] _).subset member
  have partition := interleaveFailureCuts_partition (sourceObjectFailureCuts 0 blocks)
    (groupReportCandidateCuts work observations 0 (blocks.flatMap Prod.snd))
  have origin : (cut, occurrence) ∈ groupReportCandidateCuts work observations 0 (blocks.flatMap Prod.snd)
      ∨ (cut, occurrence) ∈ sourceObjectFailureCuts 0 blocks :=
    List.mem_append.mp (partition.mem_iff.mp raw)
  have facts : cut ≤ ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).length
      ∧ ∃ owners producer payload,
          TaskAt work occurrence owners producer payload
          ∧ payload.failure.isSome = true ∧ Reachable work occurrence
          ∧ ∃ ref ∈ owners, ref ∈ announcedRefs refs
              (((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).take cut) := by
    rcases origin with report | source
    · obtain ⟨index, group, errors, count, atReport, sameCut, part⟩ :=
        groupReportCandidateCuts_origin report
      simp only [Nat.zero_add] at sameCut
      have totals := generated.startup_sourceRunBlocks_groupFailureTotals startup matched valid started
      have sources := totals group errors (List.mem_of_getElem? atReport)
      obtain ⟨received, owners, producer, path, known, contributes⟩ :=
        (groupReportSourceParts_spec sources).2.2.2 occurrence count part
      have actual := atReport
      rw [output] at actual
      have announced := State.startup_runNormalized_groupClosureAnnouncedAt (ref := group.ref) startup valid actual
        (by simp [groupClosureRefs])
      have reachable : Reachable work occurrence := by
        rcases List.mem_append.mp received with early | later
        · obtain ⟨rootOwners, rootPath, root⟩ := InitialStartup.matched_rootFailure matched
            (InitialStartup.mem_reportingObservations.mp early).1
          exact .root ⟨rootOwners, _, root⟩
        · exact valid.taskFailure_reachable generated ((initial.sourceRunBlocks_inputs publisher batches).subset later)
      refine ⟨?_, owners, producer, .object path (.error count), known, rfl, reachable,
        group.ref, contributes, ?_⟩
      · have bounded := (groupReportCandidateCuts_bounds work observations 0
          (blocks.flatMap Prod.snd) (cut, occurrence) report).2
        simpa only [Nat.zero_add, output] using bounded
      · simpa only [sameCut, Nat.zero_add] using announced
    · exact reporting_entry sourceWitness source
  change (startup.objectAvailabilityCuts work batches).Pairwise (fun left right => left.1 ≤ right.1) at ordered
  change ((startup.objectAvailabilityCuts work batches).map Prod.snd).Nodup at distinct
  refine ⟨facts.1, ?_, ?_, facts.2⟩
  · rw [split] at ordered
    intro entry included
    exact (List.pairwise_append.mp ordered).2.2 entry included _ List.mem_cons_self
  · rw [split, List.map_append, List.map_cons] at distinct
    intro prior
    exact (List.nodup_append.mp distinct).2.2 _ prior _ List.mem_cons_self rfl

/-- Selected availability entries retain fixed failed object descriptors without start assumptions. -/
theorem ExecutedWork.startup_objectAvailability_objectOrigin {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (_matched : startup.MatchesWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) {entry : Nat × Occurrence}
    (member : entry ∈ startup.objectAvailabilityCuts work batches)
    : ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
  classical
  let initial := State.initialize (Work.fromExecution work) startup
  let refs := (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  let blocks := (initial.sourceRunBlocks publisher batches).2.2
  let observations := startup.reportingObservations work refs ++ blocks.filterMap Prod.fst
  have raw := (firstReportingCuts_sublist [] _).subset member
  have origin := (interleaveFailureCuts_partition (sourceObjectFailureCuts 0 blocks)
    (groupReportCandidateCuts work observations 0 (blocks.flatMap Prod.snd))).mem_iff.mp raw
  rcases List.mem_append.mp origin with report | source
  · obtain ⟨index, group, errors, count, _, _, part⟩ := groupReportCandidateCuts_origin report
    have sources : GroupFailureSources work observations group.ref errors := by
      apply Classical.byContradiction
      intro absent
      simp only [groupReportSourceParts, dite_eq_right absent, List.not_mem_nil] at part
    obtain ⟨_, owners, producer, path, known, _⟩ :=
      (groupReportSourceParts_spec sources).2.2.2 entry.2 count part
    exact ⟨owners, producer, path, count, known⟩
  · obtain ⟨_, owners, producer, path, errors, known, _⟩ :=
      generated.startup_sourceObjectFailureCuts_origin startup valid entry source
    exact ⟨owners, producer, path, errors, known⟩

/-- Initial availability and later callback/report evidence share one fresh reporting inventory. -/
noncomputable def InitialStartup.objectReportingCuts (startup : InitialStartup)
    (work : Execution.Work) (batches : List (List GraphEvent))
    : FailureCuts :=
  let initial := State.initialize (Work.fromExecution work) startup
  let refs :=
    (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  prependInitialReporting (startup.reportingCuts work refs)
    (startup.objectAvailabilityCuts work batches)

/-- Every actual aggregate has its complete distinct causes available by the report cut. -/
theorem ExecutedWork.startup_objectReportingCuts_groupCauses {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true) {index : Nat}
    {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : let initial := State.initialize (Work.fromExecution work) startup
        ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : NodeFailureCauses work
        (failedBefore (startup.objectReportingCuts work batches) index) group.ref
        errors := by
  let initial := State.initialize (Work.fromExecution work) startup
  let refs := (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  let blocks := (initial.sourceRunBlocks publisher batches).2.2
  let observations := startup.reportingObservations work refs ++ blocks.filterMap Prod.fst
  have atBlocks : (blocks.flatMap Prod.snd)[index]? = some (.groupFailure group errors) := by
    rw [(initial.sourceRunBlocks_withPublisher_agrees publisher batches).2.2]
    exact atEvent
  have totals := generated.startup_sourceRunBlocks_groupFailureTotals startup matched valid started
  have sources := totals group errors (List.mem_of_getElem? atBlocks)
  obtain ⟨nonempty, distinct, total, supported⟩ := groupReportSourceParts_spec sources
  refine ⟨
    groupReportSourceParts work observations group.ref errors,
    nonempty,
    distinct,
    ?_,
    total.symm
  ⟩
  intro occurrence count member
  obtain ⟨_, owners, producer, path, known, contributes⟩ := supported occurrence count member
  refine ⟨?_, owners, producer, _, known, contributes, rfl,
    generated.taskFailure_positive known rfl⟩
  have raw := groupReportCandidateCuts_atReport (offset := 0) atBlocks member
  have candidate : (index, occurrence) ∈ startup.objectAvailabilityCandidates work batches := by
    apply (interleaveFailureCuts_partition (sourceObjectFailureCuts 0 blocks)
      (groupReportCandidateCuts work observations 0 (blocks.flatMap Prod.snd))).mem_iff.mpr
    exact List.mem_append_left _ (by simpa only [Nat.zero_add] using raw)
  obtain ⟨kept, retained, same, earlier⟩ := firstReportingCuts_earlier (seen := [])
    (startup.objectAvailabilityCandidates_ordered work batches) candidate (by simp)
  apply prependInitialReporting_later (startup.reportingCuts work refs)
    (startup.objectAvailabilityCuts work batches)
    (by
      intro entry listed
      obtain ⟨other, _, identity⟩ := List.mem_map.mp listed
      exact (congrArg Prod.fst identity).symm)
    index
  have identity : kept = (kept.1, occurrence) := Prod.ext rfl same
  exact mem_failedBefore (identity ▸ retained) earlier

/-- One reporting witness supports all exact group counts without duplicate occurrences. -/
theorem ExecutedWork.startup_objectReportingWitness {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      FailureReportingWitness work refs events (startup.objectReportingCuts work batches)
      ∧ ∀ index group errors,
          events[index]? = some (.groupFailure group errors)
          → NodeFailureCauses work
              (failedBefore (startup.objectReportingCuts work batches) index) group.ref
              errors := by
  refine ⟨prependInitialReporting_witness (InitialStartup.reportingWitness matched _)
    (generated.startup_objectAvailability_reportingWitness startup matched valid started) ?_, ?_⟩
  · intro entry member
    obtain ⟨occurrence, _, same⟩ := List.mem_map.mp member
    exact (congrArg Prod.fst same).symm
  · intro index group errors atEvent
    exact generated.startup_objectReportingCuts_groupCauses startup matched valid started atEvent

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
