import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupOwnerPublicationFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupContributorRootReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupTerminalFailureReports
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureExtension

/-! Retired startup contributors publish or have observable licensed cancellation reports. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every uncancelled retired structural contributor has published on the shared matching.
The source-handler ledger and actual startup output retain the same complete object rank.
-/
theorem startup_retiredContributor_published
    {work inputs w address owners producer payload ref} (generated : ExecutedWork work)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    (retired
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.RetiredGroup ref)
    (uncancelled
      : let initial := State.initialize (Work.fromExecution work) startup
        ref ∉ (initial.runNormalized inputs).1.cancelledGroups)
    : Published w.matching w.events (.executionGroup address) := by
  let initial := State.initialize (Work.fromExecution work) startup
  obtain ⟨published, covered, _, interpret, _⟩ := ledger
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := (generated.initialStartup_ownerPublicationFrame canonical startup
    matched).rawBatches
    generated canonical inputs valid (by rwa [← inputsStartedWithStartup_eq_batchesStarted]) covered
  simp only [List.nil_append] at frame
  have state : (initial.rawBatches inputs).1 = (initial.runNormalized inputs).1 :=
    (initial.rawBatches_state inputs).trans
      (initial.runNormalized_replayBatches inputs).symm
  rw [state] at frame
  obtain ⟨value, delivered⟩ := frame.retired_structuralContributor_published generated valid known
    contributes retired uncancelled
  have count : w.events.flatMap normalizedObjectValues
      = (initial.rawBatches inputs).2.flatMap WorkQueueEvent.objectValues := by
    have shape := Witness.startup_rawBatches_shape startup history
    have projection := congrArg (fun events => events.flatMap normalizedObjectValues) shape
    simp only [List.flatMap_assoc, (publicationAtoms_values _).1,
      IncrementalPublisher.normalizeBatch_objectValues] at projection
    split at projection <;> simpa only [List.flatMap_append, List.flatMap_cons,
      normalizedObjectValues, List.flatMap_nil, List.append_nil] using projection.symm
  have complete := interpret w.events.length (Nat.le_refl _) (.executionGroup address)
  simp only [List.take_length] at complete
  apply complete
  rw [count, ← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), delivered, rfl⟩

/-- At termination every registered object task is published or causally cancelled.
A retired uncancelled owner publishes it; each cancelled owner has an actual reported
failure whose licensed scope establishes the same explanation's semantic owner failure.
-/
theorem startup_terminal_registeredTask_accounted {work inputs task} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (explained
      : Explains work (initialQueue work).initialGroups (initialQueue work).initialStreams
          w.events w.matching w.failures)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (registered
      : let initial := State.initialize (Work.fromExecution work) startup
        task ∈ (initial.runNormalized inputs).1.tasks)
    : TaskAccounted work w.matching w.events w.failures task.occurrence := by
  classical
  by_cases published : Published w.matching w.events task.occurrence
  · exact .inr published
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := generated.startup_runNormalized_frame canonical startup matched inputs valid started
  have metadata := frame.pending.matching task registered
  obtain ⟨address, payload, producer, identity, known⟩ := metadata.1
  apply Or.inl
  apply explained.snapshot_taskCancelled
  refine Causality.TaskCancelled.owners ⟨producer, payload, known⟩ published
    (generated.taskOwners_nonempty known) ?_
  intro ref contributes
  have retired := generated.startup_terminal_registeredContributor_retired startup matched valid
    started ended registered contributes
  have cancelled : let initial := State.initialize (Work.fromExecution work) startup
      ref ∈ (initial.runNormalized inputs).1.cancelledGroups := by
    apply Classical.byContradiction
    intro uncancelled
    have delivered := startup_retiredContributor_published generated startup matched valid started
      history ledger (identity ▸ known) contributes retired uncancelled
    exact published (identity.symm ▸ delivered)
  obtain ⟨group, dependencies, descriptor, same⟩ := (identity ▸ known).executionGroup_owner
    contributes
  have report := generated.startup_runNormalized_cancelledRecordsReported startup matched valid
    started ended group dependencies
    (groupRecordAt_of_nodeAt descriptor) (same.symm ▸ cancelled)
  rw [← history] at report
  have failed := report.nodeFailed explained descriptor
  exact explained.nodeFailed_snapshot (same ▸ failed)

/-- Every unpublished registered object has an actual report covering its attachment path.
Uncancelled retirement would have published it; a cancelled contributor supplies its own
or an ancestor's positive completion on the exact observed history.
-/
theorem startup_terminal_registeredTask_reported
    {work inputs task address owners producer payload} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (explained
      : Explains work (initialQueue work).initialGroups (initialQueue work).initialStreams
          w.events w.matching w.failures)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (registered
      : let initial := State.initialize (Work.fromExecution work) startup
        task ∈ (initial.runNormalized inputs).1.tasks)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (identity : task.occurrence = .executionGroup address)
    (unpublished : ¬Published w.matching w.events (.executionGroup address))
    : FailureReportedFor w.events payload.path := by
  classical
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := generated.startup_runNormalized_frame canonical startup matched inputs valid started
  obtain ⟨_, _, _, _, actual⟩ := (frame.pending.matching task registered).1
  have sameOwners := ((identity ▸ actual).unique known).1
  obtain ⟨ref, contributes⟩ := List.exists_mem_of_ne_nil owners
    (generated.taskOwners_nonempty known)
  have retired := generated.startup_terminal_registeredContributor_retired startup matched valid
    started ended registered (sameOwners.symm ▸ contributes)
  have cancelled : let initial := State.initialize (Work.fromExecution work) startup
      ref ∈ (initial.runNormalized inputs).1.cancelledGroups := by
    apply Classical.byContradiction
    intro uncancelled
    exact unpublished (startup_retiredContributor_published generated startup matched valid started
      history ledger known contributes retired uncancelled)
  obtain ⟨group, dependencies, descriptor, same⟩ := known.executionGroup_owner contributes
  have report := generated.startup_runNormalized_cancelledRecordsReported startup matched valid
    started ended group dependencies
    (groupRecordAt_of_nodeAt descriptor) (same.symm ▸ cancelled)
  rw [← history] at report
  exact generated.groupReport_covers_task explained known descriptor
    (same.symm ▸ contributes) report

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
