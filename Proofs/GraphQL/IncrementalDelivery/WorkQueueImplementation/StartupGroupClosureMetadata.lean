import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReportingAvailability
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationLedger

/-! Actual startup group completions retain their exact contributor descriptors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Startup preserves contributor support for all populated and active group refs. -/
theorem State.initializeWithStartup_groupRefSupport (input : Work)
    (startup : InitialStartup) (supported : NodeRef → Prop)
    (owners : ∀ task ∈ input.tasks, ∀ group ∈ task.groups, supported group.ref)
    : (State.initialize input startup).GroupRefSupport supported := by
  have integrated := (State.GroupRefSupport.empty supported).maybeIntegrateWork input owners
  obtain ⟨pruned, groups⟩ := integrated.pruneEmptyGroups
    (({} : State).maybeIntegrateWork input).2.newGroups
  have started := pruned.startNewWork
    { (({} : State).maybeIntegrateWork input).2 with newGroups :=
        ((({} : State).maybeIntegrateWork input).1.pruneEmptyGroups
          (({} : State).maybeIntegrateWork input).2.newGroups).2 } groups startup.failures
  unfold State.initialize
  exact ⟨started.contents, started.roots⟩

/-- Startup retains the original registration descriptor for every queued group notice. -/
theorem ExecutedWork.initialStartup_queuedGroupRecords {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    : (State.initialize (Work.fromExecution work) startup).QueuedGroupRecords work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registered := (initialPreparation_parentCutFrame generated canonical).records
  unfold State.QueuedGroupRecords
  unfold State.initialize
  simpa only [initialPreparation, State.enqueueGroupFailures,
    State.startNewWork_groupFailureEvents, State.pruneEmptyGroups_groupFailureEvents,
    State.maybeIntegrateWork_groupFailureEvents, List.nil_append]
    using registered.startNewWork_failureRecords (initialPreparation work).2
      startup.failures

/-- Each queued initial failure retains its exact announced structural descriptor. -/
theorem ExecutedWork.initialStartup_failure_located {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    : ∀ failure ∈ (State.initialize (Work.fromExecution work) startup).groupFailureEvents,
        ∃ dependencies producer,
          NodeAt work failure.group .group dependencies producer := by
  have records := generated.initialStartup_queuedGroupRecords startup
  intro failure member
  obtain ⟨dependencies, record⟩ := records failure member
  have noticed := State.initializeWithStartup_failure_refs (Work.fromExecution work) startup
    failure member
  rw [State.initializeWithStartup_initialGroups] at noticed
  obtain ⟨group, included, same⟩ := List.mem_map.mp noticed
  obtain ⟨owners, known⟩ := generated.initialGroups_nodeAt included
  exact generated.record_contributor record ⟨owners, group, none, known, same⟩

/-- A raw batch starting in a supported registry and forwarding known initial failures
closes only exact original group descriptors. Its FIFO state remains the ordinary handler
state; the supplied local tail is used only as output provenance evidence.
-/
theorem State.startup_handleGraphEvents_groupClosuresLocated {queue : State}
    {work : Execution.Work} (generated : ExecutedWork work)
    (records : queue.GroupNodesMatchWork work)
    (queued : queue.QueuedGroupRecords work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : ∀ event ∈ (queue.handleGraphEvents events).2, event.GroupClosureLocated work := by
  have metadata := (records.handleGraphEvents_groupClosureRecords queued events matching).2
  have contributors := (support.handleGraphEvents_support registered tasks events matching).2
  intro event member
  have record := metadata event member
  have supported := contributors event member
  cases event <;> try trivial
  all_goals
    obtain ⟨dependencies, known⟩ := record
    exact generated.record_contributor known supported

/-- Publisher normalization retains the complete descriptor of every group closure. -/
theorem IncrementalPublisher.normalizeBatch_groupClosuresLocated {work events}
    (publisher : IncrementalPublisher)
    (known : ∀ event ∈ events, WorkQueueEvent.GroupClosureLocated work event)
    : ∀ event ∈ (publisher.normalizeBatch events).2, GroupClosureLocated work event := by
  have one (publisher : IncrementalPublisher) (event : WorkQueueEvent)
      (known : event.GroupClosureLocated work)
      : ∀ output ∈ (publisher.handleWorkQueueEvent event).2,
          GroupClosureLocated work output := by
    cases event <;> simp_all [IncrementalPublisher.handleWorkQueueEvent,
      WorkQueueEvent.GroupClosureLocated, GroupClosureLocated]
  induction events generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      intro output member
      rcases List.mem_append.mp member with first | later
      · exact one publisher event (known event List.mem_cons_self) output first
      · exact ih _ (fun next member => known next (List.mem_cons_of_mem _ member)) output later

/-- Every completion in the actual seeded publisher has exact group-node provenance.
The initial failure tail is checked separately and consumed once; later batches use their
own source payloads and cache snapshots. No notification history is synthesized.
-/
theorem ExecutedWork.startup_runNormalized_groupClosuresLocated {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∀ event ∈ (initial.runNormalized batches).2.flatten,
        GroupClosureLocated work event := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (registry : acc.1.GroupNodesMatchWork work)
      (queued : acc.1.QueuedGroupRecords work)
      (support : acc.1.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
      (registered : acc.1.StartedTasksRegistered)
      (tasks : acc.1.RegisteredTasksMatch work)
      (output : ∀ event ∈ acc.2.2.flatten, GroupClosureLocated work event)
      (matching : ∀ batch ∈ more, ∀ event ∈ batch, event.MatchesWork work)
      : ∀ event ∈ (more.foldl normalizedStep acc).2.2.flatten,
          GroupClosureLocated work event := by
    induction more generalizing acc with
    | nil => exact output
    | cons batch rest ih =>
        have batchMatch := matching batch List.mem_cons_self
        have nextSupport := support.handleGraphEvents_support registered tasks batch batchMatch
        have emitted := acc.2.1.normalizeBatch_groupClosuresLocated
          (acc.1.startup_handleGraphEvents_groupClosuresLocated generated registry queued support
            registered tasks batch batchMatch)
        rw [List.foldl_cons]
        apply ih
        · rw [normalizedStep_queue]
          exact registry.handleGraphEvents batch batchMatch
        · rw [normalizedStep_queue]
          exact (registry.handleGraphEvents_groupClosureRecords queued batch batchMatch).1
        · rw [normalizedStep_queue]
          exact nextSupport.1
        · rw [normalizedStep_queue]
          exact registered.handleGraphEvents batch
        · rw [normalizedStep_queue]
          exact tasks.handleGraphEvents batch batchMatch
        · rw [normalizedStep_flatten]
          intro event member
          exact (List.mem_append.mp member).elim (output event) (emitted event)
        · exact fun next member => matching next (List.mem_cons_of_mem _ member)
  let initial := State.initialize (Work.fromExecution work) startup
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have records := (generated.initialStartup_parentCutFrame canonical startup).records
  have owners := State.initializeWithStartup_taskOwnerFrame work startup
  have supported : initial.GroupRefSupport
      (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
    apply State.initializeWithStartup_groupRefSupport
    intro task member group contributes
    obtain ⟨address, payload, identity, known⟩ := workFromSpec_tasks_taskAt Located.root member
    have matching : TaskMatches work task :=
      ⟨⟨address, payload, none, identity, known⟩,
        workFromSpec_tasks_groupsExact Located.root member⟩
    exact matching.contributorKnown (List.mem_map.mpr ⟨group, contributes, rfl⟩)
  have replay := loop batches (initial, publisher, []) records
    (generated.initialStartup_queuedGroupRecords startup) supported
    owners.registered owners.matching
    (by intro event impossible; cases impossible)
    (fun batch member event listed => valid.eachMatches
      (List.mem_flatten.mpr ⟨batch, member, listed⟩))
  exact replay

/-- Atomization retains the same exact startup group descriptors and creates no closure. -/
theorem ExecutedWork.startup_runNormalized_atomicGroupClosuresLocated
    {work : Execution.Work} (generated : ExecutedWork work) (startup : InitialStartup)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∀ event ∈ (initial.runNormalized batches).2.flatten.flatMap publicationAtoms,
        GroupClosureLocated work event := by
  dsimp only
  intro event member
  obtain ⟨carrier, emitted, atom⟩ := List.mem_flatMap.mp member
  exact (generated.startup_runNormalized_groupClosuresLocated startup valid carrier emitted).atoms
    event atom

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
