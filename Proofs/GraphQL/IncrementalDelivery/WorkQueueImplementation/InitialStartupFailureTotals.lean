import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialFailureTotalsReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupOwnerAccounting

/-! Exact initial and later aggregate diagnostics use one available-observation inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Proof-only descriptors of initially available, announced reporting failures.
These describe rejection evidence; no descriptor is inserted into the host input history.
-/
noncomputable def InitialStartup.reportingObservations (startup : InitialStartup)
    (work : Execution.Work) (initial : NodeRefs)
    : List GraphEvent := by
  classical
  exact (startup.failures.filter (fun failure => decide
    (failure.1 ∈ startup.reportingOccurrences work initial))).map
    (fun failure => GraphEvent.taskFailure failure.1 failure.2)

/-- A reporting observation retains the exact supplied task-boundary count and occurrence. -/
theorem InitialStartup.mem_reportingObservations {startup work initial occurrence errors}
    : GraphEvent.taskFailure occurrence errors
        ∈ InitialStartup.reportingObservations startup work initial
      ↔ (occurrence, errors) ∈ startup.failures
        ∧ occurrence ∈ startup.reportingOccurrences work initial := by
  classical
  constructor
  · intro member
    obtain ⟨⟨task, count⟩, supplied, same⟩ := List.mem_map.mp member
    obtain ⟨rfl, rfl⟩ := GraphEvent.taskFailure.inj same
    simpa only [List.mem_filter, decide_eq_true_eq] using supplied
  · intro supplied
    exact List.mem_map.mpr ⟨(occurrence, errors),
      List.mem_filter.mpr ⟨supplied.1, by simpa using supplied.2⟩, rfl⟩

/-- Every selected initial observation has its exact fixed failed task descriptor. -/
theorem InitialStartup.reportingObservations_match {startup work initial}
    (matched : InitialStartup.MatchesWork startup work)
    : ∀ event ∈ startup.reportingObservations work initial, event.MatchesWork work := by
  intro event member
  obtain ⟨⟨occurrence, errors⟩, supplied, rfl⟩ := List.mem_map.mp member
  exact (matched.2 occurrence errors (List.mem_filter.mp supplied).1).1

/-- Initial activation preserves duplicate-free surviving group task memberships. -/
theorem State.initializeWithStartup_taskMembershipsUnique (work : Work)
    (startup : InitialStartup)
    : (State.initialize work startup).TaskMembershipsUnique := by
  have empty : ({} : State).TaskMembershipsUnique := by intro node member; cases member
  unfold State.initialize
  exact ((empty.maybeIntegrateWork work).pruneEmptyGroups _).startNewWork _
    startup.failures

/-- The initial reporting frame uses only observations with an initially announced owner. -/
theorem State.initializeWithStartup_failureSourceFrame (work : Execution.Work)
    (startup : InitialStartup)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      initial.FailureSourceFrame work (startup.reportingObservations work refs) := by
  dsimp only
  let initial := State.initialize (Work.fromExecution work) startup
  let refs := (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  have facts := State.initializeWithStartup_announcementFacts work startup
  have rejected := State.initializeWithStartup_taskRejections (Work.fromExecution work) startup
    (fun occurrence errors => (occurrence, errors) ∈ startup.failures) (fun _ _ member => member)
  refine ⟨?_, State.initializeWithStartup_taskMembershipsUnique _ startup,
    facts.sound, facts.matching, facts.registered⟩
  intro node member errors rejection
  have supplied := rejected node member errors rejection
  obtain ⟨owner, owns, announced⟩ := facts.known node member
  obtain ⟨⟨_, payload, producer, _, task⟩, _⟩ :=
    facts.matching node.task (facts.registered node member)
  apply InitialStartup.mem_reportingObservations.mpr
  refine ⟨supplied, InitialStartup.mem_reportingOccurrences.mpr
    ⟨List.mem_map_of_mem supplied, node.task.groups.map Execution.DeliveryNode.ref,
      ⟨producer, payload, task⟩, owner.ref, List.mem_map_of_mem owns, ?_⟩⟩
  rw [List.map_append]
  exact List.mem_append_left _ announced

/-- Initial aggregates retain distinct task causes from the initial reporting observations. -/
theorem ExecutedWork.initialStartup_failure_sources {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      ∀ failure ∈ initial.groupFailureEvents,
        GroupFailureSources work (startup.reportingObservations work refs)
          failure.group.ref failure.errors := by
  dsimp only
  intro failure reported
  obtain ⟨causes, nonempty, distinct, supported, total⟩ :=
    generated.initialStartup_reportingCauses startup matched failure reported
  refine ⟨causes, nonempty, distinct, total.symm, ?_⟩
  intro occurrence count member
  obtain ⟨available, owners, producer, payload, task, contributes, failed, positive⟩ :=
    supported occurrence count member
  rw [InitialStartup.failedBefore_reportingCuts] at available
  have supplied := (InitialStartup.mem_reportingOccurrences.mp available).1
  obtain ⟨⟨other, errors⟩, received, identity⟩ := List.mem_map.mp supplied
  dsimp only at identity
  subst other
  obtain ⟨rootOwners, path, root⟩ := InitialStartup.matched_rootFailure matched received
  rw [← (root.unique task).2.2] at failed
  have same : errors = count := Option.some.inj failed
  subst count
  exact ⟨InitialStartup.mem_reportingObservations.mpr ⟨received, available⟩,
    rootOwners, none, path, root, (root.unique task).1 ▸ contributes⟩

/-- Every actual group-failure block retains its exact distinct available diagnostic causes.
Initial observations remain separate evidence from consumed labels, including duplicate
notification of the same initial rejection. No source freshness premise is strengthened.
-/
theorem ExecutedWork.startup_sourceRunBlocks_groupFailureTotals {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (_started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      let publisher : IncrementalPublisher :=
        { active := initial.initialGroups ++ initial.initialStreams }
      SourceBlocksHaveFailureTotals work (startup.reportingObservations work refs)
        (initial.sourceRunBlocks publisher batches).2.2 := by
  apply (State.initializeWithStartup_failureSourceFrame work startup).sourceRunBlocks_initial_totals
    (generated.initialStartup_failure_sources startup matched)
  intro event member
  rcases List.mem_append.mp member with initial | received
  · exact InitialStartup.reportingObservations_match matched event initial
  · exact valid.eachMatches received

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
