import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupStartup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConstructorInitialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedTaskErrors
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Initial synchronous activation retains valid notices and supported aggregate reports. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial activation introduces only rejections licensed by its explicit availability. -/
theorem State.initializeWithStartup_taskRejections (input : Work)
    (startup : InitialStartup) (property : Occurrence → Nat → Prop)
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ startup.failures → property occurrence errors)
    : (State.initialize input startup).TaskRejectionsSatisfy property := by
  have empty : ({} : State).TaskRejectionsSatisfy property := by
    intro node member
    cases member
  unfold State.initialize
  exact ((empty.maybeIntegrateWork input).pruneEmptyGroups _).startNewWork _
    startup.failures licensed

/-- Every initial queued completion has positive errors when its task causes do. -/
theorem State.initializeWithStartup_failure_positive (input : Work)
    (startup : InitialStartup)
    (positive : ∀ occurrence errors, (occurrence, errors) ∈ startup.failures → 0 < errors)
    : ∀ failure ∈ (State.initialize input startup).groupFailureEvents,
        0 < failure.errors := by
  have empty : ({} : State).TaskRejectionsSatisfy (fun _ errors => 0 < errors) := by
    intro node member
    cases member
  unfold State.initialize
  simpa only [State.enqueueGroupFailures, State.startNewWork_groupFailureEvents,
    State.pruneEmptyGroups_groupFailureEvents,
    State.maybeIntegrateWork_groupFailureEvents, List.nil_append]
    using State.startNewWork_failure_positive
      ((empty.maybeIntegrateWork input).pruneEmptyGroups _) _ startup.failures positive

/-- Initial aggregation uses distinct task causes from the original executed work.
Neither diagnostic totals nor unsupported positive counts can explain an initial notice.
-/
theorem ExecutedWork.initialStartup_failure_nodeCauses {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work)
    : ∀ failure ∈ (State.initialize (Work.fromExecution work) startup).groupFailureEvents,
        NodeFailureCauses work (startup.failures.map Prod.fst) failure.group.ref
          failure.errors := by
  let input := Work.fromExecution work
  have emptyRejected : ({} : State).TaskRejectionsSatisfy
      (fun occurrence errors => (occurrence, errors) ∈ startup.failures) := by
    intro node member
    cases member
  have emptyUnique : ({} : State).TaskMembershipsUnique := by
    intro node member
    cases member
  have emptySound : ({} : State).GroupMembershipSound := by
    intro node member
    cases member
  have emptyMatching : ({} : State).RegisteredTasksMatch work := by
    intro task member
    cases member
  have tasks : ∀ task ∈ input.tasks, TaskMatches work task := by
    intro task member
    obtain ⟨address, payload, identity, known⟩ := workFromSpec_tasks_taskAt Located.root member
    exact ⟨⟨address, payload, none, identity, known⟩,
      workFromSpec_tasks_groupsExact Located.root member⟩
  unfold State.initialize
  simp only [State.enqueueGroupFailures, State.startNewWork_groupFailureEvents,
    State.pruneEmptyGroups_groupFailureEvents, State.maybeIntegrateWork_groupFailureEvents,
    List.nil_append]
  apply State.startNewWork_failure_nodeCauses
    ((emptyRejected.maybeIntegrateWork input).pruneEmptyGroups _)
    ((emptyUnique.maybeIntegrateWork input).pruneEmptyGroups _)
    ((emptySound.maybeIntegrateWork input).pruneEmptyGroups _)
    ((emptyMatching.maybeIntegrateWork input tasks).pruneEmptyGroups _)
  · intro occurrence errors member
    exact member
  · intro occurrence errors member
    obtain ⟨owners, producer, path, known⟩ := (matched.2 occurrence errors member).1
    refine ⟨List.mem_map_of_mem member, owners, producer, .object path (.error errors),
      known, rfl, ?_⟩
    simpa [Payload.failure] using generated.taskFailure_positive known (by rfl)

/-- Immediate startup removal does not erase the independently valid initial notices. -/
theorem ExecutedWork.initializesWithStartup {work : Execution.Work}
    (generated : ExecutedWork work) (nonempty : work.size ≠ 0) (startup : InitialStartup)
    : let initialized := State.initialize (Work.fromExecution work) startup
      Initializes work initialized.initialGroups initialized.initialStreams := by
  dsimp only
  rw [State.initializeWithStartup_initialGroups, State.initializeWithStartup_initialStreams]
  exact generated.initializes nonempty

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
