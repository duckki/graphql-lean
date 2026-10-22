import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupActivationSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureReporting

/-! Initial aggregate notices have distinct, reachable reporting causes at the initial cut. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every initial queued failure refers to a group in the initial announcement frontier. -/
theorem State.initializeWithStartup_failure_refs (input : Work) (startup : InitialStartup)
    : let initial := State.initialize input startup
      ∀ failure ∈ initial.groupFailureEvents,
        failure.group.ref ∈ initial.initialGroups.map Execution.DeliveryNode.ref := by
  dsimp only
  unfold State.initialize
  simpa only [State.enqueueGroupFailures, State.startNewWork_groupFailureEvents,
    State.pruneEmptyGroups_groupFailureEvents, State.maybeIntegrateWork_groupFailureEvents,
    List.nil_append] using State.startNewWork_failure_refs _ _ startup.failures

/-- Initial synchronous observations concern producer-free failing tasks. -/
theorem InitialStartup.matched_rootFailure {work startup occurrence errors}
    (matched : InitialStartup.MatchesWork startup work)
    (member : (occurrence, errors) ∈ startup.failures)
    : ∃ owners path,
        TaskAt work occurrence owners none (.object path (.error errors)) := by
  obtain ⟨owners, producer, path, known⟩ := (matched.2 occurrence errors member).1
  obtain ⟨otherOwners, otherProducer, payload, task, ready⟩ :=
    (matched.2 occurrence errors member).2
  have same := (known.unique task).2.1
  have free : producer = none := by
    cases producer with
    | none => rfl
    | some source =>
        exact False.elim (List.not_mem_nil (ready source same.symm))
  rw [free] at known
  exact ⟨owners, path, known⟩

/-- A proof-only reporting inventory selects supplied failures with an announced owner.
It supplies availability evidence; it does not add a runtime cache or causal settlement.
-/
noncomputable def InitialStartup.reportingOccurrences (startup : InitialStartup)
    (work : Execution.Work) (initial : NodeRefs)
    : List Occurrence := by
  classical
  exact (startup.failures.map Prod.fst).filter (fun occurrence => decide
    (∃ owners, TaskHasOwners work occurrence owners ∧ ∃ ref ∈ owners, ref ∈ initial))

/-- The selected inventory contains exactly supplied failures licensed by an initial owner. -/
theorem InitialStartup.mem_reportingOccurrences {startup work initial occurrence}
    : occurrence ∈ InitialStartup.reportingOccurrences startup work initial
      ↔ occurrence ∈ startup.failures.map Prod.fst
        ∧ ∃ owners,
            TaskHasOwners work occurrence owners ∧ ∃ ref ∈ owners, ref ∈ initial := by
  classical
  simp [InitialStartup.reportingOccurrences]

/-- Initial reporting records one zero output cut per selected occurrence. -/
noncomputable def InitialStartup.reportingCuts (startup : InitialStartup)
    (work : Execution.Work) (initial : NodeRefs)
    : FailureCuts :=
  (startup.reportingOccurrences work initial).map (fun occurrence => (0, occurrence))

/-- Every selected cause is available at every output boundary starting with initialization. -/
theorem InitialStartup.failedBefore_reportingCuts (startup : InitialStartup)
    (work : Execution.Work) (initial : NodeRefs) (cut : Nat)
    : failedBefore (startup.reportingCuts work initial) cut
      = startup.reportingOccurrences work initial := by
  simp [failedBefore, InitialStartup.reportingCuts, List.filter_map, List.map_map,
    Function.comp_def]

/-- Initial reporting availability is fresh and licensed independently of causal cuts. -/
theorem InitialStartup.reportingWitness {startup work initial}
    (matched : InitialStartup.MatchesWork startup work)
    (events : List Execution.WorkQueueEvent)
    : FailureReportingWitness work initial events
        (startup.reportingCuts work initial) := by
  classical
  have selectedDistinct : (startup.reportingOccurrences work initial).Nodup :=
    matched.1.sublist List.filter_sublist
  have distinct : ((startup.reportingCuts work initial).map Prod.snd).Nodup := by
    simpa [InitialStartup.reportingCuts, List.map_map, Function.comp_def]
      using selectedDistinct
  intro before cut occurrence after split
  have member : (cut, occurrence) ∈ startup.reportingCuts work initial := by simp [split]
  obtain ⟨selected, included, identity⟩ := List.mem_map.mp member
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj identity
  obtain ⟨supplied, owners, ⟨producer, payload, task⟩, ref, contributes, announced⟩ :=
    InitialStartup.mem_reportingOccurrences.mp included
  obtain ⟨⟨address, errors⟩, available, same⟩ := List.mem_map.mp supplied
  dsimp only [Prod.fst] at same
  subst address
  obtain ⟨rootOwners, path, root⟩ := InitialStartup.matched_rootFailure matched available
  have groups := (root.unique task).1
  refine ⟨
    Nat.zero_le _,
    ?_,
    ?_,
    rootOwners,
    none,
    .object path (.error errors),
    root,
    ?_,
    .root ⟨rootOwners, .object path (.error errors), root⟩,
    ref,
    groups.symm ▸ contributes,
    ?_
  ⟩
  · intro earlier prior
    have entry : earlier ∈ startup.reportingCuts work initial := by
      rw [split]
      exact List.mem_append_left _ prior
    obtain ⟨other, _, same⟩ := List.mem_map.mp entry
    have zero := congrArg Prod.fst same
    dsimp only at zero
    omega
  · rw [split, List.map_append, List.map_cons] at distinct
    intro prior
    exact (List.nodup_append.mp distinct).2.2 _ prior _ List.mem_cons_self rfl
  · simp [Payload.failure]
  · simpa [announcedRefs, pendingRefs] using announced

/-- Every queued initial aggregate is supported by the same initial reporting inventory. -/
theorem ExecutedWork.initialStartup_reportingCauses {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      ∀ failure ∈ initial.groupFailureEvents,
        NodeFailureCauses work (failedBefore (startup.reportingCuts work refs) 0)
          failure.group.ref failure.errors := by
  dsimp only
  let initialized := State.initialize (Work.fromExecution work) startup
  let refs := (initialized.initialGroups ++ initialized.initialStreams).map
    Execution.DeliveryNode.ref
  intro failure emitted
  have announced : failure.group.ref ∈ refs := by
    change failure.group.ref ∈
      (initialized.initialGroups ++ initialized.initialStreams).map Execution.DeliveryNode.ref
    rw [List.map_append]
    exact List.mem_append_left _
      (State.initializeWithStartup_failure_refs _ startup failure emitted)
  obtain ⟨causes, nonempty, distinct, supported, total⟩ :=
    generated.initialStartup_failure_nodeCauses startup matched failure emitted
  rw [InitialStartup.failedBefore_reportingCuts]
  refine ⟨causes, nonempty, distinct, ?_, total⟩
  intro occurrence count member
  have known := supported occurrence count member
  refine ⟨InitialStartup.mem_reportingOccurrences.mpr ⟨known.1, ?_⟩, known.2⟩
  obtain ⟨owners, producer, payload, task, contributes, failed, positive⟩ := known.2
  exact ⟨owners, ⟨producer, payload, task⟩, failure.group.ref, contributes, announced⟩

/-- One fresh reporting witness supports every initial aggregate at every later output cut.
Earlier availability is reused without recording the same occurrence a second time.
This does not claim that reporting availability itself licenses causal cancellation.
-/
theorem ExecutedWork.initialStartup_reportingWitness {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (events : List Execution.WorkQueueEvent)
    : let initial := State.initialize (Work.fromExecution work) startup
      let refs :=
        (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
      ∃ reported,
        FailureReportingWitness work refs events reported
        ∧ ∀ failure ∈ initial.groupFailureEvents,
            ∀ cut,
              NodeFailureCauses work (failedBefore reported cut) failure.group.ref
                failure.errors := by
  dsimp only
  let initial := State.initialize (Work.fromExecution work) startup
  let refs := (initial.initialGroups ++ initial.initialStreams).map Execution.DeliveryNode.ref
  refine ⟨startup.reportingCuts work refs, InitialStartup.reportingWitness matched events, ?_⟩
  intro failure emitted cut
  have supported := generated.initialStartup_reportingCauses startup matched failure emitted
  rw [InitialStartup.failedBefore_reportingCuts] at supported ⊢
  exact supported

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
