import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledReplay

/-! Initial synchronous activation preserves source-independent bookkeeping certificates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- One activation equation covers empty and nonempty initial cache observations. -/
theorem State.initializeWithStartup_eq_preparation (work : Execution.Work)
    (startup : InitialStartup)
    : (State.initialize (Work.fromExecution work) startup)
      = let prepared := initialPreparation work
        let started := prepared.1.startNewWork prepared.2 startup.failures
        {
          started.1.enqueueGroupFailures started.2 with
            initialGroups := prepared.2.newGroups
            initialStreams := prepared.2.newStreams
        } :=
  rfl

/-- Failed startup preserves the complete immediate task catalogue, including skipped work. -/
theorem State.initializeWithStartup_tasks (input : Work) (startup : InitialStartup)
    : (State.initialize input startup).tasks = input.tasks := by
  unfold State.initialize
  dsimp only
  simp only [State.enqueueGroupFailures]
  rw [State.startNewWork_tasks, State.pruneEmptyGroups_tasks,
    State.maybeIntegrateWork_tasks_append]
  rfl

/-- Registration and pruning establish the canonical parent/cancellation frame before activation. -/
theorem initialPreparation_parentCutFrame {work parents}
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : ParentCutFrame (initialPreparation work).1 work parents := by
  have empty : ParentCutFrame {} work parents := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro node member; cases member
    · simp [State.GroupRefsUnique]
    · intro node member; cases member
    · intro node member; cases member
    · intro node member; cases member
    · intro node member; cases member
    · intro task member; cases member
    · intro ref member; cases member
    · intro node member; cases member
    · intro child member; cases member
    · intro ref member; cases member
    · refine ⟨generated.declarations, ?_, ?_, ?_, ?_⟩ <;>
        intro node member <;> cases member
  have integrated := empty.maybeIntegrateWork (Work.fromExecution work)
    (fun _ member => (workFromSpec_groups_recordAt_root member).imp
      (fun _ record => record.1))
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)
    (generated.declarations.lower (Located.root (root := work))) none generated canonical
  exact integrated.pruneEmptyGroups _

private theorem parentCutFrame_withNotices {queue : State} {work parents}
    (frame : ParentCutFrame queue work parents)
    (groupFailureEvents : List GroupFailureEvent)
    (initialGroups initialStreams : List Execution.DeliveryNode)
    : ParentCutFrame
        ({ queue with groupFailureEvents, initialGroups, initialStreams } : State) work
        parents :=
  ⟨
    frame.safe,
    frame.keys,
    frame.records,
    frame.links,
    frame.children,
    frame.live,
    frame.tasks,
    frame.closed,
    frame.fields,
    frame.complete,
    frame.cancelled,
    ⟨
      frame.registration.source,
      frame.registration.live,
      frame.registration.tasks,
      frame.registration.children,
      frame.registration.started
    ⟩
  ⟩

/-- Startup, including immediate rejection removal, retains parent cancellation safety. -/
theorem ExecutedWork.initialStartup_parentCutFrame {work parents}
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup)
    : ParentCutFrame (State.initialize (Work.fromExecution work) startup)
        work parents := by
  rw [State.initializeWithStartup_eq_preparation]
  have frame := (initialPreparation_parentCutFrame generated canonical).startNewWork generated canonical
    (initialPreparation work).2 startup.failures
  exact parentCutFrame_withNotices frame _ _ _

/-- Activation retains the all-owner ledger without treating a cached failure as a settlement. -/
theorem State.PendingAccounting.startNewWork {queue work settled}
    (prior : State.PendingAccounting queue work settled) (released : NewWork)
    (available : List (Occurrence × Nat))
    : (queue.startNewWork released available).1.PendingAccounting work settled := by
  have registration := queue.startNewWork_registration prior.liveGroups prior.taskGroups
    released available
  exact ⟨prior.pending.startNewWork _ available, prior.links.startNewWork _ available,
    prior.refs.startNewWork _ available, prior.memberships.startNewWork _ available,
    registration.1, registration.2, prior.sound.startNewWork _ available,
    prior.matching.startNewWork _ available, prior.started.startNewWork _ available,
    prior.registration.startNewWork _ available⟩

/-- Initial registration supplies safe counters and unsettled links before any task starts. -/
theorem initialPreparation_pendingAccounting (work : Execution.Work)
    (certified : DeclarationCoverage.Certified [] work)
    : (initialPreparation work).1.PendingAccounting work [] := by
  let lowered := Work.fromExecution work
  let integrated := ({} : State).maybeIntegrateWork lowered
  have owners := initialPreparation_taskOwnerFrame work
  have emptyBound : ({} : State).PendingBound (fun _ => True) [] := by
    intro node member; cases member
  have bound := (emptyBound.maybeIntegrateWork lowered).pruneEmptyGroups integrated.2.newGroups
  have links : integrated.1.UnsettledTaskLinks [] :=
    fun task member _ => State.initialWorkTaskLinks lowered task member
  have memberships : ({} : State).TaskMembershipsUnique := by
    intro node member; cases member
  have unique := (memberships.maybeIntegrateWork lowered).pruneEmptyGroups integrated.2.newGroups
  have live : ({} : State).LiveGroupsRegistered := by intro node member; cases member
  have tasks : ({} : State).TaskGroupsRegistered := by intro task member; cases member
  have context : ({} : State).RegistrationFrame work := by
    refine ⟨certified, live, tasks, ?_, ?_⟩ <;> intro node member <;> cases member
  have certificate := certified.lower (Located.root (root := work))
  have registration := ({} : State).maybeIntegrateWork_registration live tasks lowered
    certificate.contributors
  have pruned := integrated.1.pruneEmptyGroups_registration registration.1 registration.2.1
    integrated.2.newGroups
  exact ⟨bound, links.pruneEmptyGroups _, owners.keys, unique, pruned.1, pruned.2.1,
    owners.sound, owners.matching, owners.registered,
    (context.maybeIntegrateWork lowered certificate).1.pruneEmptyGroups _⟩

private theorem pendingAccounting_withNotices {queue : State} {work settled}
    (frame : queue.PendingAccounting work settled)
    (groupFailureEvents : List GroupFailureEvent)
    (initialGroups initialStreams : List Execution.DeliveryNode)
    : ({ queue with groupFailureEvents, initialGroups, initialStreams }
        : State).PendingAccounting
        work settled :=
  ⟨
    frame.pending,
    frame.links,
    frame.refs,
    frame.memberships,
    frame.liveGroups,
    frame.taskGroups,
    frame.sound,
    frame.matching,
    frame.started,
    ⟨
      frame.registration.source,
      frame.registration.live,
      frame.registration.tasks,
      frame.registration.children,
      frame.registration.started
    ⟩
  ⟩

/-- Initial failures leave every surviving group's all-owner counter certificate valid. -/
theorem State.initializeWithStartup_pendingAccounting (work : Execution.Work)
    (certified : DeclarationCoverage.Certified [] work)
    (startup : InitialStartup)
    : (State.initialize (Work.fromExecution work) startup).PendingAccounting work [] := by
  rw [State.initializeWithStartup_eq_preparation]
  have frame := (initialPreparation_pendingAccounting work certified).startNewWork
    (initialPreparation work).2 startup.failures
  exact pendingAccounting_withNotices frame _ _ _

/-- Startup does not change any permanent task's exposed source region. -/
theorem State.initializeWithStartup_regionInventory (work : Execution.Work)
    (startup : InitialStartup)
    : (State.initialize (Work.fromExecution work) startup).RegionInventory work [] := by
  have owners := State.initializeWithStartup_taskOwnerFrame work startup
  have regions : (State.initialize (Work.fromExecution work) startup).RegisteredRegions
      work [] := by
    intro task member
    rw [State.initializeWithStartup_tasks] at member
    exact workFromSpec_tasks_regionCovered Located.root
      (fun _ contains => .inl contains) task member
  have supported : ({} : State).RegisteredRefsCovered work [] := by
    intro ref impossible; cases impossible
  let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  have prepared := (supported.maybeIntegrateWork (Work.fromExecution work)
    (fun _ member => .inl (workFromSpec_group_rootRef work [] member)))
    |>.pruneEmptyGroups integrated.2.newGroups
  have registrations : State.RegisteredRefsCovered
      (State.initialize (Work.fromExecution work) startup)
      work [] := by
    rw [State.initializeWithStartup_eq_preparation]
    exact prepared.startNewWork (initialPreparation work).2 startup.failures
  exact ⟨regions, owners.matching, registrations, owners.registered⟩

/-- Initial producer registration remains complete even for tasks never started after failure. -/
theorem State.initializeWithStartup_producerRegistrationAccounting (work : Execution.Work)
    (startup : InitialStartup)
    : State.ProducerRegistrationAccounting
        (State.initialize (Work.fromExecution work) startup) work [] := by
  intro address owners producer payload known available
  have sourceFree : producer = none := by
    rcases available with root | ⟨source, same, impossible⟩
    · exact root
    · cases impossible
  subst producer
  obtain ⟨task, member, identity, groups⟩ :=
    (createWorkQueue_producerRegistrationAccounting work).root_registered known
  refine .inl ⟨task, ?_, identity, groups⟩
  rw [State.initializeWithStartup_tasks, ← createWorkQueue_tasks]
  exact member

/-- Every initial registered task is producer-free, independently of cache timing. -/
theorem State.initializeWithStartup_producerOrder (work : Execution.Work)
    (startup : InitialStartup)
    : TaskProducersSucceeded work
        (State.initialize (Work.fromExecution work) startup).tasks []
      ∧ ProducerOrder work
          ((State.initialize (Work.fromExecution work) startup).tasks.map
            Task.occurrence) := by
  rw [State.initializeWithStartup_tasks, ← createWorkQueue_tasks]
  exact createWorkQueue_producerOrder work

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
