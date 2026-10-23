import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerExistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalCoverage

/-! Structural frames before and after initial synchronous activation. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Proof notation for root registration and pruning, before any computation is started. -/
def initialPreparation (work : Execution.Work) : State × NewWork :=
  let (integrated, newWork) := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  let (pruned, groups) := integrated.pruneEmptyGroups newWork.newGroups
  (pruned, { newWork with newGroups := groups })

/-- Initial task ownership is sound before activation and before cache exposure. -/
theorem initialPreparation_taskOwnerFrame (work : Execution.Work)
    : (initialPreparation work).1.TaskOwnerFrame work := by
  have empty : ({} : State).TaskOwnerFrame work := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [State.TaskOwnersPresent,
      State.TaskLinkDisposition, State.GroupRefsUnique, State.StartedTasksRegistered,
      State.RegisteredTasksMatch, State.GroupMembershipSound]
  have known : ∀ task ∈ (Work.fromExecution work).tasks, TaskMatches work task := by
    intro task member
    obtain ⟨address, payload, identity, located⟩ := workFromSpec_tasks_taskAt Located.root member
    exact ⟨⟨address, payload, none, identity, located⟩,
      workFromSpec_tasks_groupsExact Located.root member⟩
  exact (empty.maybeIntegrateWork
          (by intro ref impossible; cases impossible)
          (by intro task impossible; cases impossible)
          (Work.fromExecution work)
          known).pruneEmptyGroups
    _

/-- The initial removal forest is derived before starting any task, including failures. -/
theorem ExecutedWork.initialPreparation_removalForest {work : Execution.Work}
    (generated : ExecutedWork work) (parents : Nat → NodeRefs)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (initialPreparation work).1.RemovalForest parents := by
  have emptyChildren : ({} : State).ChildGroupsUnique := by
    intro node impossible
    cases impossible
  have emptyLinks : ({} : State).ChildLinksCanonical parents := by
    intro node impossible
    cases impossible
  have emptyMatching : ({} : State).GroupNodesMatchWork work := by
    intro node impossible
    cases impossible
  have children := emptyChildren.maybeIntegrateWork (Work.fromExecution work)
  have links := emptyLinks.maybeIntegrateWork (Work.fromExecution work)
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)
  have matching := emptyMatching.maybeIntegrateWork (Work.fromExecution work) (by
      intro group member
      obtain ⟨dependencies, known, _⟩ := workFromSpec_groups_recordAt_root member
      exact ⟨dependencies, known⟩)
  exact State.RemovalForest.of_generated generated (children.pruneEmptyGroups _)
    (links.pruneEmptyGroups _) (matching.pruneEmptyGroups _) canonical

private theorem taskOwnerFrame_withNotices {queue : State} {work}
    (frame : queue.TaskOwnerFrame work) (groupFailureEvents : List GroupFailureEvent)
    (initialGroups initialStreams : List Execution.DeliveryNode)
    : ({ queue with groupFailureEvents, initialGroups, initialStreams }
        : State).TaskOwnerFrame
        work :=
  ⟨
    frame.owners,
    frame.disposition,
    frame.keys,
    frame.registered,
    frame.matching,
    frame.sound
  ⟩

/-- Synchronous startup retains the live-task frame used by actual failure removal. -/
theorem State.initializeWithStartup_taskOwnerFrame (work : Execution.Work)
    (startup : InitialStartup)
    : (State.initialize (Work.fromExecution work) startup).TaskOwnerFrame work := by
  unfold State.initialize
  have frame := (initialPreparation_taskOwnerFrame work).startNewWork
    (initialPreparation work).2 startup.failures
  exact taskOwnerFrame_withNotices frame _ _ _

/-- No initial cache observation can invalidate the structural removal forest. -/
theorem ExecutedWork.initialStartup_removalForest {work : Execution.Work}
    (generated : ExecutedWork work) (parents : Nat → NodeRefs)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup)
    : (State.initialize (Work.fromExecution work) startup).RemovalForest parents := by
  have prepared := generated.initialPreparation_removalForest parents canonical
  unfold State.initialize
  apply prepared.of_subset
  exact ((initialPreparation work).1.startNewWork_groupNodes_sublist
    (initialPreparation work).2
    startup.failures).subset

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
