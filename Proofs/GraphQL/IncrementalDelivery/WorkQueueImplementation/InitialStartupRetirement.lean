import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupAccounting

/-! Initial activation preserves live roots and uncancelled retirement before notification. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial pruning retires empty shells without introducing cancellation markers. -/
theorem initialPreparation_cancelledGroups_empty (work : Execution.Work)
    : (initialPreparation work).1.cancelledGroups = [] := by
  dsimp only [initialPreparation]
  rw [State.pruneEmptyGroups_cancelledGroups, State.maybeIntegrateWork_cancelledGroups,
    State.addGroups_cancelledGroups_empty rfl]

/-- No root is active before the initial frontier is released. -/
theorem initialPreparation_rootGroups_empty (work : Execution.Work)
    : (initialPreparation work).1.rootGroups = [] := by
  dsimp only [initialPreparation]
  rw [State.pruneEmptyGroups_rootGroups, State.maybeIntegrateWork_rootGroups]

/-- Every initial contributor has its owner link before startup and cache exposure. -/
theorem initialPreparation_uncancelledTaskAccounting (work : Execution.Work)
    (generated : ExecutedWork work)
    : (initialPreparation work).1.UncancelledTaskAccounting [] := by
  let lowered := Work.fromExecution work
  let integrated := ({} : State).maybeIntegrateWork lowered
  have empty : ({} : State).UncancelledTaskAccounting [] := by
    intro task member; cases member
  have unique : ({} : State).GroupRefsUnique := by simp [State.GroupRefsUnique]
  have certificate := generated.declarations.lower (Located.root (root := work))
  have accounted := empty.maybeIntegrateWork_of_present unique lowered none (by
    intro task member ref contributes _
    obtain ⟨group, included, same⟩ :=
      workFromSpec_immediateGroupsCoverTasks work [] generated.declarations
        task member ref contributes
    have present := ({} : State).addGroups_registersRefs lowered.groups generated
      (by intro node member; cases member)
      (fun _ member => workFromSpec_groups_recordAt_root member)
      certificate.parentRefs group included (generated.empty_registrationSupported _)
    rwa [same] at present)
  exact accounted.pruneEmptyGroups (unique.maybeIntegrateWork lowered)
    integrated.2.newGroups

/-- Pruned initial roots have retired ancestors, and pruning closes healthy retirement. -/
theorem ExecutedWork.initialPreparation_retirement {work : Execution.Work}
    (generated : ExecutedWork work)
    : (∀ node ∈ (initialPreparation work).2.newGroups,
        (initialPreparation work).1.AncestorsRetired work node.ref)
      ∧ (initialPreparation work).1.UncancelledRetiredAncestors work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have pruned := State.maybeIntegrateWork_prune_retirement (queue := {}) (failed := [])
    generated (by intro node member; cases member) (by intro node member; cases member)
    canonical (by intro node member; cases member) (by intro task member; cases member)
    (Work.fromExecution work)
    (fun group member =>
      let ⟨dependencies, record, _⟩ := workFromSpec_groups_recordAt_root member
      ⟨dependencies, record⟩)
    (fun group member => workFromSpec_groups_parentCanonical_root canonical member)
    (workFromSpec_immediateGroupsCoverTasks work [] generated.declarations)
    (generated.declarations.lower (Located.root (root := work))).parentRefs
  refine ⟨pruned.1, (pruned.2 ?_).uncancelled_of_empty⟩
  intro ref retired
  exact False.elim (List.not_mem_nil retired.1)

/-- The initial pruned frontier is live and consists of supported contributing roots. -/
theorem initialPreparation_frontier {work : Execution.Work}
    : (initialPreparation work).1.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
      ∧ (∀ node ∈ (initialPreparation work).2.newGroups,
          node.ref
          ∈ (initialPreparation work).1.groupNodes.map
              (fun group => group.group.node.ref))
      ∧ (∀ node ∈ (initialPreparation work).2.newGroups,
          ∃ dependencies, NodeHasDependencies work node.ref .group dependencies) := by
  let lowered := Work.fromExecution work
  let integrated := ({} : State).maybeIntegrateWork lowered
  have supported := (State.GroupRefSupport.empty
      (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    |>.maybeIntegrateWork lowered (by
      intro task member group owner
      obtain ⟨address, payload, identity, known⟩ :=
        workFromSpec_tasks_taskAt (Located.root (root := work)) member
      have matching : TaskMatches work task :=
        ⟨⟨address, payload, none, identity, known⟩,
          workFromSpec_tasks_groupsExact Located.root member⟩
      exact matching.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩))
  have pruned := supported.pruneEmptyGroups integrated.2.newGroups
  refine ⟨pruned.1, ?_, pruned.2⟩
  intro node member
  have unique : ({} : State).GroupRefsUnique := by simp [State.GroupRefsUnique]
  exact integrated.1.pruneEmptyGroups_keptPresent integrated.2.newGroups
    (unique.maybeIntegrateWork lowered) node.ref (List.mem_map_of_mem member)

/-- Synchronous failed activation preserves every uncancelled owner link. -/
theorem State.initializeWithStartup_uncancelledTaskAccounting (work : Execution.Work)
    (generated : ExecutedWork work)
    (startup : InitialStartup)
    : State.UncancelledTaskAccounting
        (State.initialize (Work.fromExecution work) startup) [] := by
  rw [State.initializeWithStartup_eq_preparation]
  exact (initialPreparation_uncancelledTaskAccounting work generated).startNewWork
    (initialPreparation work).2 startup.failures

private theorem rootReplayFrame_withNotices {queue : State} {work parents}
    (frame : RootReplayFrame queue work parents)
    (groupFailureEvents : List GroupFailureEvent)
    (initialGroups initialStreams : List Execution.DeliveryNode)
    : RootReplayFrame
        ({ queue with groupFailureEvents, initialGroups, initialStreams } : State) work
        parents :=
  ⟨
    ⟨
      frame.live.refs,
      frame.live.records,
      frame.live.links,
      frame.live.registered,
      frame.live.tasks,
      frame.live.roots,
      ⟨frame.live.support.contents, frame.live.support.roots⟩,
      frame.live.present
    ⟩,
    frame.retired
  ⟩

/-- Generated initial activation retains live roots and structurally closed retirement. -/
theorem ExecutedWork.initialStartup_rootReplayFrame {work parents}
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup)
    : RootReplayFrame (State.initialize (Work.fromExecution work) startup)
        work parents := by
  have parent := initialPreparation_parentCutFrame generated canonical
  have retirement := generated.initialPreparation_retirement
  have frontier := initialPreparation_frontier (work := work)
  have emptyRoots : (initialPreparation work).1.RootAncestorsRetired work := by
    intro ref active
    rw [initialPreparation_rootGroups_empty] at active
    cases active
  have present : (initialPreparation work).1.RootGroupsPresent := by
    intro ref active
    rw [initialPreparation_rootGroups_empty] at active
    cases active
  have live : LiveRootFrame (initialPreparation work).1 work parents :=
    ⟨parent.keys, parent.records, parent.links, parent.live, parent.tasks, emptyRoots,
      frontier.1, present⟩
  have started := live.startNewWork (initialPreparation work).2 retirement.1
    frontier.2.1 frontier.2.2 startup.failures
  have retired := retirement.2.startNewWork (initialPreparation work).2 startup.failures
  rw [State.initializeWithStartup_eq_preparation]
  exact rootReplayFrame_withNotices ⟨started, retired⟩ _ _ _

/-- Startup cancellation markers always name permanently retired registered groups. -/
theorem State.initializeWithStartup_cancellationsRetired (work : Execution.Work)
    (generated : ExecutedWork work)
    (startup : InitialStartup)
    : (State.initialize (Work.fromExecution work) startup).CancellationsRetired := by
  have empty : (initialPreparation work).1.CancellationsRetired := by
    intro ref member
    rw [initialPreparation_cancelledGroups_empty] at member
    cases member
  have prepared := initialPreparation_pendingAccounting work generated.declarations
  rw [State.initializeWithStartup_eq_preparation]
  exact empty.startNewWork prepared.liveGroups (initialPreparation work).2
    startup.failures

/-- Startup removal retains uncancelled ancestor markers without consuming a failure. -/
theorem ExecutedWork.initialStartup_uncancelledRetiredMarkers {work}
    {parents : Nat → NodeRefs}
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup)
    : State.UncancelledRetiredMarkers
        (State.initialize (Work.fromExecution work) startup) work := by
  have parent := initialPreparation_parentCutFrame generated canonical
  have tasks := initialPreparation_taskOwnerFrame work
  have emptyReject : ({} : State).TaskRejectionsSatisfy
      (fun occurrence _ => occurrence ∉ ([] : List Occurrence)) := by
    intro node member; cases member
  have rejected := (emptyReject.maybeIntegrateWork (Work.fromExecution work)).pruneEmptyGroups
    (({} : State).maybeIntegrateWork (Work.fromExecution work)).2.newGroups
  have markers := State.UncancelledRetiredMarkers.of_empty work
    (initialPreparation_cancelledGroups_empty work)
  rw [State.initializeWithStartup_eq_preparation]
  exact markers.startNewWork generated.initialPreparation_retirement.2
    (initialPreparation_uncancelledTaskAccounting work generated) generated parent.links
    parent.records tasks.sound tasks.matching canonical rejected
    (initialPreparation work).2 startup.failures
    (by intro occurrence errors member; exact List.not_mem_nil)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
