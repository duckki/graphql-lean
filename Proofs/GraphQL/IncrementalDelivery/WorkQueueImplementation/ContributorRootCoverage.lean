import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducedGroupCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFoldCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegionRegistration

/-! Root coverage of healthy permanent task contributors, including latent live groups. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The proof invariant covers contributors without inventing tasks for ancestor shells
-----------------------------------------------------------------------------------------

/-- Each healthy live contributor of a registered task has a concrete active-root path.
`failed` is the accepted object-failure inventory; retired groups are handled separately.
This proof-only predicate imposes no new event-source or public scheduler requirement.
-/
def State.HealthyContributorsCovered (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  ∀ task ∈ queue.tasks,
  ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
    ¬GroupInvalidated work failed ref
    → (∃ node, queue.groupNode? ref = some node)
    → ∃ root ∈ queue.rootGroups, queue.LiveDescendant root ref

/-- Recording additional failures only narrows the healthy contributors requiring coverage.
Witness: contrapose monotonicity of causal group invalidation; reuse the same stored path.
-/
theorem State.HealthyContributorsCovered.mono_failures {queue : State} {work before after}
    (covered : queue.HealthyContributorsCovered work before)
    (included : before.Subset after)
    : queue.HealthyContributorsCovered work after := by
  intro task member ref contributes healthy live
  exact covered task member ref contributes (fun invalid => healthy (invalid.mono included)) live

/-- Every live contributor is covered immediately after generated initialization.
Witness: the stronger initialization theorem covers every surviving group, even taskless ones.
-/
theorem ExecutedWork.initial_healthyContributorsCovered {work : Execution.Work}
    (generated : ExecutedWork work)
    : (State.initialize (Work.fromExecution work)).HealthyContributorsCovered work
        [] := by
  intro _ _ ref _ _ live
  exact generated.initial_live_group_root_coverage ref live

/-- Removing a task's live memberships preserves healthy contributor root coverage.
Witness: the permanent registry and group refs remain unchanged, as do all root paths.
-/
theorem State.HealthyContributorsCovered.removeTask {queue : State} {work failed}
    (covered : queue.HealthyContributorsCovered work failed) (occurrence : Occurrence)
    : (queue.removeTask occurrence).HealthyContributorsCovered work failed := by
  intro task member ref contributes healthy live
  obtain ⟨node, found⟩ := live
  obtain ⟨old, earlier, _⟩ := queue.removeTask_groupEdgesFrom occurrence ref node found
  obtain ⟨root, active, path⟩ := covered task member ref contributes healthy ⟨old, earlier⟩
  exact ⟨root, active, path.removeTask occurrence⟩

/-- A matched registered contributor's health agrees with record-cleanup health.
Witness: exact task contributors are observable group descriptors, unlike taskless shells.
-/
theorem TaskMatches.contributor_recordHealthy {work task failed ref}
    (matching : TaskMatches work task) (generated : ExecutedWork work)
    (contributes : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    (healthy : ¬GroupInvalidated work failed ref)
    : ¬GroupRecordInvalidated work failed ref := by
  obtain ⟨group, member, same⟩ := List.mem_map.mp contributes
  obtain ⟨dependencies, producer, known⟩ := matching.contributorsLocated member
  exact same ▸ (fun invalid => (same.symm ▸ healthy)
    ((generated.groupRecordInvalidated_iff_groupInvalidated known).mp invalid))

-----------------------------------------------------------------------------------------
-- Full successful task handling: old contributors and newly introduced contributors
-----------------------------------------------------------------------------------------

/-- Healthy task success cannot strand an old or newly registered live contributor.
Witness: old paths survive integration; new contributors inherit a producer owner's path.
The original single-pass fold, delayed activation, and final drain preserve those paths.
All hypotheses are independent bookkeeping facts, not admission of the emitted history.
-/
theorem State.HealthyContributorsCovered.taskSuccess
    {queue : State} {work : Execution.Work} {parents settled failed}
    (covered : queue.HealthyContributorsCovered work failed)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work) (generated : ExecutedWork work)
    (records : queue.GroupNodesMatchWork work)
    (retirement : queue.HealthyRetiredAncestors work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (links : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (started : queue.StartedTasksRegistered) (closed : queue.ParentRegistryClosed parents)
    (children : queue.ChildGroupsUnique) (edges : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {occurrence result} (fresh : occurrence ∉ settled)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : (queue.taskSuccess occurrence result).1.HealthyContributorsCovered work failed := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskSuccess, found] using covered
  | some producer =>
      cases guard : queue.taskHasHealthyOwner producer.task with
      | false =>
          simpa [State.taskSuccess, found, guard] using covered.removeTask occurrence
      | true =>
          have producerMember := started producer (List.mem_of_find?_eq_some found)
          have producerOccurrence := (State.taskNode?_some found).2
          let stored := queue.putTaskNode { producer with value := some result.value }
          let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
          have storedRefs : stored.GroupRefsUnique := unique
          have storedCovered : stored.HealthyContributorsCovered work failed := by
            intro task member ref contributes healthy live
            obtain ⟨root, active, path⟩ := covered task member ref contributes healthy live
            exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩
          have storedAccounting : stored.HealthyRegisteredTaskAccounting work settled failed :=
            accounted
          have groupCanonical : ∀ group ∈ result.work.groups,
              group.parent = (parents group.node.ref).head? :=
            fun _ member => matching.taskChildGroups_parentCanonical canonical member
          have descriptors : ∀ group ∈ result.work.groups,
              ∃ dependencies, GroupRecordAt work group.node dependencies :=
            fun _ member => matching.taskChildGroups_recordAt member
          have storedRecords : stored.GroupNodesMatchWork work := records
          have storedChildren : stored.ChildGroupsUnique := children
          have storedEdges : stored.ChildLinksCanonical parents := edges
          have forest : integrated.RemovalForest parents :=
            State.RemovalForest.of_generated generated
              (storedChildren.maybeIntegrateWork result.work (some occurrence))
              (storedEdges.maybeIntegrateWork result.work groupCanonical (some occurrence))
              (storedRecords.maybeIntegrateWork result.work descriptors (some occurrence)) canonical
          intro task member ref contributes healthy survives
          have registeredTask : task ∈ queue.tasks ++ result.work.tasks := by
            rwa [State.taskSuccess_tasks found guard] at member
          have integratedSurvival : ∃ node, integrated.groupNode? ref = some node := by
            obtain ⟨node, lookup⟩ := survives
            obtain ⟨old, earlier, _⟩ := queue.taskSuccess_integration_groupEdgesFrom unique
              found guard ref node lookup
            exact ⟨old, earlier⟩
          apply State.taskSuccess_integrated_root_coverage unique found guard result
            forest ?_ survives
          rcases List.mem_append.mp registeredTask with old | new
          · have priorLive : ∃ node, queue.groupNode? ref = some node := by
              cases earlier : queue.groupNode? ref with
              | some node => exact ⟨node, rfl⟩
              | none =>
                  have retired := (State.RetiredGroup.of_lookup_none
                    (tasks task old ref contributes) earlier).taskSuccess occurrence result
                  obtain ⟨node, lookup⟩ := survives
                  rw [retired.lookup_none] at lookup
                  contradiction
            obtain ⟨root, active, path⟩ := storedCovered task old ref contributes healthy priorLive
            exact ⟨
              root,
              by rwa [State.maybeIntegrateWork_rootGroups],
              path.maybeIntegrateWork storedRefs result.work (some occurrence)
            ⟩
          · have childOwner := matching.childTasksCovered task new ref contributes
            obtain ⟨group, groupMember, sameRef⟩ := childOwner
            have taskMatch : TaskMatches work task := by
              obtain ⟨address, payload, equation, known⟩ := matching.childTask_producer new
              exact ⟨⟨address, payload, some occurrence, equation, known⟩,
                matching.childTask_groupsExact new⟩
            have recordHealthy := taskMatch.contributor_recordHealthy generated contributes healthy
            have childCoverage := storedAccounting.childGroup_integrated_root_coverage
              tracks taskMatching generated records retirement cancelled links storedRefs registered
              tasks closed canonical producerMember (producerOccurrence.symm ▸ fresh)
              (producerOccurrence.symm ▸ matching) groupMember
              ⟨task, new, sameRef.symm ▸ contributes⟩ (sameRef.symm ▸ recordHealthy)
              (by
                intro node included contributor nodeHealthy
                exact storedCovered producer.task producerMember _ contributor nodeHealthy
                  ⟨node, unique.groupNode?_of_mem included⟩)
            rw [producerOccurrence, sameRef] at childCoverage
            exact childCoverage integratedSurvival

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
