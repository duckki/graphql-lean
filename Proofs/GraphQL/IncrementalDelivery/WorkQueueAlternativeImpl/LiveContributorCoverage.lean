import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiveStreamRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorCoverageReplay

/-! Root coverage of every live permanent contributor, including cached failed owners. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Remove health from the coverage target, not from independent retirement accounting
-----------------------------------------------------------------------------------------

/-- Every live contributor of a permanent task has an active-root path.
This is an internal replay target, not a source law or native acquired-resource inventory.
-/
def State.LiveContributorsCovered (queue : State) : Prop :=
  ∀ task ∈ queue.tasks,
  ∀ key ∈ task.groups.map Execution.DeliveryNode.ref,
    (∃ node, queue.groupNode? key = some node)
    → ∃ root ∈ queue.rootGroups, queue.LiveDescendant root key

/-- Generated initialization covers even taskless surviving records. -/
theorem ExecutedWork.initial_liveContributorsCovered {work : Execution.Work}
    (generated : ExecutedWork work)
    : (State.initialize (Work.fromExecution work)).LiveContributorsCovered := by
  intro _ _ key _ live
  exact generated.initial_live_group_root_coverage key live

/-- Membership cleanup retains all earlier contributor paths. -/
theorem State.LiveContributorsCovered.removeTask {queue : State}
    (covered : queue.LiveContributorsCovered) (occurrence : Occurrence)
    : (queue.removeTask occurrence).LiveContributorsCovered := by
  intro task member key contributes live
  obtain ⟨node, found⟩ := live
  obtain ⟨old, earlier, _⟩ := queue.removeTask_groupEdgesFrom occurrence key node found
  obtain ⟨root, active, path⟩ := covered task member key contributes ⟨old, earlier⟩
  exact ⟨root, active, path.removeTask occurrence⟩

/-- Success covers new live contributors through their actual producer, regardless of health.
Witness: old paths survive registration; the live-ancestor bridge covers new tasks; actual
single-pass closure, delayed activation, and mixed draining preserve surviving paths.
-/
theorem State.LiveContributorsCovered.taskSuccess
    {queue : State} {work : Execution.Work} {parents settled failed}
    (covered : queue.LiveContributorsCovered)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work) (generated : ExecutedWork work)
    (records : queue.GroupNodesMatchWork work)
    (retirement : queue.UncancelledRetiredAncestors work)
    (health : queue.UncancelledRetiredHealthy work failed)
    (safe : queue.LiveParentsUncancelled) (fields : queue.GroupParentsCanonical parents)
    (links : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (started : queue.StartedTasksRegistered) (closed : queue.ParentRegistryClosed parents)
    (children : queue.ChildGroupsUnique) (edges : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {occurrence result} (fresh : occurrence ∉ settled)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : (queue.taskSuccess occurrence result).1.LiveContributorsCovered := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskSuccess, found] using covered
  | some producer =>
      have producerMember := started producer (List.mem_of_find?_eq_some found)
      have producerOccurrence := (State.taskNode?_some found).2
      let stored := queue.putTaskNode { producer with value := some result.value }
      let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
      have storedKeys : stored.GroupRefsUnique := unique
      have storedCovered : stored.LiveContributorsCovered := by
        intro task member key contributes live
        obtain ⟨root, active, path⟩ := covered task member key contributes live
        exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩
      have storedAccounting : stored.HealthyRegisteredTaskAccounting work settled failed := accounted
      have groupCanonical : ∀ group ∈ result.work.groups,
          group.parent = (parents group.node.ref).head? :=
        fun _ member => matching.taskChildGroups_parentCanonical canonical member
      have descriptors : ∀ group ∈ result.work.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies :=
        fun _ member => matching.taskChildGroups_recordAt member
      have storedRecords : stored.GroupNodesMatchWork work := records
      have storedChildren : stored.ChildGroupsUnique := children
      have storedEdges : stored.ChildLinksCanonical parents := edges
      have forest : integrated.RemovalForest parents := State.RemovalForest.of_generated generated
        (storedChildren.maybeIntegrateWork result.work (some occurrence))
        (storedEdges.maybeIntegrateWork result.work groupCanonical (some occurrence))
        (storedRecords.maybeIntegrateWork result.work descriptors (some occurrence)) canonical
      intro task member key contributes survives
      rw [State.taskSuccess_tasks found] at member
      have integratedSurvival : ∃ node, integrated.groupNode? key = some node := by
        obtain ⟨node, lookup⟩ := survives
        obtain ⟨old, earlier, _⟩ := queue.taskSuccess_integration_groupEdgesFrom unique
          found key node lookup
        exact ⟨old, earlier⟩
      apply State.taskSuccess_integrated_root_coverage unique found result
        forest ?_ survives
      rcases List.mem_append.mp member with old | new
      · have priorLive : ∃ node, queue.groupNode? key = some node := by
          cases earlier : queue.groupNode? key with
          | some node => exact ⟨node, rfl⟩
          | none =>
              have retired := (State.RetiredGroup.of_lookup_none
                (tasks task old key contributes) earlier).taskSuccess occurrence result
              obtain ⟨node, lookup⟩ := survives
              rw [retired.lookup_none] at lookup
              contradiction
        obtain ⟨root, active, path⟩ := storedCovered task old key contributes priorLive
        exact ⟨
          root,
          by rwa [State.maybeIntegrateWork_rootGroups],
          path.maybeIntegrateWork storedKeys result.work (some occurrence)
        ⟩
      · obtain ⟨group, groupMember, sameKey⟩ := matching.childTasksCovered task new key contributes
        have childCoverage := storedAccounting.live_childGroup_integrated_root_coverage
          taskMatching generated records retirement health safe fields links storedKeys
          registered tasks closed canonical producerMember (producerOccurrence.symm ▸ fresh)
          (producerOccurrence.symm ▸ matching) groupMember
          ⟨task, new, sameKey.symm ▸ contributes⟩
          (fun key contributes live => storedCovered producer.task producerMember key contributes live)
        rw [producerOccurrence, sameKey] at childCoverage
        exact childCoverage integratedSurvival

-----------------------------------------------------------------------------------------
-- Destructive handlers preserve paths to survivors; fresh items add their own roots
-----------------------------------------------------------------------------------------

/-- Failure preserves coverage of every surviving contributor, including failed ones. -/
theorem State.LiveContributorsCovered.taskFailure {queue : State} {parents}
    (covered : queue.LiveContributorsCovered)
    (unique : queue.GroupRefsUnique) (forest : queue.RemovalForest parents)
    (registered : queue.TaskGroupsRegistered) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.LiveContributorsCovered := by
  intro task member key contributes survives
  rw [State.taskFailure_tasks] at member
  have earlier : ∃ node, queue.groupNode? key = some node := by
    cases found : queue.groupNode? key with
    | some node => exact ⟨node, rfl⟩
    | none =>
        have retired := (State.RetiredGroup.of_lookup_none
          (registered task member key contributes) found).taskFailure occurrence errors
        obtain ⟨node, lookup⟩ := survives
        rw [retired.lookup_none] at lookup
        contradiction
  exact State.taskFailure_root_coverage unique forest occurrence errors
    (covered task member key contributes earlier) survives

/-- Mixed ready draining cannot disconnect any surviving registered contributor. -/
theorem State.LiveContributorsCovered.drainReadyGroups {queue : State} {parents}
    (covered : queue.LiveContributorsCovered)
    (unique : queue.GroupRefsUnique) (forest : queue.RemovalForest parents)
    : queue.drainReadyGroups.1.LiveContributorsCovered := by
  intro task member key contributes survives
  rw [State.drainReadyGroups_tasks] at member
  obtain ⟨node, found⟩ := survives
  obtain ⟨old, earlier, _⟩ := (queue.drainReadyGroups_descendants unique).1 key node found
  exact State.drainReadyGroups_root_coverage unique forest key
    (covered task member key contributes ⟨old, earlier⟩) ⟨node, found⟩

/-- A fresh item covers its newly registered contributors while retaining all older paths. -/
theorem State.LiveContributorsCovered.integrateStreamItem
    {queue : State} {work : Execution.Work} {parents seen}
    (covered : queue.LiveContributorsCovered)
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (safe : queue.LiveParentsUncancelled) (fields : queue.GroupParentsCanonical parents)
    (records : queue.GroupNodesMatchWork work) (children : queue.ChildGroupsUnique)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items) (fresh : item.occurrence ∉ seen)
    : (queue.integrateStreamItem item).LiveContributorsCovered := by
  intro task member key contributes survives
  rw [State.integrateStreamItem_tasks] at member
  rcases List.mem_append.mp member with old | new
  · have priorLive : ∃ node, queue.groupNode? key = some node := by
      cases earlier : queue.groupNode? key with
      | some node => exact ⟨node, rfl⟩
      | none =>
          have retired := State.RetiredGroup.of_lookup_none (tasks task old key contributes) earlier
          have integrated := retired.maybeIntegrateWork item.work
          let candidates := (queue.maybeIntegrateWork item.work).2.newGroups
          have next := (integrated.pruneEmptyGroups candidates).startNewWork
            { (queue.maybeIntegrateWork item.work).2 with newGroups :=
              ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups candidates).2 }
          obtain ⟨node, lookup⟩ := survives
          have absent : (queue.integrateStreamItem item).groupNode? key = none := next.lookup_none
          rw [absent] at lookup
          contradiction
    exact State.integrateStreamItem_old_root_coverage unique registered item
      (covered task old key contributes priorLive)
  · obtain ⟨group, member, same⟩ := matching.streamItem_childTasksCovered itemMember task new key contributes
    have exactParents : ∀ candidate ∈ item.work.groups,
        candidate.parent = (parents candidate.node.ref).head? :=
      fun _ included => matching.streamItem_childGroups_parentCanonical canonical itemMember included
    have descriptors : ∀ candidate ∈ item.work.groups,
        ∃ dependencies, GroupRecordAt work candidate.node dependencies :=
      fun _ included => matching.streamItem_childGroups_recordAt itemMember included
    have forest := State.RemovalForest.of_generated generated
      (children.maybeIntegrateWork item.work) (links.maybeIntegrateWork item.work exactParents)
      (records.maybeIntegrateWork item.work descriptors) canonical
    exact same ▸ complete.fresh_live_item_root_coverage unique registered closed safe fields item
      exactParents (matching.streamItem_parentsCovered itemMember)
      (matching.streamItem_parentsBefore itemMember)
      (inventory.streamItem_groupsFresh generated matching itemMember fresh)
      forest member (same.symm ▸ survives)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
