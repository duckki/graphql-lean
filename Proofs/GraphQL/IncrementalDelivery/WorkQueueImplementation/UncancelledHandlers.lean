import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorRetirements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAvailability

/-! Cancellation-aware certificates at actual task and stream handler boundaries. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Successful task handling preserves ancestor markers under the supplied batch snapshot.
Witness: producer freshness derives child availability, registration reserves decrement
debt, and the same successful fold supplies markers and owners for cached startup/draining.
-/
theorem State.UncancelledRetiredMarkers.taskSuccess_certificates {queue : State}
    {work parents settled} (markers : queue.UncancelledRetiredMarkers work)
    (owners : queue.UncancelledTaskAccounting settled)
    (parent : ParentCutFrame queue work parents)
    (roots : RootReplayFrame queue work parents) (tasks : queue.TaskOwnerFrame work)
    (pending : queue.PendingAccounting work settled) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : occurrence ∉ settled)
    (rejections
      : queue.TaskRejectionsSatisfy (fun task _ => task ∉ occurrence :: settled))
    (available : List (Occurrence × Nat))
    (licensed : ∀ task errors, (task, errors) ∈ available → task ∉ occurrence :: settled)
    : (queue.taskSuccess occurrence result available).1.UncancelledRetiredMarkers work
      ∧ (queue.taskSuccess occurrence result available).1.NoticeAncestorRetirements work
          (queue.taskSuccess occurrence result available).2.1 := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskSuccess, found]
        using And.intro markers
          (State.NoticeAncestorRetirements.of_noNotices (queue := queue) (work := work)
            (events := []) (by intro event impossible; cases impossible))
  | some node =>
      have member := List.mem_of_find?_eq_some found
      have registered := pending.started node member
      have same := (State.taskNode?_some found).2
      let stored := queue.putTaskNode { node with value := some result.value }
      have storedParent : ParentCutFrame stored work parents :=
        ⟨parent.safe, parent.keys, parent.records, parent.links, parent.children, parent.live,
          parent.tasks, parent.closed, parent.fields, parent.complete, parent.cancelled,
          parent.registration.putTaskNode _ registered⟩
      have storedRoots : RootReplayFrame stored work parents :=
        ⟨⟨roots.live.refs, roots.live.records, roots.live.links, roots.live.registered,
          roots.live.tasks, roots.live.roots,
          ⟨roots.live.support.contents, roots.live.support.roots⟩, roots.live.present⟩,
          roots.retired⟩
      have childTasks : ∀ task ∈ result.work.tasks, TaskMatches work task := by
        intro task member
        obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
        exact ⟨⟨address, payload, some occurrence, same, known⟩,
          matching.childTask_groupsExact member⟩
      have known := fun group member => matching.taskChildGroups_recordAt (group := group) member
      have fields := fun group member =>
        matching.taskChildGroups_parentCanonical canonical (group := group) member
      have certificate := (pending.registration.children node.task registered).sourceChild same matching
      have descriptors : ∀ group ∈ result.work.groups, ∃ dependencies,
          GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head? := by
        intro group member
        obtain ⟨dependencies, record⟩ := known group member
        exact ⟨dependencies, record, by rw [canonical _ _ record]; exact fields group member⟩
      have childAvailable := (owners.putTaskNode {node with value := some result.value}).childGroupsPresent
        (queue := stored) roots.retired (markers.putTaskNode _) generated
        pending.matching storedParent.registration storedParent.closed canonical registered
        (same.symm ▸ fresh) (same.symm ▸ matching)
      have preparedParent := storedParent.maybeIntegrateWork result.work known fields
        certificate (some occurrence) generated canonical
      have preparedRoots := storedRoots.maybeIntegrateWork result.work known fields
        certificate.contributors (by
          intro task member group contributes
          exact (childTasks task member).contributorKnown (List.mem_map_of_mem contributes))
        (some occurrence) generated canonical certificate.parentRefs
      have preparedTasks := (tasks.putExistingTaskNode node member
        { node with value := some result.value } rfl).maybeIntegrateWork roots.live.present
          pending.taskGroups result.work childTasks (some occurrence)
      have preparedMarkers := (markers.putTaskNode
        { node with value := some result.value }).maybeIntegrateWork parent.closed canonical
          result.work (some occurrence) generated parent.live descriptors certificate.parentRefs
      have preparedOwners := ((owners.putTaskNode
        { node with value := some result.value }).maybeIntegrateWork_of_present storedParent.keys
          result.work (some occurrence) childAvailable).weakenSettled
          (after := occurrence :: settled) (by intro task member; simp [member])
      have preparedRejections := (rejections.putTaskNode
        { node with value := some result.value } (rejections node member)).maybeIntegrateWork
          result.work (some occurrence)
      let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := node.task.groups.foldl successGroupStep (integrated, [], {})
      have markerFold := preparedMarkers.successGroupFold preparedParent canonical node.task.groups
      have ownerFold := preparedOwners.successGroupFold preparedParent.keys node.task.groups
        (pending.matching.contributorsNodup generated registered)
        (pending.taskSuccess_integratedDebt occurrence result matching node found fresh)
      have retirement := successGroupFold_uncancelledRetirement preparedRoots.retired generated
        preparedParent.records preparedParent.links canonical preparedParent.live
        preparedParent.tasks preparedRoots.live.roots node.task.groups
      have foldedTasks := preparedTasks.successFold node.task.groups [] {}
      have foldedRejections := preparedRejections.successGroupFold node.task.groups
      have activated := markerFold.1.startNewWork retirement.2.2.2.2.2 ownerFold.1 generated
        markerFold.2.links markerFold.2.records foldedTasks.sound foldedTasks.matching canonical
        foldedRejections released.2.2 available licensed
      have closure : ClosureContext (released.1.startNewWork released.2.2 available).1 work
          parents (occurrence :: settled) :=
        ⟨activated, ownerFold.1.startNewWork released.2.2 available,
          markerFold.2.startNewWork generated canonical released.2.2 available,
          preparedRoots.successGroupFold_start generated canonical node.task.groups available,
          foldedTasks.startNewWork released.2.2 available,
          foldedRejections.startNewWork released.2.2 available licensed,
          ownerFold.2.1.startNewWork released.2.2 available⟩
      have foldNotices := State.successGroupFold_noticeAncestorRetirements preparedParent
        preparedMarkers preparedRoots generated canonical node.task.groups
      have continued := foldNotices.post (fun _ retired =>
        (retired.startNewWork released.2.2 available).drainReadyGroups available)
      have drained := closure.drainReadyGroups_noticeAncestorRetirements generated canonical
        (released.1.startNewWork released.2.2 available).1.groupNodes.length available licensed
      rw [queue.taskSuccess_eq occurrence result node found available]
      exact ⟨
        closure.markers.drainReadyGroups closure.owners closure.parent closure.roots
          closure.tasks closure.rejected closure.counts generated canonical available
          licensed,
        continued.append drained
      ⟩

/-- Successful task handling preserves ancestor markers under the supplied batch snapshot. -/
theorem State.UncancelledRetiredMarkers.taskSuccess {queue : State} {work parents settled}
    (markers : queue.UncancelledRetiredMarkers work)
    (owners : queue.UncancelledTaskAccounting settled)
    (parent : ParentCutFrame queue work parents)
    (roots : RootReplayFrame queue work parents) (tasks : queue.TaskOwnerFrame work)
    (pending : queue.PendingAccounting work settled) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : occurrence ∉ settled)
    (rejections
      : queue.TaskRejectionsSatisfy (fun task _ => task ∉ occurrence :: settled))
    (available : List (Occurrence × Nat))
    (licensed : ∀ task errors, (task, errors) ∈ available → task ∉ occurrence :: settled)
    : (queue.taskSuccess occurrence result available).1.UncancelledRetiredMarkers work :=
  (markers.taskSuccess_certificates owners parent roots tasks pending generated canonical
    occurrence result matching fresh rejections available licensed).1

/-- Rejected-task notification preserves uncancelled retired ancestor markers.
Witness: every visited contributor is licensed by the same fresh task descriptor. The
actual owner fold preserves permanent task registration while removal marks cancelled refs.
-/
theorem State.UncancelledRetiredMarkers.taskFailure {queue : State}
    {work parents settled}
    (markers : queue.UncancelledRetiredMarkers work)
    (owners : queue.UncancelledTaskAccounting settled)
    (structural : queue.UncancelledRetiredAncestors work)
    (links : queue.ChildLinksCanonical parents) (records : queue.GroupNodesMatchWork work)
    (started : queue.StartedTasksRegistered) (matching : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (errors : Nat) (fresh : occurrence ∉ settled)
    : (queue.taskFailure occurrence errors).1.UncancelledRetiredMarkers work := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using markers
  | some node =>
      have registered := started node (List.mem_of_find?_eq_some found)
      have known := matching node.task registered
      have taskFresh : node.task.occurrence ∉ settled := (State.taskNode?_some found).2.symm ▸ fresh
      let invariant (current : State) := current.UncancelledRetiredMarkers work
        ∧ current.UncancelledRetiredAncestors work ∧ current.UncancelledTaskAccounting settled
        ∧ current.ChildLinksCanonical parents ∧ current.GroupNodesMatchWork work
        ∧ node.task ∈ current.tasks
      have preserved := failureGroupFold_preserves_on invariant
        (GroupRecordInvalidated work [node.task.occurrence]) (by
          intro current ref frame invalid
          exact ⟨frame.1.removeGroup frame.2.1 frame.2.2.1 generated frame.2.2.2.1
              frame.2.2.2.2.1 canonical frame.2.2.2.2.2 known taskFresh ref invalid,
            frame.2.1.removeGroup ref, frame.2.2.1.removeGroup ref,
            frame.2.2.2.1.removeGroup ref, frame.2.2.2.2.1.removeGroup ref,
            frame.2.2.2.2.2⟩)
        errors node.task.groups (by
          intro group member
          obtain ⟨⟨_, payload, producer, _, taskKnown⟩, _⟩ := known
          exact .task ⟨producer, payload, taskKnown⟩ (List.mem_map_of_mem member)
            List.mem_cons_self)
        (queue.putTaskNode { node with rejection := some errors }, [])
        ⟨markers.putTaskNode _, structural, owners.putTaskNode _, links, records, registered⟩
      rw [queue.taskFailure_eq occurrence errors node found]
      exact preserved.1

/-- Fresh item registration preserves uncancelled owner links through actual startup.
Witness: the item's region has no registered contributor refs; registration installs
its task memberships before pruning and cached startup can remove an owner.
-/
theorem State.UncancelledTaskAccounting.integrateStreamItem {queue : State}
    {work settled seen stream items item}
    (owners : queue.UncancelledTaskAccounting settled) (unique : queue.GroupRefsUnique)
    (regions : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items) (fresh : item.occurrence ∉ seen)
    (live : queue.LiveGroupsRegistered)
    (available : List (Occurrence × Nat))
    : (queue.integrateStreamItem item available).UncancelledTaskAccounting settled := by
  have certificate := generated.declarations.sourceStreamItem matching member queue.registeredGroups
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have descriptors : ∀ group ∈ item.work.groups, ∃ dependencies,
      GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head? := by
    intro group included
    obtain ⟨dependencies, known⟩ := matching.streamItem_childGroups_recordAt member included
    exact ⟨dependencies, known,
      (matching.streamItem_childGroups_parentCanonical
        canonical member included).trans
          (congrArg List.head? (canonical _ _ known)).symm⟩
  have support := State.registrationSupported_of_fresh_candidates generated item.work.groups
    (regions.streamItem_groupsFresh generated matching member fresh) descriptors
    (fun group included parent head =>
      (matching.streamItem_parentsCovered generated.declarations member group included parent head
        ).resolve_left (by simp))
  have integrated := owners.maybeIntegrateWork_of_present unique item.work none (by
    intro task included ref contributes _
    obtain ⟨group, candidate, same⟩ :=
      matching.streamItem_childTasksCovered generated.declarations member task included ref contributes
    exact same ▸ queue.addGroups_supported_live (support group candidate) generated live
      item.work.groups descriptors certificate.parentRefs
      (List.mem_map_of_mem candidate))
  exact (integrated.pruneEmptyGroups (unique.maybeIntegrateWork item.work none) _
    ).startNewWork _ available

/-- Fresh stream-item preparation preserves ancestor markers before its source carrier.
Witness: group integration and empty-shell pruning preserve markers; their exact
registration records supply the retirement certificate needed by cached startup.
-/
theorem State.UncancelledRetiredMarkers.integrateStreamItem_certificates {queue : State}
    {work parents settled seen stream items item}
    (markers : queue.UncancelledRetiredMarkers work)
    (owners : queue.UncancelledTaskAccounting settled)
    (parent : ParentCutFrame queue work parents)
    (roots : RootReplayFrame queue work parents) (tasks : queue.TaskOwnerFrame work)
    (regions : queue.RegionInventory work seen)
    (rejections : queue.TaskRejectionsSatisfy (fun task _ => task ∉ settled))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items) (fresh : item.occurrence ∉ seen)
    (available : List (Occurrence × Nat))
    (licensed : ∀ task errors, (task, errors) ∈ available → task ∉ settled)
    : (queue.integrateStreamItem item available).UncancelledRetiredMarkers work
      ∧ ∀ values streams,
          (queue.integrateStreamItem item available).NoticeAncestorRetirements work
            [.streamValues stream values
              (((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
                  (queue.maybeIntegrateWork item.work).2.newGroups).2) streams] := by
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released : NewWork := { integrated.2 with newGroups := pruned.2 }
  have childTasks : ∀ task ∈ item.work.tasks, TaskMatches work task := by
    intro task included
    obtain ⟨address, payload, same, known⟩ := matching.streamItem_childTask_producer member included
    exact ⟨⟨address, payload, some item.occurrence, same, known⟩,
      matching.streamItem_childTask_groupsExact member included⟩
  have records := fun group candidate =>
    matching.streamItem_childGroups_recordAt member (group := group) candidate
  have fields := fun group candidate =>
    matching.streamItem_childGroups_parentCanonical canonical member (group := group) candidate
  have certificate := generated.declarations.sourceStreamItem matching member queue.registeredGroups
  have descriptors : ∀ group ∈ item.work.groups, ∃ dependencies,
      GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head? := by
    intro group included
    obtain ⟨dependencies, record⟩ := records group included
    exact ⟨dependencies, record, by rw [canonical _ _ record]; exact fields group included⟩
  have integratedParent := parent.maybeIntegrateWork item.work records fields
    certificate none generated canonical
  have integratedTasks := tasks.maybeIntegrateWork roots.live.present parent.tasks
    item.work childTasks
  have protectedRoots : ∀ child ∈ integrated.2.newGroups,
      integrated.1.AncestorsRetired work child.ref := by
    intro child included
    rw [State.maybeIntegrateWork_newGroups] at included
    obtain ⟨group, candidate, same, parentless, _⟩ :=
      queue.addGroups_newGroup_candidate item.work.groups included
    obtain ⟨dependencies, record⟩ := records group candidate
    have head := fields group candidate
    rw [parentless, ← canonical _ _ record] at head
    have empty : dependencies = [] := List.head?_eq_none_iff.mp head.symm
    rw [← same]
    exact .of_record generated record (by simp [empty])
  have retired := (roots.retired.maybeIntegrateWork item.work none generated parent.live
    descriptors certificate.parentRefs).pruneEmptyGroups generated
    integratedParent.records integratedParent.links canonical integratedParent.live
    integrated.2.newGroups protectedRoots
  have support := State.registrationSupported_of_fresh_candidates generated item.work.groups
    (regions.streamItem_groupsFresh generated matching member fresh) descriptors
    (fun group included ancestor head =>
      (matching.streamItem_parentsCovered generated.declarations member group included ancestor head
        ).resolve_left (by simp))
  have newOwners := owners.maybeIntegrateWork_of_present parent.keys item.work none (by
    intro task included ref contributes _
    obtain ⟨group, candidate, same⟩ :=
      matching.streamItem_childTasksCovered generated.declarations member task included ref contributes
    exact same ▸ queue.addGroups_supported_live (support group candidate) generated parent.live
      item.work.groups descriptors certificate.parentRefs (List.mem_map_of_mem candidate))
  have prunedOwners := newOwners.pruneEmptyGroups integratedParent.keys integrated.2.newGroups
  have prunedParent := integratedParent.pruneEmptyGroups integrated.2.newGroups
  have prunedTasks := integratedTasks.pruneEmptyGroups integrated.2.newGroups
  have prunedRejections := (rejections.maybeIntegrateWork item.work).pruneEmptyGroups
    integrated.2.newGroups
  have prunedMarkers := (markers.maybeIntegrateWork parent.closed canonical item.work none generated parent.live
    descriptors certificate.parentRefs).pruneEmptyGroups integratedParent.safe integratedParent.fields integratedParent.closed
      integratedParent.live canonical integrated.2.newGroups
  refine ⟨prunedMarkers.startNewWork retired prunedOwners generated prunedParent.links
    prunedParent.records prunedTasks.sound prunedTasks.matching canonical prunedRejections
    released available licensed, ?_⟩
  intro values streams
  have frontier := State.NoticeAncestorRetirements.of_frontier prunedParent prunedMarkers
    canonical (events := [.streamValues stream values pruned.2 streams])
    (by simp only [List.flatMap_singleton, rawGroupNoticeRefs]; rfl)
    (integrated.1.pruneEmptyGroups_ancestorsRetired generated integratedParent.records
      integratedParent.links canonical integratedParent.live integrated.2.newGroups protectedRoots)
    (fun child member => integrated.1.pruneEmptyGroups_keptPresent integrated.2.newGroups
      integratedParent.keys child.ref (List.mem_map_of_mem member))
  exact frontier.post (fun _ retired => retired.startNewWork released available)

/-- Fresh item integration preserves uncancelled ancestor markers. -/
theorem State.UncancelledRetiredMarkers.integrateStreamItem {queue : State}
    {work parents settled seen stream items item}
    (markers : queue.UncancelledRetiredMarkers work)
    (owners : queue.UncancelledTaskAccounting settled)
    (parent : ParentCutFrame queue work parents)
    (roots : RootReplayFrame queue work parents) (tasks : queue.TaskOwnerFrame work)
    (regions : queue.RegionInventory work seen)
    (rejections : queue.TaskRejectionsSatisfy (fun task _ => task ∉ settled))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items) (fresh : item.occurrence ∉ seen)
    (available : List (Occurrence × Nat))
    (licensed : ∀ task errors, (task, errors) ∈ available → task ∉ settled)
    : (queue.integrateStreamItem item available).UncancelledRetiredMarkers work :=
  (markers.integrateStreamItem_certificates owners parent roots tasks regions rejections
    generated canonical matching member fresh available licensed).1

private structure StreamContext (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (settled seen : List Occurrence)
    : Prop where
  markers : queue.UncancelledRetiredMarkers work
  owners : queue.UncancelledTaskAccounting settled
  parent : ParentCutFrame queue work parents
  roots : RootReplayFrame queue work parents
  tasks : queue.TaskOwnerFrame work
  regions : queue.RegionInventory work seen
  rejected : queue.TaskRejectionsSatisfy (fun task _ => task ∉ settled)
  counts : queue.PendingBound (fun _ => True) settled

/-- Item preparation retains its closure frame and exact accumulated notice ancestors. -/
theorem State.UncancelledRetiredMarkers.prepareItems_certificates {queue : State}
    {work parents settled seen stream items}
    (markers : queue.UncancelledRetiredMarkers work)
    (owners : queue.UncancelledTaskAccounting settled)
    (parent : ParentCutFrame queue work parents)
    (roots : RootReplayFrame queue work parents) (tasks : queue.TaskOwnerFrame work)
    (regions : queue.RegionInventory work seen)
    (rejections : queue.TaskRejectionsSatisfy (fun task _ => task ∉ settled))
    (counts : queue.PendingBound (fun _ => True) settled) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (unique : (items.map StreamItem.occurrence).Nodup)
    (fresh : ∀ item ∈ items, item.occurrence ∉ seen) (available : List (Occurrence × Nat))
    (licensed : ∀ task errors, (task, errors) ∈ available → task ∉ settled)
    : let prepared :=
        items.foldl (fun acc item => streamItemStep acc item available)
          (queue, [], [], [], [])
      ClosureContext prepared.1 work parents settled
      ∧ prepared.1.NoticeAncestorRetirements work
          [.streamValues stream prepared.2.2.2.1 prepared.2.1 prepared.2.2.1] := by
  have step (current : State) (seen : List Occurrence) (item : StreamItem)
      (member : item ∈ items) (frame : StreamContext current work parents settled seen)
      (fresh : item.occurrence ∉ seen)
      : StreamContext (current.integrateStreamItem item available) work parents settled
          (item.occurrence :: seen) := by
    have singleton : (GraphEvent.streamItems stream [item]).MatchesWork work := by
      intro next listed
      cases List.mem_singleton.mp listed
      exact matching item member
    have roots := frame.roots.live.prepareItems frame.roots.retired generated canonical singleton
      available
    have tasks := frame.tasks.prepareItems_of_registered frame.parent.live frame.parent.tasks
      frame.roots.live.present generated.declarations singleton available
    exact ⟨frame.markers.integrateStreamItem frame.owners frame.parent frame.roots frame.tasks
        frame.regions frame.rejected generated canonical matching member fresh available licensed,
      frame.owners.integrateStreamItem frame.parent.keys frame.regions generated matching
        member fresh frame.parent.live available,
      frame.parent.integrateStreamItem generated canonical matching member available,
      ⟨roots.1, roots.2⟩, tasks,
      frame.regions.integrateStreamItem matching member available,
      ((frame.rejected.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork
        _ available licensed,
      ((frame.counts.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available⟩
  have loop (more : List StreamItem) (included : more.Subset items)
      (unique : (more.map StreamItem.occurrence).Nodup)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List Execution.StreamItemValue × List GroupFailureEvent)
      (seen : List Occurrence) (frame : StreamContext acc.1 work parents settled seen)
      (notices : acc.1.NoticeAncestorRetirements work
        [.streamValues stream acc.2.2.2.1 acc.2.1 acc.2.2.1])
      (fresh : ∀ item ∈ more, item.occurrence ∉ seen)
      : ∃ finalSeen,
          let result := more.foldl (fun acc item => streamItemStep acc item available) acc
          StreamContext result.1 work parents settled finalSeen
          ∧ result.1.NoticeAncestorRetirements work
              [.streamValues stream result.2.2.2.1 result.2.1 result.2.2.1] := by
    induction more generalizing acc seen with
    | nil => exact ⟨seen, frame, notices⟩
    | cons item rest ih =>
        have unique := List.nodup_cons.mp unique
        let next := streamItemStep acc item available
        have receipt := frame.markers.integrateStreamItem_certificates frame.owners frame.parent
          frame.roots frame.tasks frame.regions frame.rejected generated canonical matching
          (included List.mem_cons_self) (fresh item List.mem_cons_self) available licensed
        have priorNotices : next.1.NoticeAncestorRetirements work
            [.streamValues stream acc.2.2.2.1 acc.2.1 acc.2.2.1] :=
          notices.post (fun _ retired =>
            ((retired.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available)
        have newNotices := receipt.2 [] []
        change next.1.NoticeAncestorRetirements work
          [.streamValues stream []
            (((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
              (acc.1.maybeIntegrateWork item.work).2.newGroups).2) []] at newNotices
        have nextNotices : next.1.NoticeAncestorRetirements work
            [.streamValues stream next.2.2.2.1 next.2.1 next.2.2.1] :=
          (priorNotices.append newNotices).of_noticeRefs (by
            intro ref member
            simpa only [next, streamItemStep, List.flatMap_singleton, rawGroupNoticeRefs,
              List.map_append, List.flatMap_append, List.mem_append] using member)
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member)) unique.2
          next (item.occurrence :: seen)
          (step acc.1 seen item (included List.mem_cons_self) frame
            (fresh item List.mem_cons_self))
          nextNotices
        intro next member recorded
        rcases List.mem_cons.mp recorded with same | earlier
        · exact unique.1 (same ▸ List.mem_map_of_mem member)
        · exact fresh next (List.mem_cons_of_mem _ member) earlier
  obtain ⟨_, prepared, preparedNotices⟩ := loop items (List.Subset.refl _) unique
    (queue, [], [], [], []) seen
    ⟨markers, owners, parent, roots, tasks, regions, rejections, counts⟩
    (State.NoticeAncestorRetirements.of_noNotices (by
      intro event member
      cases List.mem_singleton.mp member
      rfl)) fresh
  exact ⟨⟨prepared.markers, prepared.owners, prepared.parent, prepared.roots,
    prepared.tasks, prepared.rejected, prepared.counts⟩, preparedNotices⟩

/-- A fresh source receipt preserves uncancelled owners and ancestor markers.
The preparation certificate is transported through the final success-only drain. -/
theorem State.UncancelledRetiredMarkers.streamItems_certificates {queue : State}
    {work parents settled seen stream items}
    (markers : queue.UncancelledRetiredMarkers work)
    (owners : queue.UncancelledTaskAccounting settled)
    (parent : ParentCutFrame queue work parents)
    (roots : RootReplayFrame queue work parents) (tasks : queue.TaskOwnerFrame work)
    (regions : queue.RegionInventory work seen)
    (rejections : queue.TaskRejectionsSatisfy (fun task _ => task ∉ settled))
    (counts : queue.PendingBound (fun _ => True) settled) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (unique : (items.map StreamItem.occurrence).Nodup)
    (fresh : ∀ item ∈ items, item.occurrence ∉ seen) (available : List (Occurrence × Nat))
    (licensed : ∀ task errors, (task, errors) ∈ available → task ∉ settled)
    : (queue.streamItems stream items available).1.UncancelledRetiredMarkers work
      ∧ (queue.streamItems stream items available).1.UncancelledTaskAccounting settled
      ∧ (queue.streamItems stream items available).1.NoticeAncestorRetirements work
          (queue.streamItems stream items available).2.1 := by
  obtain ⟨prepared, preparedNotices⟩ := markers.prepareItems_certificates owners parent roots
    tasks regions rejections counts generated canonical matching unique fresh available licensed
  rw [queue.streamItems_eq stream items available]
  split
  · exact ⟨markers, owners, .of_noNotices (by intro event impossible; cases impossible)⟩
  · have drained := prepared.drainReadyGroups_noticeAncestorRetirements generated canonical
      (queue.preparedStreamItems items available).groupNodes.length available licensed
    exact ⟨prepared.markers.drainReadyGroups prepared.owners prepared.parent prepared.roots
      prepared.tasks prepared.rejected prepared.counts generated canonical available licensed,
      prepared.owners.drainReadyGroups prepared.parent.keys prepared.counts available,
      (preparedNotices.post (fun _ retired => retired.drainReadyGroups available)).append drained⟩

/-- Fresh stream receipts preserve uncancelled owners and ancestor markers. -/
theorem State.UncancelledRetiredMarkers.streamItems {queue : State}
    {work parents settled seen stream items}
    (markers : queue.UncancelledRetiredMarkers work)
    (owners : queue.UncancelledTaskAccounting settled)
    (parent : ParentCutFrame queue work parents)
    (roots : RootReplayFrame queue work parents) (tasks : queue.TaskOwnerFrame work)
    (regions : queue.RegionInventory work seen)
    (rejections : queue.TaskRejectionsSatisfy (fun task _ => task ∉ settled))
    (counts : queue.PendingBound (fun _ => True) settled) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (unique : (items.map StreamItem.occurrence).Nodup)
    (fresh : ∀ item ∈ items, item.occurrence ∉ seen) (available : List (Occurrence × Nat))
    (licensed : ∀ task errors, (task, errors) ∈ available → task ∉ settled)
    : (queue.streamItems stream items available).1.UncancelledRetiredMarkers work
      ∧ (queue.streamItems stream items available).1.UncancelledTaskAccounting
          settled := by
  have certificates := markers.streamItems_certificates owners parent roots tasks regions rejections
    counts generated canonical matching unique fresh available licensed
  exact ⟨certificates.1, certificates.2.1⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
