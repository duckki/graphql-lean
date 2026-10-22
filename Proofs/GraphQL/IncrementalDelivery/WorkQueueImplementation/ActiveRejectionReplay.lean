import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveFailureCaches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRemoval

/-! Consumed failures cannot retain an active live contributing owner. Cache availability
may include later notifications from the same host batch; consumed failures do not.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def RefUnfailed (work : Execution.Work) (failed : List Occurrence) (ref : NodeRef)
    : Prop :=
  ∀ occurrence ∈ failed, ∀ owners, TaskHasOwners work occurrence owners → ref ∉ owners

/-- No consumed failed task contributes directly to a live active group.
This is internal proof evidence over source notifications, independent of cache exposure.
-/
def State.ActiveFailuresAbsent (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  ∀ group ∈ queue.groupNodes,
    group.group.node.ref ∈ queue.rootGroups → RefUnfailed work failed group.group.node.ref

private theorem absent_of_sublist {before after : State} {ref}
    (groups : after.groupNodes.Sublist before.groupNodes)
    (absent : before.groupNode? ref = none)
    : after.groupNode? ref = none := by
  apply List.find?_eq_none.mpr
  intro group member
  exact List.find?_eq_none.mp absent group (groups.subset member)

private theorem State.RetainedFailures.startGroup_failed_absent {queue : State}
    {work failed} (retained : queue.RetainedFailures work failed) {ref occurrence owners}
    (recorded : occurrence ∈ failed) (known : TaskHasOwners work occurrence owners)
    (owner : ref ∈ owners) (available : List (Occurrence × Nat))
    : (queue.startGroup ref available).1.groupNode? ref = none := by
  let cached := queue.cacheTaskFailures available
  have prior := retained.cacheTaskFailures available
  cases found : cached.groupNode? ref with
  | none =>
      dsimp only [cached] at found
      simp only [State.startGroup, found]
  | some group =>
      have same := State.groupNode?_ref found
      obtain ⟨listed, task, lookup, rejected, _⟩ :=
        prior.retained occurrence recorded owners known
          group (List.mem_of_find?_eq_some found) (same ▸ owner)
      have nonempty
          : (group.tasks.filterMap
              (fun occurrence => (cached.taskNode? occurrence).bind (·.rejection))).isEmpty
            = false := by
        cases failure : task.rejection with
        | none => simp [failure] at rejected
        | some errors =>
            apply Bool.eq_false_iff.mpr
            intro empty
            have member : errors ∈ group.tasks.filterMap
                (fun occurrence => (cached.taskNode? occurrence).bind (·.rejection)) :=
              List.mem_filterMap.mpr ⟨occurrence, listed, by rw [lookup]; exact failure⟩
            rw [List.isEmpty_iff.mp empty] at member
            cases member
      dsimp only [cached] at found nonempty
      simp only [State.startGroup, found, nonempty, Bool.false_eq_true, ↓reduceIte]
      rw [← same]
      exact cached.removeGroup_ownGroupAbsent _

private theorem State.RetainedFailures.startNewWork_failed_absent {queue : State}
    {work failed} (retained : queue.RetainedFailures work failed) (released : NewWork)
    {ref occurrence owners} (recorded : occurrence ∈ failed)
    (known : TaskHasOwners work occurrence owners) (owner : ref ∈ owners)
    (selected : ref ∈ released.newGroups.map Execution.DeliveryNode.ref)
    (available : List (Occurrence × Nat))
    : (queue.startNewWork released available).1.groupNode? ref = none := by
  have fold (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (retained : acc.1.RetainedFailures work failed)
      (selected : ref ∈ refs ∨ acc.1.groupNode? ref = none)
      : (refs.foldl (fun (current, failures) next =>
          let (queue, queued) := current.startGroup next available
          (queue, failures ++ queued)) acc).1.groupNode? ref = none := by
    induction refs generalizing acc with
    | nil => exact selected.resolve_left (by simp)
    | cons next rest ih =>
        rw [List.foldl_cons]
        apply ih ((acc.1.startGroup next available).1,
          acc.2 ++ (acc.1.startGroup next available).2) (retained.startGroup next available)
        rcases selected with listed | absent
        · rcases List.mem_cons.mp listed with same | later
          · subst next
            exact .inr (retained.startGroup_failed_absent recorded known owner available)
          · exact .inl later
        · exact .inr (absent_of_sublist
            (acc.1.startGroup_groupNodes_sublist next available) absent)
  have streams (refs : NodeRefs) (current : State) (absent : current.groupNode? ref = none)
      : (refs.foldl State.startStream current).groupNode? ref = none := by
    induction refs generalizing current with
    | nil => exact absent
    | cons next rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact absent
  unfold State.startNewWork
  apply streams
  exact fold _ _ retained (.inl selected)

/-- Starting released groups excludes every consumed failed contributor from live roots.
Witness: retained rejections force each newly released failed group to be removed before
its tasks start. Earlier roots only shrink; stream activation leaves groups unchanged.
-/
theorem State.ActiveFailuresAbsent.startNewWork {queue : State} {work failed}
    (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.ActiveFailuresAbsent work failed := by
  intro group member active occurrence recorded owners known owner
  have old := (queue.startNewWork_groupNodes_sublist released available).subset member
  rcases List.mem_append.mp ((queue.startNewWork_rootGroups_sublist released available).subset
      active) with prior | fresh
  · exact clear group old prior occurrence recorded owners known owner
  · have absent := retained.startNewWork_failed_absent released recorded known owner fresh available
    have skipped := List.find?_eq_none.mp absent group member
    exact skipped (by simp)

private theorem State.ActiveFailuresAbsent.nodeProperty {queue : State} {work failed}
    (clear : queue.ActiveFailuresAbsent work failed)
    : ∀ group ∈ queue.groupNodes,
        group.group.node.ref ∈ queue.rootGroups
        → RefUnfailed work failed group.group.node.ref :=
  clear

/-- Successful flushing preserves direct exclusion of consumed failures.
Witness: surviving refs and root refs come from before the flush; only task memberships
are shortened, so the exclusion property is unaffected.
-/
theorem State.ActiveFailuresAbsent.finishGroupSuccess {queue : State} {work failed}
    (clear : queue.ActiveFailuresAbsent work failed) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.ActiveFailuresAbsent work failed := by
  have surviving := State.finishGroupSuccess_nodeProperty
    (fun node => node.group.node.ref ∈ queue.rootGroups
      → RefUnfailed work failed node.group.node.ref)
    (fun _ _ prior => prior) clear.nodeProperty group
  intro node member active
  exact surviving node member (queue.finishGroupSuccess_rootsSubset group active)

private def RefsSatisfy (queue : State) (property : NodeRef → Prop) : Prop :=
  ∀ group ∈ queue.groupNodes, property group.group.node.ref

private theorem RefsSatisfy.putGroupNode {queue : State} {property}
    (prior : RefsSatisfy queue property) (updated : GroupNode)
    (valid : property updated.group.node.ref)
    : RefsSatisfy (queue.putGroupNode updated) property := by
  intro group member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst group; exact valid
  · subst group; exact prior old oldMember

private theorem RefsSatisfy.appendFresh {queue : State} {property}
    (prior : RefsSatisfy queue property) (group : Group) (registered : NodeRefs)
    (valid : property group.node.ref)
    : RefsSatisfy
        ({
              queue with
                registeredGroups := registered
                groupNodes := queue.groupNodes ++ [{ group }]
            }
          : State) property := by
  intro node member
  rcases List.mem_append.mp member with old | fresh
  · exact prior node old
  · obtain rfl := List.mem_singleton.mp fresh
    exact valid

private theorem RefsSatisfy.addGroup {queue : State} {property}
    (prior : RefsSatisfy queue property)
    (fresh : ∀ ref, ref ∉ queue.registeredGroups → property ref) (group : Group)
    : RefsSatisfy (queue.addGroup group) property := by
  unfold State.addGroup
  split
  · exact prior
  · rename_i unregistered
    have absent : group.node.ref ∉ queue.registeredGroups := by
      simp only [Bool.or_eq_true, List.contains_iff_mem, not_or] at unregistered
      exact unregistered.1
    split
    · exact prior.appendFresh group _ (fresh _ absent)
    · split
      · split <;> exact prior
      · rename_i node found
        apply (prior.appendFresh group _ (fresh _ absent)).putGroupNode _
        exact prior node (List.mem_of_find?_eq_some found)

private theorem RefsSatisfy.addGroups {queue : State} {property}
    (prior : RefsSatisfy queue property)
    (fresh : ∀ ref, ref ∉ queue.registeredGroups → property ref) (groups : List Group)
    : RefsSatisfy (queue.addGroups groups).1 property := by
  let invariant := fun current : State => RefsSatisfy current property
    ∧ ∀ ref, ref ∉ current.registeredGroups → property ref
  exact (State.addGroups_preserves invariant groups
    (fun current group _ valid =>
      ⟨valid.1.addGroup valid.2 group,
        fun ref absent => valid.2 ref (fun old => absent
          (current.addGroup_registeredGroups_subset_old group old))⟩)
    queue ⟨prior, fresh⟩).1

private theorem RefsSatisfy.addTask {queue : State} {property}
    (prior : RefsSatisfy queue property) (task : Task)
    : RefsSatisfy (queue.addTask task) property := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have fold (groups : List Execution.DeliveryNode) (current : State)
      (prior : RefsSatisfy current property)
      : RefsSatisfy (groups.foldl step current) property := by
    induction groups generalizing current with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        unfold step
        split
        · exact prior
        · rename_i node found
          split
          · exact prior
          · exact prior.putGroupNode _ (prior node (List.mem_of_find?_eq_some found))
  dsimp only [State.addTask]
  split <;> exact fold task.groups _ prior

private theorem RefsSatisfy.addStreams {queue : State} {property}
    (prior : RefsSatisfy queue property) (streams : List Stream)
    (producer : Option Occurrence)
    : RefsSatisfy (queue.addStreams streams producer).1 property := by
  unfold State.addStreams
  dsimp only
  split
  · exact prior
  · split <;> exact prior

/-- Registering child work cannot add an earlier failed contributor to an active ref.
Witness: existing refs retain their exclusion; fresh registered refs have no earlier
failed owner by retained-failure freshness. Task and stream registration preserve refs.
-/
theorem State.ActiveFailuresAbsent.maybeIntegrateWork {queue : State} {work failed}
    (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed) (more : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork more producer).1.ActiveFailuresAbsent work failed := by
  let property := fun ref => ref ∈ queue.rootGroups → RefUnfailed work failed ref
  have initial : RefsSatisfy queue property := clear
  have grouped := initial.addGroups
    (fun ref absent _ => retained.fresh ref absent) more.groups
  have fold (tasks : List Task) (current : State) (prior : RefsSatisfy current property)
      : RefsSatisfy (tasks.foldl State.addTask current) property := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (prior.addTask task)
  have final := (fold more.tasks _ grouped).addStreams more.streams producer
  intro group member active
  exact final group member (by rwa [State.maybeIntegrateWork_rootGroups] at active)

/-- Pruning empty shells preserves exclusion of consumed failed contributors. -/
theorem State.ActiveFailuresAbsent.pruneEmptyGroups {queue : State} {work failed}
    (clear : queue.ActiveFailuresAbsent work failed)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.ActiveFailuresAbsent work failed := by
  intro group member active
  exact clear group ((queue.pruneEmptyGroups_groupNodes_sublist groups).subset member)
    (by rwa [State.pruneEmptyGroups_rootGroups] at active)

/-- Cache exposure changes no active ref or live group descriptor. -/
theorem State.ActiveFailuresAbsent.cacheTaskFailures {queue : State} {work failed}
    (clear : queue.ActiveFailuresAbsent work failed) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).ActiveFailuresAbsent work failed := by
  intro group member active
  rw [State.cacheTaskFailures_groupNodes] at member
  rw [State.cacheTaskFailures_rootGroups] at active
  exact clear group member active

private theorem State.ActiveFailuresAbsent.decrement {queue : State} {work failed}
    (clear : queue.ActiveFailuresAbsent work failed) {node : GroupNode}
    (member : node ∈ queue.groupNodes)
    : (queue.putGroupNode { node with pending := node.pending - 1 }).ActiveFailuresAbsent
        work failed :=
  (show RefsSatisfy queue
          (fun ref => ref ∈ queue.rootGroups → RefUnfailed work failed ref) from clear).putGroupNode
    _ (clear node member)

/-- A notified rejection removes every live active direct owner of that task.
Witness: exact task provenance identifies the handler's owner list; the owner fold makes
every surviving contributor dormant. Previously excluded failed contributors stay excluded.
-/
theorem State.ActiveFailuresAbsent.taskFailure {queue : State} {work failed}
    (clear : queue.ActiveFailuresAbsent work failed)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) {occurrence errors}
    (accepted : queue.acceptsGraphEvent (.taskFailure occurrence errors) = true)
    : (queue.taskFailure occurrence errors).1.ActiveFailuresAbsent work
        (occurrence :: failed) := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.acceptsGraphEvent, found] at accepted
  | some task =>
      have member := (State.taskNode?_some found).1
      have identity := (State.taskNode?_some found).2
      obtain ⟨⟨_, _, _, _, knownTask⟩, _⟩ := matching task.task (registered task member)
      rw [identity] at knownTask
      intro group member active other recorded owners known owner
      rcases List.mem_cons.mp recorded with same | old
      · subst other
        obtain ⟨producer, payload, actual⟩ := known
        have sameOwners := (actual.unique knownTask).1
        exact queue.taskFailure_ownerLiveRootsAbsent found group.group.node.ref
          (sameOwners ▸ owner) group member rfl active
      · exact clear group ((queue.taskFailure_groupNodes_sublist occurrence errors).subset member)
          (queue.taskFailure_rootsSubset occurrence errors active) other old owners known owner

/-- A bounded successful drain preserves exclusion of all consumed failures.
Witness: every flushed membership is a successful settlement, so retained failures survive
at remaining owners; startup then removes released failed groups before they become live.
-/
theorem State.ActiveFailuresAbsent.drainReadyGroups {queue : State} {work failed settled}
    (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (safe : ∀ task ∈ settled, task ∉ failed)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.ActiveFailuresAbsent work failed := by
  let invariant := fun current : State => current.ActiveFailuresAbsent work failed
    ∧ current.RetainedFailures work failed ∧ current.PendingBound (fun _ => True) settled
  have final := State.drainReadyGroups_preserves invariant (available := available)
    (fun current node prior member _ zero => by
      have all := prior.2.2.allSettled member trivial zero
      have kept := prior.2.1.finishGroupSuccess node
        (fun task listed => safe task (all task listed))
      exact ⟨(prior.1.finishGroupSuccess node).startNewWork kept _ available,
        kept.startNewWork _ available,
        (prior.2.2.finishGroupSuccess node all).startNewWork _ available⟩)
    (show invariant queue from ⟨clear, retained, bounded⟩)
  exact final.1

/-- Successful settlement preserves consumed-failure exclusion through each release phase.
Witness: success-only counter debt prevents flushing failed memberships. Retention and
exclusion are transported together through the contributor fold, startup and final drain.
-/
theorem State.ActiveFailuresAbsent.taskSuccess {queue : State} {work failed settled}
    (clear : queue.ActiveFailuresAbsent work failed)
    (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work settled) (occurrence : Occurrence)
    (result : TaskResult) (taskNode : TaskNode)
    (found : queue.taskNode? occurrence = some taskNode) (fresh : occurrence ∉ settled)
    (notFailed : occurrence ∉ failed) (disjoint : ∀ task ∈ settled, task ∉ failed)
    (uniqueOwners : (taskNode.task.groups.map Execution.DeliveryNode.ref).Nodup)
    (childrenMatch : ∀ task ∈ result.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.ActiveFailuresAbsent work
        failed := by
  rw [queue.taskSuccess_eq occurrence result taskNode found available]
  let stored := queue.putTaskNode { taskNode with value := some result.value }
  let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
  have storedRefs : stored.GroupRefsUnique := ledger.refs
  have storedMembers : stored.TaskMembershipsUnique := ledger.memberships
  have storedCounts : stored.PendingBound (fun _ => True) settled := ledger.pending
  have storedCovered : stored.TaskGroupsRegistered := ledger.taskGroups
  have storedSound : stored.GroupMembershipSound := ledger.sound
  have storedMatch : stored.RegisteredTasksMatch work := ledger.matching
  have integratedLinks : integrated.UnsettledTaskLinks settled :=
    (ledger.links.putTaskNode _).maybeIntegrateWork storedRefs storedCovered result.work
      (some occurrence)
  have integratedCounts : integrated.PendingBound (fun _ => True) settled :=
    storedCounts.maybeIntegrateWork result.work (some occurrence)
  have integratedRefs := storedRefs.maybeIntegrateWork result.work (some occurrence)
  have integratedMembers := storedMembers.maybeIntegrateWork result.work (some occurrence)
  have integratedSound := storedSound.maybeIntegrateWork result.work (some occurrence)
  have integratedMatch := storedMatch.maybeIntegrateWork result.work childrenMatch
    (some occurrence)
  have taskMember : taskNode.task ∈ integrated.tasks := by
    rw [State.maybeIntegrateWork_tasks_append]
    exact List.mem_append_left _ (ledger.started taskNode (List.mem_of_find?_eq_some found))
  have same := (State.taskNode?_some found).2
  have owned := integratedLinks.ownedExactlyBy integratedSound integratedMatch taskMember
    (same.symm ▸ fresh)
  rw [same] at owned
  have debt : integrated.PendingDebtBound (fun _ => True) (occurrence :: settled)
      (taskNode.task.groups.map Execution.DeliveryNode.ref) :=
    integratedCounts.beginSettlement integratedMembers
      (fun node member _ => owned node member) fresh
  have storedRetained : stored.RetainedFailures work failed :=
    prior.putTaskNode found _ rfl (fun rejected => rejected)
  have integratedRetained := storedRetained.maybeIntegrateWork ledger.refs result.work
    (some occurrence)
  have integratedClear : integrated.ActiveFailuresAbsent work failed :=
    (show stored.ActiveFailuresAbsent work failed from clear).maybeIntegrateWork
      storedRetained result.work (some occurrence)
  let invariant (current : State) := current.GroupRefsUnique
    ∧ current.RetainedFailures work failed ∧ current.ActiveFailuresAbsent work failed
  have initial : invariant integrated := ⟨integratedRefs, integratedRetained, integratedClear⟩
  have safe : ∀ task ∈ occurrence :: settled, task ∉ failed := by
    intro task member
    rcases List.mem_cons.mp member with rfl | earlier
    · exact notFailed
    · exact disjoint task earlier
  have loop := successGroupFold_preservesBound (fun _ => True) (occurrence :: settled)
    invariant (fun _ valid => valid.1) (by intros; trivial)
    (fun _ node valid selected =>
      ⟨valid.1.putGroupNode _, valid.2.1.putGroupNodeSameTasks valid.1 node
        (List.mem_of_find?_eq_some selected) _ rfl rfl,
        valid.2.2.decrement (List.mem_of_find?_eq_some selected)⟩)
    (fun _ node _ valid _ _ _ _ all =>
      ⟨valid.1.finishGroupSuccess node,
        valid.2.1.finishGroupSuccess node (fun task member => safe task (all task member)),
        valid.2.2.finishGroupSuccess node⟩)
    taskNode.task.groups uniqueOwners (integrated, [], {}) initial debt
  let released := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
  have activated := loop.1.2.2.startNewWork loop.1.2.1 released.2.2 available
  exact activated.drainReadyGroups (loop.1.2.1.startNewWork _ available)
    (loop.2.startNewWork _ available) safe available

/-- One item integration preserves direct consumed-failure exclusion at activated roots. -/
theorem State.ActiveFailuresAbsent.integrateStreamItem {queue : State} {work failed}
    (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed) (refs : queue.GroupRefsUnique)
    (item : StreamItem) (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).ActiveFailuresAbsent work failed := by
  unfold State.integrateStreamItem
  exact ((clear.maybeIntegrateWork retained item.work).pruneEmptyGroups _).startNewWork
    ((retained.maybeIntegrateWork refs item.work).pruneEmptyGroups _) _ available

/-- Item batches preserve consumed-failure exclusion through their final successful drain.
Witness: the fixed failure inventory and retention are maintained across item startup;
counter bounds keep every flushed task disjoint from the consumed failures.
-/
theorem State.ActiveFailuresAbsent.streamItems {queue : State} {work failed settled}
    (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed) (refs : queue.GroupRefsUnique)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (disjoint : ∀ task ∈ settled, task ∉ failed) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.ActiveFailuresAbsent work failed := by
  let invariant := fun current : State => current.ActiveFailuresAbsent work failed
    ∧ current.RetainedFailures work failed ∧ current.GroupRefsUnique
    ∧ current.PendingBound (fun _ => True) settled
  have preserve (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List Execution.StreamItemValue × List GroupFailureEvent) (item : StreamItem)
      (prior : invariant acc.1) : invariant (streamItemStep acc item available).1 := by
    exact ⟨prior.1.integrateStreamItem prior.2.1 prior.2.2.1 item available,
      prior.2.1.integrateStreamItem prior.2.2.1 item available,
      ((prior.2.2.1.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _ available,
      ((prior.2.2.2.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available⟩
  have fold (more : List StreamItem)
      (acc
        : State
          × List Execution.DeliveryNode
          × List Execution.DeliveryNode
          × List Execution.StreamItemValue
          × List GroupFailureEvent)
      (prior : invariant acc.1)
      : invariant
          (more.foldl (fun acc item => streamItemStep acc item available) acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih => exact ih _ (preserve acc item prior)
  rw [queue.streamItems_eq stream items available]
  split
  · exact clear
  · have final := fold items (queue, [], [], [], []) ⟨clear, retained, refs, bounded⟩
    exact final.1.drainReadyGroups final.2.1 final.2.2.2 disjoint available

/-- A disposition-tracked FIFO handler excludes consumed failures from live active owners.
Witness: cached outcomes preserve the old exclusion; notifications remove direct owners,
while success/item handlers preserve retention and successful-settlement counter bounds.
-/
theorem State.ActiveFailuresAbsent.handleGraphEvent_ofDisposition {queue : State}
    {work before failed} (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before)) (event : GraphEvent)
    (source : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat) := [])
    (evidence
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    : (queue.handleGraphEvent event available).1.ActiveFailuresAbsent work
        (event.groupFailures ++ failed) := by
  let current := queue.cacheTaskFailures available
  have cached := clear.cacheTaskFailures available
  have kept := retained.cacheTaskFailures available
  have counted := ledger.cacheTaskFailures available
  have disjoint : ∀ task ∈ GraphEvent.groupSettlements before, task ∉ failed := by
    intro task member recorded
    exact valid.succeeds_not_failureSettlements (valid.groupSettlements_succeed member)
      (included recorded)
  cases event with
  | taskSuccess occurrence result =>
      cases found : current.taskNode? occurrence with
      | none =>
          change (current.taskSuccess occurrence result available).1.ActiveFailuresAbsent
            work failed
          simpa only [State.taskSuccess, found] using cached
      | some node =>
          apply cached.taskSuccess kept counted occurrence result node found
            (available := available)
          · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
              (GraphEvent.groupSettlements_subsetIdentities before member)
          · exact fun member => valid.succeeds_not_failureSettlements
              (source.successes_succeed (by simp [GraphEvent.successes])) (included member)
          · exact disjoint
          · exact counted.matching.contributorsNodup generated
              (counted.started node (List.mem_of_find?_eq_some found))
          · intro task member
            obtain ⟨address, payload, same, known⟩ := source.childTask_producer member
            exact ⟨⟨address, payload, some occurrence, same, known⟩,
              source.childTask_groupsExact member⟩
  | taskFailure occurrence errors =>
      cases found : current.taskNode? occurrence with
      | some node =>
          exact cached.taskFailure counted.started counted.matching
            (by
              change (current.taskNode? occurrence).isSome = true
              rw [found]
              rfl)
      | none =>
          change (current.taskFailure occurrence errors).1.ActiveFailuresAbsent work
            (occurrence :: failed)
          simp only [State.taskFailure, found]
          have absent :=
            ((evidence occurrence errors rfl).1.cacheTaskFailures available).absent found
          obtain ⟨task, registered, identity⟩ := (evidence occurrence errors rfl).2
          have member : task ∈ current.tasks := by
            simpa only [current, State.cacheTaskFailures_tasks] using registered
          obtain ⟨_, _, _, _, descriptor⟩ := (counted.matching task member).1
          rw [identity] at descriptor
          have pending : task.occurrence ∉ GraphEvent.groupSettlements before := by
            rw [identity]
            exact fun prior => fresh.2.2.1 occurrence List.mem_cons_self
              (GraphEvent.groupSettlements_subsetIdentities before prior)
          intro group live active other recorded owners known contributes
          rcases List.mem_cons.mp recorded with same | old
          · subst other
            obtain ⟨producer, payload, otherKnown⟩ := known
            have sameOwners := (descriptor.unique otherKnown).1
            have linked := counted.links task member pending group live
              (sameOwners.symm ▸ contributes)
            exact absent group live (identity ▸ linked)
          · exact cached group live active other old owners known contributes
  | streamItems stream items =>
      exact cached.streamItems kept counted.refs counted.pending disjoint stream items available
  | streamSuccess stream =>
      change (current.streamSuccess stream).1.ActiveFailuresAbsent work failed
      unfold State.streamSuccess
      split <;> exact cached
  | streamFailure stream errors =>
      change (current.streamFailure stream errors).1.ActiveFailuresAbsent work failed
      unfold State.streamFailure
      split <;> exact cached
  | groupFailure notice =>
      change (current.groupFailure notice).1.ActiveFailuresAbsent work failed
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached

/-- Dispatch enqueues notices without changing the live owner exclusion property. -/
theorem State.ActiveFailuresAbsent.dispatchGraphEvent_ofDisposition {queue : State}
    {work before failed} (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before)) (event : GraphEvent)
    (source : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat) := [])
    (evidence
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    : (queue.dispatchGraphEvent event available).1.ActiveFailuresAbsent work
        (event.groupFailures ++ failed) :=
  clear.handleGraphEvent_ofDisposition retained ledger generated valid included event
    source fresh available evidence

/-- A currently live callback specializes disposition-tracked failure exclusion. -/
theorem State.ActiveFailuresAbsent.handleGraphEvent {queue : State} {work before failed}
    (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (event : GraphEvent) (source : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.ActiveFailuresAbsent work
        (event.groupFailures ++ failed) := by
  apply clear.handleGraphEvent_ofDisposition retained ledger generated valid included
    event source fresh available
  intro occurrence errors same
  subst event
  cases found : queue.taskNode? occurrence with
  | none => simp [State.acceptsGraphEvent, found] at accepted
  | some node =>
      exact ⟨.inl ⟨node, found⟩, node.task,
        ledger.started node (List.mem_of_find?_eq_some found), (State.taskNode?_some found).2⟩

/-- FIFO replay uses its actual fixed cache snapshot and advances consumed failures only.
Witness: joint source-prefix induction supplies retention and success-only counter ledgers
at each step, independently of output admission or healthy-owner assumptions.
-/
theorem State.ActiveFailuresAbsent.replayGraphEvents {queue : State}
    {work before failed available} (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (accepted : State.eventsStarted available queue events = true)
    : (queue.replayGraphEvents events available).ActiveFailuresAbsent work
        (GraphEvent.failureSettlements events ++ failed) := by
  induction events generalizing queue before failed with
  | nil => simpa [State.replayGraphEvents, GraphEvent.failureSettlements] using clear
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      obtain ⟨validBefore, source, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest
            = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have next := clear.handleGraphEvent retained ledger generated validBefore included event
        source fresh accepts.1 available
      have nextRetained := retained.dispatchGraphEvent ledger generated validBefore included event
        source fresh accepts.1 available
      have nextLedger := ledger.dispatchGraphEvent_successes_ofMatching generated
        (GraphEvent.groupSettlements_subsetIdentities before) event source fresh available
      rw [← GraphEvent.groupSettlements_append] at nextLedger
      have nextIncluded : (event.groupFailures ++ failed).Subset
          (GraphEvent.failureSettlements (before ++ [event])) := by
        rw [GraphEvent.failureSettlements_append]
        intro task member
        rcases List.mem_append.mp member with member | member
        · exact List.mem_append_left _ member
        · exact List.mem_append_right _ (included member)
      have dispatched : (queue.dispatchGraphEvent event available).1.ActiveFailuresAbsent work
          (event.groupFailures ++ failed) := next
      have result := ih dispatched nextRetained nextLedger nextIncluded
        (by simpa [List.append_assoc] using valid) accepts.2
      simpa only [State.replayGraphEvents, GraphEvent.failureSettlements_cons,
        List.append_assoc, List.foldl_cons]
        using result

/-- Public batch admission retains entry eligibility while consumed failures advance. -/
theorem State.ActiveFailuresAbsent.replayGraphEvents_admitted {queue : State}
    {work before failed available} (clear : queue.ActiveFailuresAbsent work failed)
    (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (generated : ExecutedWork work)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (accepted : State.acceptsBatch.go (fun _ => false) available queue events = true)
    : (queue.replayGraphEvents events available).ActiveFailuresAbsent work
        (GraphEvent.failureSettlements events ++ failed) := by
  have includedAt (fifo : List GraphEvent) :
      (GraphEvent.failureSettlements fifo ++ failed).Subset
        (GraphEvent.failureSettlements (before ++ fifo)) := by
    rw [GraphEvent.failureSettlements_append_list]
    intro occurrence member
    rcases List.mem_append.mp member with recent | old
    · exact List.mem_append_left _ recent
    · exact List.mem_append_right _ (included old)
  have result : (queue.replayGraphEvents events available).ActiveFailuresAbsent work
        (GraphEvent.failureSettlements events ++ failed)
      ∧ (queue.replayGraphEvents events available).RetainedFailures work
        (GraphEvent.failureSettlements events ++ failed)
      ∧ (queue.replayGraphEvents events available).PendingAccounting work
        (GraphEvent.groupSettlements (before ++ events)) := by
    apply prefix_invariant events (fun fifo =>
      (queue.replayGraphEvents fifo available).ActiveFailuresAbsent work
          (GraphEvent.failureSettlements fifo ++ failed)
        ∧ (queue.replayGraphEvents fifo available).RetainedFailures work
          (GraphEvent.failureSettlements fifo ++ failed)
        ∧ (queue.replayGraphEvents fifo available).PendingAccounting work
          (GraphEvent.groupSettlements (before ++ fifo)))
    · simpa only [State.replayGraphEvents, List.foldl_nil, GraphEvent.failureSettlements,
        List.flatMap_nil, List.reverse_nil, List.nil_append, List.append_nil] using And.intro clear (And.intro prior ledger)
    · intro fifo event rest split past
      have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
        ⟨rest, by simp [split, List.append_assoc]⟩
      obtain ⟨validBefore, matching, fresh⟩ := validGraphEvents_last (valid.prefix boundary)
      obtain ⟨clear, retained, counted⟩ := past fifo (List.prefix_refl _)
      have evidence : ∀ occurrence errors, event = .taskFailure occurrence errors
          → (queue.replayGraphEvents fifo available).StartedTaskDisposition occurrence
            ∧ ∃ task ∈ (queue.replayGraphEvents fifo available).tasks,
                task.occurrence = occurrence := by
        intro occurrence errors same
        subst event
        obtain ⟨seen, seenPrefix, eligible⟩ := queue.acceptsBatch_go_eachAccepted events fifo
          (.taskFailure occurrence errors) available accepted ⟨rest, by simp [split]⟩
        have frame := (past seen seenPrefix).2.2
        cases found : (queue.replayGraphEvents seen available).taskNode? occurrence with
        | none =>
            simp only [State.acceptsGraphEvent, found, Option.isSome_none, Bool.false_eq_true]
              at eligible
        | some node =>
            obtain ⟨remaining, history⟩ := seenPrefix
            have validSeen : ValidGraphEvents work (before ++ seen) :=
              validBefore.prefix ⟨remaining, by simp [history, List.append_assoc]⟩
            have source := queue.replayGraphEvents_producerOrder ready ordered seen validSeen available
            have disposition := frame.startedTaskDisposition_atPrefix found source.1 source.2
              remaining (by simpa [history, List.append_assoc] using validBefore) available
            rw [← history, State.replayGraphEvents_append queue seen remaining available]
            exact ⟨
              disposition,
              node.task,
              (queue.replayGraphEvents seen available).replayGraphEvents_tasks_subset
                remaining available
                (frame.started node (List.mem_of_find?_eq_some found)),
              (State.taskNode?_some found).2
            ⟩
      have nextClear := clear.dispatchGraphEvent_ofDisposition retained counted generated validBefore
        (includedAt fifo) event matching fresh available evidence
      have next := retained.dispatchGraphEvent_ofDisposition counted generated validBefore
        (includedAt fifo) event matching fresh available evidence
      have nextLedger := counted.dispatchGraphEvent_successes_ofMatching generated
        (GraphEvent.groupSettlements_subsetIdentities (before ++ fifo)) event matching fresh available
      rw [← GraphEvent.groupSettlements_append] at nextLedger
      refine ⟨?_, ?_, ?_⟩
      · simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
          List.foldl_append, List.foldl_cons, List.foldl_nil,
          GraphEvent.failureSettlements_append, List.append_assoc] using nextClear
      · simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
          List.foldl_append, List.foldl_cons, List.foldl_nil,
          GraphEvent.failureSettlements_append, List.append_assoc] using next
      · simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
          List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc] using nextLedger
  exact result.1

private theorem State.ActiveFailuresAbsent.handleGraphEvents {queue : State}
    {work before failed} (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (generated : ExecutedWork work)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).1.ActiveFailuresAbsent work
        (GraphEvent.failureSettlements events ++ failed) := by
  have replayed := clear.replayGraphEvents_admitted retained ledger ready ordered generated
    included events valid accepted
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact replayed

/-- Actual host batches exclude every consumed failed contributor from live active owners.
Witness: each batch uses its own availability snapshot; the consumed source prefix supplies
retention and counter accounting for the following batch. Terminal flags change no groups.
-/
theorem State.ActiveFailuresAbsent.runNormalized {queue : State} {work before failed}
    (clear : queue.ActiveFailuresAbsent work failed)
    (retained : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (generated : ExecutedWork work)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.runNormalized batches).1.ActiveFailuresAbsent work
        (GraphEvent.failureSettlements batches.flatten ++ failed) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before failed with
  | nil => simpa [State.replayBatches, GraphEvent.failureSettlements] using clear
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := clear.handleGraphEvents retained ledger ready ordered generated included batch
        (valid.prefix earlier) running accepted
      have nextRetained := retained.handleGraphEvents ledger ready ordered generated included batch
        (valid.prefix earlier) running accepted
      have producerStep := State.handleGraphEvents_producerOrder ready ordered batch
        (valid.prefix earlier) running
      have nextLedger := ledger.handleGraphEvents_successes generated batch (valid.prefix earlier)
        running accepted
      have nextIncluded : (GraphEvent.failureSettlements batch ++ failed).Subset
          (GraphEvent.failureSettlements (before ++ batch)) := by
        rw [GraphEvent.failureSettlements_append_list]
        intro task member
        rcases List.mem_append.mp member with member | member
        · exact List.mem_append_left _ member
        · exact List.mem_append_right _ (included member)
      have result := ih next nextRetained nextLedger producerStep.1 producerStep.2 nextIncluded
        (by simpa [List.append_assoc] using valid) restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        GraphEvent.failureSettlements_append_list, List.append_assoc]
        using result

/-- Consumed-failure exclusion and exact rejection provenance clear every active task cache.
Witness: sound membership identifies a contributing owner of each listed rejected task,
contradicting its exclusion from that live active group.
-/
theorem State.ActiveFailuresAbsent.noActiveCachedFailure {queue : State} {work failed}
    (clear : queue.ActiveFailuresAbsent work failed) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (rejections : queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ failed))
    : queue.NoActiveCachedFailure := by
  intro group member active
  apply State.rejectedTask?_eq_none_iff.mpr
  intro occurrence listed node found
  cases rejected : node.rejection with
  | none => rfl
  | some errors =>
      have recorded := rejections node (List.mem_of_find?_eq_some found) errors rejected
      obtain ⟨task, registered, identity, owner⟩ := sound group member occurrence listed
      obtain ⟨⟨_, payload, producer, _, known⟩, _⟩ := matching task registered
      rw [identity, ← (State.taskNode?_some found).2] at known
      exact False.elim (clear group member active node.task.occurrence recorded _
        ⟨producer, payload, known⟩ owner)

/-- Every complete supplied host batch leaves active groups without cached rejection.
Witness: actual batched replay excludes all consumed failed contributors, while every
retained rejection comes from one of those source notifications. No flattening bridge
or output-admission premise is used.
-/
theorem createWorkQueue_runNormalized_noActiveCachedFailure {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.NoActiveCachedFailure := by
  have initial : (State.initialize (Work.fromExecution work)).ActiveFailuresAbsent work [] := by
    intro _ _ _ occurrence recorded
    cases recorded
  have clear := initial.runNormalized
    (createWorkQueue_retainedFailures (Work.fromExecution work) work)
    (createWorkQueue_pendingAccounting work generated.declarations) (createWorkQueue_producerOrder work).1
    (createWorkQueue_producerOrder work).2 generated (before := [])
    (by intro _ member; cases member) batches (by simpa using valid)
    (by rwa [inputsStarted_eq_batchesStarted] at started)
  simp only [List.append_nil] at clear
  have ledger := generated.runNormalized_successLedger batches valid started
  apply clear.noActiveCachedFailure ledger.sound ledger.matching
  exact (createWorkQueue_runNormalized_taskRejections (Work.fromExecution work)
          batches).mono
    (fun occurrence errors member =>
      List.mem_reverse.mpr
        (List.mem_flatMap.mpr
          ⟨.taskFailure occurrence errors, member, List.mem_cons_self⟩))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
