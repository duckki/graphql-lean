import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureNotices

/-! Task activation records a contributing owner that has already been announced. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Recover the contributing owner at each executable start boundary
-----------------------------------------------------------------------------------------

/-- A task newly started during registration has a contributor in the active root set.
Witness: the exact registration guard; membership updates preserve roots and task nodes.
-/
theorem State.addTask_startedOldOrRootOwner (queue : State) (task : Task)
    {node : TaskNode} (member : node ∈ (queue.addTask task).taskNodes)
    : node ∈ queue.taskNodes
      ∨ node = { task } ∧ ∃ owner ∈ task.groups, owner.key ∈ queue.rootGroups := by
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.key with
    | none => current
    | some groupNode =>
        if groupNode.tasks.contains task.occurrence then current
        else current.putGroupNode
          { groupNode with
              tasks := groupNode.tasks ++ [task.occurrence]
              pending := groupNode.pending + 1 }
  have stepCore (current : State) (group : Execution.DeliveryNode)
      : (step current group).taskNodes = current.taskNodes
        ∧ (step current group).rootGroups = current.rootGroups := by
    unfold step
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
  have foldCore (groups : List Execution.DeliveryNode) (current : State)
      : (groups.foldl step current).taskNodes = current.taskNodes
        ∧ (groups.foldl step current).rootGroups = current.rootGroups := by
    induction groups generalizing current with
    | nil => exact ⟨rfl, rfl⟩
    | cons group rest ih =>
        exact ⟨(ih (step current group)).1.trans (stepCore current group).1,
          (ih (step current group)).2.trans (stepCore current group).2⟩
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have core := foldCore task.groups { queue with tasks := queue.tasks ++ [task] }
  change node ∈ (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
        { current with taskNodes := current.taskNodes ++ [{ task }] }
      else current).taskNodes at member
  split at member
  · rename_i accepted
    rcases List.mem_append.mp member with old | fresh
    · exact Or.inl (core.1 ▸ old)
    · refine Or.inr ⟨List.mem_singleton.mp fresh, ?_⟩
      simp only [Bool.and_eq_true_iff] at accepted
      obtain ⟨owner, contributes, active⟩ := List.any_eq_true.mp accepted.1
      exact ⟨owner, contributes, core.2 ▸ List.contains_iff_mem.mp active⟩
  · exact Or.inl (core.1 ▸ member)

/-- A newly activated task names one of the groups released at this activation boundary.
Witness: activation requests a listed occurrence, and sound registration identifies its
contributors exactly. Already started tasks are retained without requiring a live owner.
-/
theorem State.startNewWork_startedOldOrOwner {queue : State} {work : Execution.Work}
    (sound : queue.GroupMembershipSound) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (newWork : NewWork)
    {node : TaskNode} (member : node ∈ (queue.startNewWork newWork).taskNodes)
    : node ∈ queue.taskNodes
      ∨ ∃ owner ∈ node.task.groups,
          owner.key ∈ newWork.newGroups.map Execution.DeliveryNode.key := by
  rcases queue.startNewWork_oldOrRequested newWork member with old | requested
  · exact Or.inl old
  · right
    obtain ⟨group, groupMember, listed⟩ := List.mem_flatMap.mp requested
    change node.task.occurrence ∈
      (if group.group.node.key ∈ newWork.newGroups.map Execution.DeliveryNode.key
        then group.tasks else []) at listed
    split at listed
    · rename_i released
      have finalSound := sound.startNewWork newWork
      have finalRegistered := registered.startNewWork newWork
      have finalMatching := matching.startNewWork newWork
      have finalGroup : group ∈ (queue.startNewWork newWork).groupNodes := by
        rwa [(queue.startNewWork_groupCore newWork).1]
      have contributes := finalSound.startedOwner finalRegistered finalMatching
        member finalGroup listed
      obtain ⟨owner, ownerMember, keyEq⟩ := List.mem_map.mp contributes
      exact ⟨owner, ownerMember, keyEq ▸ released⟩
    · cases listed

-----------------------------------------------------------------------------------------
-- Preserve historical notices, even after their announcing owner has closed
-----------------------------------------------------------------------------------------

/-- Each live task node has a contributor in the historical group-notice keys `announced`.
This is proof-only evidence; it does not require that contributor to remain active.
-/
def State.StartedTasksAnnounced (queue : State) (announced : Keys) : Prop :=
  ∀ node ∈ queue.taskNodes, ∃ owner ∈ node.task.groups, owner.key ∈ announced

/-- Enlarging the notice history preserves all recorded start justifications.
Witness: transport the contributing owner's membership along the key inclusion.
-/
theorem State.StartedTasksAnnounced.mono {queue : State} {before after : Keys}
    (known : queue.StartedTasksAnnounced before) (included : before.Subset after)
    : queue.StartedTasksAnnounced after := by
  intro node member
  obtain ⟨owner, contributes, announced⟩ := known node member
  exact ⟨owner, contributes, included announced⟩

/-- Updating one task node preserves announcement evidence supplied for its task.
Witness: every updated map entry is either the replacement or an unchanged old node.
-/
theorem State.StartedTasksAnnounced.putTaskNode {queue : State} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced) (updated : TaskNode)
    (owner : ∃ group ∈ updated.task.groups, group.key ∈ announced)
    : (queue.putTaskNode updated).StartedTasksAnnounced announced := by
  intro node member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    exact owner
  · subst node
    exact known old oldMember

/-- Removing a completed or cancelled task preserves surviving start justifications.
Witness: task cleanup filters old task nodes without changing their contributors.
-/
theorem State.StartedTasksAnnounced.removeTask {queue : State} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced) (occurrence : Occurrence)
    : (queue.removeTask occurrence).StartedTasksAnnounced announced :=
  fun node member => known node (List.mem_filter.mp member).1

/-- Group cancellation preserves historical witnesses even when their owner is removed.
Witness: surviving task nodes are unchanged; the notice history is not filtered.
-/
theorem State.StartedTasksAnnounced.removeGroup {queue : State} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced) (key : Nat)
    : (queue.removeGroup key).StartedTasksAnnounced announced :=
  fun node member => known node (List.mem_filter.mp member).1

/-- Accepted or ignored task failures preserve surviving tasks' historical notice owners.
Witness: the executable failure handler keeps only unchanged old task nodes.
-/
theorem State.StartedTasksAnnounced.taskFailure {queue : State} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.StartedTasksAnnounced announced :=
  fun node member => known node (queue.taskFailure_startedSubset occurrence errors member)

/-- Group registration cannot change a started task's historical notice witness.
Witness: the exact task-node map equation for group integration.
-/
theorem State.StartedTasksAnnounced.addGroups {queue : State} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced) (groups : List Group)
    : (queue.addGroups groups).1.StartedTasksAnnounced announced := by
  intro node member
  rw [State.addGroups_taskNodes] at member
  exact known node member

/-- Registration starts tasks only through already announced active contributors.
Witness: preserve old nodes' historical witness or use the executable registration guard.
-/
theorem State.StartedTasksAnnounced.addTask {queue : State} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced)
    (roots : queue.rootGroups.Subset announced) (task : Task)
    : (queue.addTask task).StartedTasksAnnounced announced := by
  intro node member
  rcases queue.addTask_startedOldOrRootOwner task member with old | fresh
  · exact known node old
  · obtain ⟨rfl, owner, contributes, active⟩ := fresh
    exact ⟨owner, contributes, roots active⟩

/-- Stream registration only changes an existing producer task's child-stream list.
Witness: the producer keeps its task and therefore the same historical notice witness.
-/
theorem State.StartedTasksAnnounced.addStreams {queue : State} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.StartedTasksAnnounced announced := by
  cases parentTask with
  | none => exact known
  | some occurrence =>
      simp only [State.addStreams]
      split
      · exact known
      · rename_i node found
        apply known.putTaskNode
        exact known node (List.mem_of_find?_eq_some found)

/-- Integrating child work starts tasks only under already announced active roots.
Witness: registration preserves root keys; each task insertion supplies its active owner.
-/
theorem State.StartedTasksAnnounced.maybeIntegrateWork {queue : State} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced)
    (roots : queue.rootGroups.Subset announced) (newWork : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.StartedTasksAnnounced
        announced := by
  have taskFold (tasks : List Task) (current : State)
      (currentKnown : current.StartedTasksAnnounced announced)
      (currentRoots : current.rootGroups.Subset announced)
      : (tasks.foldl State.addTask current).StartedTasksAnnounced announced := by
    induction tasks generalizing current with
    | nil => exact currentKnown
    | cons task rest ih =>
        apply ih _ (currentKnown.addTask currentRoots task)
        rwa [State.addTask_rootGroups]
  have integrated := taskFold newWork.tasks _ (known.addGroups newWork.groups)
    (by rwa [State.addGroups_rootGroups])
  exact integrated.addStreams newWork.streams parentTask

/-- Pruning empty group shells keeps every started task's notice witness.
Witness: pruning changes only the group-node map, not task nodes.
-/
theorem State.StartedTasksAnnounced.pruneEmptyGroups {queue : State} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.StartedTasksAnnounced announced := by
  intro node member
  rw [State.pruneEmptyGroups_taskNodes] at member
  exact known node member

/-- Group activation supplies notice witnesses for precisely the newly started tasks.
Witness: sound activation ownership and monotonic transport of old historical notices.
-/
theorem State.StartedTasksAnnounced.startNewWork {queue : State} {work : Execution.Work}
    {announced : Keys} (known : queue.StartedTasksAnnounced announced)
    (sound : queue.GroupMembershipSound) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (newWork : NewWork)
    : (queue.startNewWork newWork).StartedTasksAnnounced
        (announced ++ newWork.newGroups.map Execution.DeliveryNode.key) := by
  intro node member
  rcases queue.startNewWork_startedOldOrOwner sound registered matching newWork member with
    old | fresh
  · exact (known.mono (List.subset_append_left _ _)) node old
  · obtain ⟨owner, contributes, released⟩ := fresh
    exact ⟨owner, contributes, List.mem_append_right _ released⟩

-----------------------------------------------------------------------------------------
-- Release-time draining retains old notices and supplies new ones before activation
-----------------------------------------------------------------------------------------

/-- Successful group flushing preserves notice witnesses for surviving task nodes.
Witness: the flush selects and removes task nodes; retained nodes have unchanged tasks.
-/
theorem State.StartedTasksAnnounced.finishGroupSuccess {queue : State} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.StartedTasksAnnounced announced := by
  obtain ⟨_, _, _, _, retained, _, _⟩ := queue.finishGroupSuccess_selection group
  exact fun node member => known node (retained member)

/-- Ready-group draining justifies every newly started task by its actual carrier notice.
Witness: induction over the executable drain, composing success activation with old
historical notices; cached failure closures only remove task nodes and keep old witnesses.
-/
theorem State.StartedTasksAnnounced.drainReadyGroups {queue : State}
    {work : Execution.Work} {announced : Keys}
    (known : queue.StartedTasksAnnounced announced) (sound : queue.GroupMembershipSound)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    : queue.drainReadyGroups.1.StartedTasksAnnounced
        (announced ++ queue.drainReadyGroups.2.flatMap rawGroupNoticeKeys) := by
  have loop (fuel : Nat) (current : State) (seen : Keys)
      (currentKnown : current.StartedTasksAnnounced seen)
      (currentSound : current.GroupMembershipSound)
      (currentRegistered : current.StartedTasksRegistered)
      (currentMatching : current.RegisteredTasksMatch work)
      : (State.drainReadyGroups.go fuel current).1.StartedTasksAnnounced
          (seen ++ (State.drainReadyGroups.go fuel current).2.flatMap rawGroupNoticeKeys) := by
    induction fuel generalizing current seen with
    | zero => simpa [State.drainReadyGroups.go] using currentKnown
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · simpa using currentKnown
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              let first := current.finishGroupSuccess node
              have firstSound := (currentSound.finishGroupSuccess node).startNewWork first.2.2
              have firstRegistered :=
                (currentRegistered.finishGroupSuccess node).startNewWork first.2.2
              have firstMatching :=
                (currentMatching.finishGroupSuccess node).startNewWork first.2.2
              have firstKnown := (currentKnown.finishGroupSuccess node).startNewWork
                (currentSound.finishGroupSuccess node)
                (currentRegistered.finishGroupSuccess node)
                (currentMatching.finishGroupSuccess node) first.2.2
              rw [current.finishGroupSuccess_groupNotices node] at firstKnown
              simpa only [List.flatMap_append, List.append_assoc]
                using ih _ _ firstKnown firstSound firstRegistered firstMatching
          | some errors =>
              have firstKnown := currentKnown.removeGroup node.group.node.key
              simpa only [State.finishGroupFailure, List.flatMap_append,
                List.flatMap_singleton, rawGroupNoticeKeys, List.nil_append]
                using ih _ _ firstKnown (currentSound.finishGroupFailure node errors)
                  (currentRegistered.finishGroupFailure node errors)
                  (currentMatching.finishGroupFailure node errors)
  exact loop _ queue announced known sound registered matching

-----------------------------------------------------------------------------------------
-- Initial task starts are justified by the actual initial notices
-----------------------------------------------------------------------------------------

/-- Every initially started task has a contributor among the queue's initial notices.
Witness: integration has no active roots, then activation supplies a genuine contributing
owner for every newly started task. No generated-work or output-admission premise is used.
-/
theorem createWorkQueue_startedTasksAnnounced (work : Execution.Work)
    : let queue := State.initialize (Work.fromExecution work)
      queue.StartedTasksAnnounced
        (queue.initialGroups.map Execution.DeliveryNode.key) := by
  let integrated := (({} : State).maybeIntegrateWork (Work.fromExecution work)).1
  let newWork := (({} : State).maybeIntegrateWork (Work.fromExecution work)).2
  let pruned := (integrated.pruneEmptyGroups newWork.newGroups).1
  let groups := (integrated.pruneEmptyGroups newWork.newGroups).2
  let roots := { newWork with newGroups := groups }
  have emptyKnown : ({} : State).StartedTasksAnnounced [] := by
    intro node member
    cases member
  have integratedKnown : integrated.StartedTasksAnnounced [] :=
    emptyKnown.maybeIntegrateWork (by intro key member; cases member) (Work.fromExecution work)
  have prunedKnown : pruned.StartedTasksAnnounced [] :=
    integratedKnown.pruneEmptyGroups newWork.newGroups
  have emptySound : ({} : State).GroupMembershipSound := by
    intro node member
    cases member
  have sound : pruned.GroupMembershipSound :=
    (emptySound.maybeIntegrateWork (Work.fromExecution work)).pruneEmptyGroups newWork.newGroups
  have emptyRegistered : ({} : State).StartedTasksRegistered := by
    intro node member
    cases member
  have registered : pruned.StartedTasksRegistered :=
    (emptyRegistered.maybeIntegrateWork (Work.fromExecution work)).pruneEmptyGroups newWork.newGroups
  have matching : pruned.RegisteredTasksMatch work := by
    intro task member
    apply createWorkQueue_fromSpec_registeredTasksMatch work task
    change task ∈ (pruned.startNewWork roots).tasks
    rwa [(pruned.startNewWork_groupCore roots).2.1]
  exact prunedKnown.startNewWork sound registered matching roots

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
