import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ActivationCatalogues
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalBookkeeping

/-! Sound source registration makes native startup a filter of the live group records.
This field frame follows fused disposal directly, without an activation refinement premise.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)

/-- Fused disposal only removes group records when task descriptors and memberships agree. -/
theorem State.removeGroup_groupNodes_sublist_of_matching {state : State} {work : Work}
    (matching : state.queue.RegisteredTasksMatch work)
    (sound : state.queue.GroupMembershipSound) (ref : NodeRef)
    (targets : List CleanupTarget := [])
    : (state.removeGroup ref targets).1.queue.groupNodes.Sublist
        state.queue.groupNodes := by
  have loop (fuel : Nat) (current : State) (pending removed) (targets)
      (matching : current.queue.RegisteredTasksMatch work)
      (sound : current.queue.GroupMembershipSound)
      : let final := State.removeGroup.walk fuel current pending removed targets
        final.1.queue.groupNodes.Sublist current.queue.groupNodes
        ∧ final.1.queue.RegisteredTasksMatch work ∧ final.1.queue.GroupMembershipSound := by
    induction fuel generalizing current pending removed targets with
    | zero => simp only [State.removeGroup.walk]; exact ⟨.refl _, matching, sound⟩
    | succ fuel ih =>
        induction pending generalizing current removed targets with
        | nil => simp only [State.removeGroup.walk]; exact ⟨.refl _, matching, sound⟩
        | cons key rest tailIH =>
            cases found : current.queue.groupNode? key with
            | none =>
                simpa only [State.removeGroup.walk, found]
                  using tailIH current removed targets matching sound
            | some group =>
                rw [State.removeGroup.walk, found]
                let erased := eraseRemovalGroup current key
                let folded := group.tasks.foldl fusedRemovalTaskStep (erased, targets)
                have frame := fusedRemovalTaskFold_bookkeeping group.tasks (erased, targets)
                  (eraseRemovalGroup_registeredTasksMatch matching key)
                  (eraseRemovalGroup_groupMembershipSound sound key)
                have next := ih folded.1 (group.childGroups ++ rest) (key :: removed) folded.2
                  frame.2.1 frame.2.2
                refine ⟨next.1.trans ?_, next.2⟩
                rw [frame.1]
                exact List.filter_sublist
  exact (loop _ state [ref] [] targets matching sound).1

private theorem startTasks_groupNodes (tasks : List Occurrence)
    (queue : ReferenceWorkQueue.State) (available : List (Occurrence × Nat))
    : (tasks.foldl (fun current task => current.startTask task available)
        queue).groupNodes
      = queue.groupNodes := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      rw [List.foldl_cons, ih, ReferenceWorkQueue.State.startTask_groupNodes]

/-- Each native cached startup branch retains whole surviving group records. -/
theorem State.startGroup_groupNodes_sublist_of_matching {state : State} {work : Work}
    (matching : state.queue.RegisteredTasksMatch work)
    (sound : state.queue.GroupMembershipSound) (ref : NodeRef)
    (targets : List CleanupTarget := []) (available : List (Occurrence × Nat) := [])
    : (state.startGroup ref targets available).1.queue.groupNodes.Sublist
        state.queue.groupNodes := by
  have cachedMatching := matching.cacheTaskFailures available
  have cachedSound := sound.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · rw [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes]; exact .refl _
  · rename_i group found
    split
    · rw [startTasks_groupNodes, ReferenceWorkQueue.State.cacheTaskFailures_groupNodes]
      exact .refl _
    · have included := State.removeGroup_groupNodes_sublist_of_matching
        (state := { state with queue := state.queue.cacheTaskFailures available })
        cachedMatching cachedSound group.group.node.ref targets
      simpa only [State.finishGroupFailure,
        ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] using included

/-- Native activation retains whole group records under source registration consistency.
Cached failure is allowed; the frame does not assume that any selected owner survives.
-/
theorem State.startNewWork_groupNodes_sublist_of_matching {state : State} {work : Work}
    (matching : state.queue.RegisteredTasksMatch work)
    (sound : state.queue.GroupMembershipSound) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    (available : List (Occurrence × Nat) := [])
    : (state.startNewWork roots integrated targets available).1.queue.groupNodes.Sublist
        state.queue.groupNodes := by
  have loop (refs : NodeRefs)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      (matching : acc.1.queue.RegisteredTasksMatch work)
      (sound : acc.1.queue.GroupMembershipSound)
      : (refs.foldl
          (fun (current, targets, failures) ref =>
            let (next, targets, queued) := current.startGroup ref targets available
            (next, targets, failures ++ queued)) acc).1.queue.groupNodes.Sublist
          acc.1.queue.groupNodes := by
    induction refs generalizing acc with
    | nil => exact .refl _
    | cons ref rest ih =>
        let step := acc.1.startGroup ref acc.2.1 available
        have groups := State.startGroup_groupNodes_sublist_of_matching matching sound ref
          acc.2.1 available
        have catalogue := State.startGroup_permanentCatalogues acc.1 ref acc.2.1 available
        have nextMatching : step.1.queue.RegisteredTasksMatch work := by
          simpa only [step, ReferenceWorkQueue.State.RegisteredTasksMatch, catalogue.1]
            using matching
        have nextSound : step.1.queue.GroupMembershipSound := by
          intro node member occurrence linked
          obtain ⟨task, registered, same, contributes⟩ := sound node (groups.subset member)
            occurrence linked
          exact ⟨task, catalogue.1.symm ▸ registered, same, contributes⟩
        exact (ih (step.1, step.2.1, acc.2.2 ++ step.2.2) nextMatching nextSound).trans
          groups
  have streams (more : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
      : (more.foldl (fun current stream => current.startStream stream.ref) queue).groupNodes
        = queue.groupNodes := by
    induction more generalizing queue with
    | nil => rfl
    | cons stream rest ih =>
        rw [List.foldl_cons, ih, ReferenceWorkQueue.State.startStream_groupNodes]
  have tasks (more : List ReferenceWorkQueue.Task) (queue : ReferenceWorkQueue.State)
      : (more.foldl (fun current task => current.startTask task.occurrence available)
          queue).groupNodes = queue.groupNodes := by
    induction more generalizing queue with
    | nil => rfl
    | cons task rest ih =>
        rw [List.foldl_cons, ih, ReferenceWorkQueue.State.startTask_groupNodes]
  have streamFrame (more : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
      (matching : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
      : (more.foldl (fun current stream => current.startStream stream.ref)
          queue).RegisteredTasksMatch work
        ∧ (more.foldl (fun current stream => current.startStream stream.ref)
          queue).GroupMembershipSound := by
    induction more generalizing queue with
    | nil => exact ⟨matching, sound⟩
    | cons stream rest ih =>
        exact ih _ (matching.startStream stream.ref) (sound.startStream stream.ref)
  have taskFrame (more : List ReferenceWorkQueue.Task) (queue : ReferenceWorkQueue.State)
      (matching : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
      : (more.foldl (fun current task => current.startTask task.occurrence available)
          queue).RegisteredTasksMatch work
        ∧ (more.foldl (fun current task => current.startTask task.occurrence available)
          queue).GroupMembershipSound := by
    induction more generalizing queue with
    | nil => exact ⟨matching, sound⟩
    | cons task rest ih =>
        exact ih _ (matching.startTask task.occurrence available)
          (sound.startTask task.occurrence available)
  unfold State.startNewWork
  split
  · exact .refl _
  · dsimp only
    let rooted := { state.queue with
      rootGroups := state.queue.rootGroups ++ roots.newGroups.map Execution.DeliveryNode.ref }
    let installed := roots.newStreams.foldl
      (fun current stream => current.startStream stream.ref) rooted
    let started := integrated.activeTasks.foldl
      (fun current task => current.startTask task.occurrence available) installed
    have ready := streamFrame roots.newStreams rooted matching sound
    have source := taskFrame integrated.activeTasks installed ready.1 ready.2
    have groups := loop (roots.newGroups.map Execution.DeliveryNode.ref)
      ({ state with queue := started },
        ({ state with queue := installed } : State).disposeRejectedTasks integrated targets, [])
      source.1 source.2
    have same : started.groupNodes = state.queue.groupNodes :=
      (tasks integrated.activeTasks installed).trans (streams roots.newStreams rooted)
    exact groups.trans (by rw [same]; exact .refl _)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
