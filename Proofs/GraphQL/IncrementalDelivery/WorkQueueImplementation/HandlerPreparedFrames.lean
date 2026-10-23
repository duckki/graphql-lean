import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActualSourceFrames

/-! Actual successful preparation retains parent and root frames under its batch snapshot. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The storing and integration phase of task success retains its structural source frames. -/
theorem UncancelledReplayFrame.taskSuccess_preparedFrames
    {queue work parents before} (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (incoming : TaskNode) (available : List (Occurrence × Nat))
    (found : (queue.cacheTaskFailures available).taskNode? occurrence = some incoming)
    : let current := queue.cacheTaskFailures available
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      ParentCutFrame prepared work parents ∧ RootReplayFrame prepared work parents := by
  intro current stored prepared
  have parent := frame.parent.cacheTaskFailures available
  have roots := frame.roots.cacheTaskFailures available
  have registered := parent.registration.started incoming (State.taskNode?_some found).1
  have certificate := (parent.registration.children incoming.task registered).sourceChild
    (State.taskNode?_some found).2 matching
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
  have records := fun group member => matching.taskChildGroups_recordAt (group := group) member
  have fields := fun group member =>
    matching.taskChildGroups_parentCanonical canonical (group := group) member
  exact ⟨
    storedParent.maybeIntegrateWork result.work records fields certificate
      (some occurrence) generated canonical,
    storedRoots.maybeIntegrateWork result.work records fields certificate.contributors
      (by
        intro task member group contributes
        exact (childTasks task member).contributorKnown (List.mem_map_of_mem contributes))
      (some occurrence) generated canonical certificate.parentRefs
  ⟩

/-- Item preparation retains the same parent and root frames before the shared drain. -/
theorem UncancelledReplayFrame.streamItems_preparedFrames
    {queue work parents before stream items}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat))
    : let current := queue.cacheTaskFailures available
      let prepared := current.preparedStreamItems items available
      ParentCutFrame prepared work parents ∧ RootReplayFrame prepared work parents := by
  let parent := frame.parent.cacheTaskFailures available
  let roots := frame.roots.cacheTaskFailures available
  have preparedParent := State.preparedStreamItems_preserves
    (fun current => ParentCutFrame current work parents) parent items available
    (fun _ _ member prior =>
      prior.integrateStreamItem generated canonical matching member available)
  have preparedRoots := roots.live.prepareItems roots.retired generated canonical matching available
  exact ⟨preparedParent, preparedRoots.1, preparedRoots.2⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
