import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchedPublicationCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionBoundaries

/-! Actual handler phases exclude the same prior and local publication labels before startup. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Derived same-ledger exclusion at one source input and its supplied rejection snapshot. -/
structure HandlerMembershipCut (queue : State) (event : GraphEvent)
    (published : List ObjectPublication) (prior : List WorkQueueEvent)
    (available : List (Occurrence × Nat))
    : Prop where
  before
    : ∀ publication ∈ published.take (prior.flatMap WorkQueueEvent.objectValues).length,
        (queue.cacheTaskFailures available).TaskMembershipAbsent publication.1
        ∧ ∀ child ∈ event.childTasks, publication.1 ≠ child.occurrence
  localLedger
    : queue.ReplayClosuresCovered [event]
        (published.drop (prior.flatMap WorkQueueEvent.objectValues).length) available

private theorem split_labels {published : List ObjectPublication}
    {publication offset count full} (bounded : count ≤ full)
    (member : publication ∈ published.take (offset + count))
    : publication ∈ published.take offset
      ∨ publication ∈ ((published.drop offset).take full).take count := by
  rw [List.take_add] at member
  simpa only [List.mem_append, List.take_take, Nat.min_eq_left bounded] using member

/-- Each actual owner-fold prefix excludes all labels published by that boundary. -/
theorem HandlerMembershipCut.taskSuccess_foldMemberships
    {queue occurrence result published prior available incoming}
    (cut
      : HandlerMembershipCut queue (.taskSuccess occurrence result) published prior
          available)
    : let current := queue.cacheTaskFailures available
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      current.taskNode? occurrence = some incoming
      → ∀ steps,
          steps ≤ incoming.task.groups.length
          → let boundary :=
              (incoming.task.groups.take steps).foldl successGroupStep (prepared, [], {})
            ∀ publication ∈
              published.take
                ((prior.flatMap WorkQueueEvent.objectValues).length
                  + (boundary.2.1.flatMap WorkQueueEvent.objectValues).length),
              boundary.1.TaskMembershipAbsent publication.1 := by
  intro current stored prepared found steps bounded boundary publication member
  have count := successGroupFold_objectCount_take_le incoming.task.groups (prepared, [], {}) steps
  have full : (boundary.2.1.flatMap WorkQueueEvent.objectValues).length
      ≤ ((queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1.flatMap
          WorkQueueEvent.objectValues).length := by
    change _ ≤ ((current.taskSuccess occurrence result available).2.1.flatMap
      WorkQueueEvent.objectValues).length
    rw [current.taskSuccess_eq occurrence result incoming found available]
    simp only [List.flatMap_append, List.length_append]
    exact Nat.le_trans count (Nat.le_add_right _ _)
  rcases split_labels full member with old | new
  · obtain ⟨absent, fresh⟩ := cut.before publication old
    exact ((absent.putTaskNode { incoming with value := some result.value }).maybeIntegrateWork
      result.work fresh (some occurrence)).successGroupFold
        (incoming.task.groups.take steps) [] {}
  · exact (cut.localLedger.2.2.2.2.2.2.2.1 incoming found).ownerFold steps bounded publication new

/-- Actual task-drain flushes exclude the full ledger before cached child startup. -/
theorem HandlerMembershipCut.taskSuccess_drainStartupMemberships
    {queue occurrence result published prior available incoming}
    (cut
      : HandlerMembershipCut queue (.taskSuccess occurrence result) published prior
          available)
    : let current := queue.cacheTaskFailures available
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := (released.1.startNewWork released.2.2 available).1
      current.taskNode? occurrence = some incoming
      → active.DrainStartupMembershipsCleared active.groupNodes.length published available
          (prior ++ released.2.1) := by
  intro current stored prepared released active found steps bounded node
  dsimp only
  intro chosen publication member
  have count := active.drainReadyGroups_beforeStartup_objectCount_le bounded available chosen
  have full : ((released.2.1 ++ (State.drainReadyGroups.go available steps active).2.1
        ++ ((State.drainReadyGroups.go available steps active).1.finishGroupSuccess
          node).2.1).flatMap WorkQueueEvent.objectValues).length
      ≤ ((queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1.flatMap
          WorkQueueEvent.objectValues).length := by
    change _ ≤ ((current.taskSuccess occurrence result available).2.1.flatMap
      WorkQueueEvent.objectValues).length
    rw [current.taskSuccess_eq occurrence result incoming found available]
    simpa only [List.flatMap_append, List.length_append, Nat.add_assoc, State.drainReadyGroups,
      stored, prepared, released, active] using Nat.add_le_add_left count
        (released.2.1.flatMap WorkQueueEvent.objectValues).length
  have selected : publication ∈ published.take
      ((prior.flatMap WorkQueueEvent.objectValues).length
        + ((released.2.1 ++ (State.drainReadyGroups.go available steps active).2.1
          ++ ((State.drainReadyGroups.go available steps active).1.finishGroupSuccess
            node).2.1).flatMap WorkQueueEvent.objectValues).length) := by
    simpa only [List.flatMap_append, List.length_append, Nat.add_assoc] using member
  rcases split_labels full selected with old | fresh
  · obtain ⟨absent, childFresh⟩ := cut.before publication old
    have integrated := (absent.putTaskNode
      { incoming with value := some result.value }).maybeIntegrateWork result.work childFresh
        (some occurrence)
    have started := (integrated.successGroupFold incoming.task.groups [] {}).startNewWork
      released.2.2 available
    exact (started.drainReadyGroups_go steps available).finishGroupSuccess node
  · apply (cut.localLedger.2.2.2.2.2.2.2.1 incoming found).startup
      steps bounded node chosen publication
    simpa only [List.flatMap_append, List.length_append, Nat.add_assoc, State.dispatchGraphEvent] using fresh

/-- Actual item-drain flushes retain prior exclusions before cached child startup. -/
theorem HandlerMembershipCut.streamItems_drainStartupMemberships
    {queue stream items published prior available}
    (cut
      : HandlerMembershipCut queue (.streamItems stream items) published prior available)
    : let current := queue.cacheTaskFailures available
      let prepared := current.preparedStreamItems items available
      current.rootStreams.contains stream.ref = true
      → prepared.DrainStartupMembershipsCleared prepared.groupNodes.length published
          available prior := by
  intro current prepared active steps bounded node
  dsimp only
  intro chosen publication member
  have count := prepared.drainReadyGroups_beforeStartup_objectCount_le bounded available chosen
  have full : (((State.drainReadyGroups.go available steps prepared).2.1
        ++ ((State.drainReadyGroups.go available steps prepared).1.finishGroupSuccess
          node).2.1).flatMap WorkQueueEvent.objectValues).length
      ≤ ((queue.handleGraphEvent (.streamItems stream items) available).2.1.flatMap
          WorkQueueEvent.objectValues).length := by
    change _ ≤ ((current.streamItems stream items available).2.1.flatMap
      WorkQueueEvent.objectValues).length
    rw [current.streamItems_eq stream items available]
    simpa only [active, Bool.not_true, Bool.false_eq_true, ite_false, List.flatMap_cons,
      WorkQueueEvent.objectValues, List.nil_append, State.drainReadyGroups,
      State.preparedStreamItems, prepared] using count
  have selected : publication ∈ published.take
      ((prior.flatMap WorkQueueEvent.objectValues).length
        + (((State.drainReadyGroups.go available steps prepared).2.1
          ++ ((State.drainReadyGroups.go available steps prepared).1.finishGroupSuccess
            node).2.1).flatMap WorkQueueEvent.objectValues).length) := by
    simpa only [List.flatMap_append, List.length_append, Nat.add_assoc] using member
  rcases split_labels full selected with old | fresh
  · obtain ⟨absent, childFresh⟩ := cut.before publication old
    have ready := absent.preparedStreamItems items (by
      intro item itemMember child childMember
      exact childFresh child (List.mem_flatMap.mpr ⟨item, itemMember, childMember⟩)) available
    exact (ready.drainReadyGroups_go steps available).finishGroupSuccess node
  · apply cut.localLedger.2.2.2.2.2.2.2.1.startup active steps bounded node chosen publication
    simpa only [List.nil_append, State.dispatchGraphEvent] using fresh

namespace ConformancePlan

/-- Actual batch/FIFO evidence derives the handler's full common-ledger membership cut. -/
theorem batchHandlerMembershipCut
    {work inputs published earlier batch later fifo event tail}
    (batches : (initialQueue work).BatchClosuresCovered inputs published)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (inputEq : inputs = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ event :: tail)
    : let boundary := (initialQueue work).replayBatches earlier
      let available := GraphEvent.availableFailures batch
      let current := boundary.replayGraphEvents fifo available
      let prior :=
        ((initialQueue work).rawBatches earlier).2
        ++ (boundary.rawEventReplay fifo available).2
      HandlerMembershipCut current event published prior available := by
  let boundary := (initialQueue work).replayBatches earlier
  let available := GraphEvent.availableFailures batch
  have frame := batchPublicationCut batches valid started earlier batch later fifo inputEq
    ⟨event :: tail, batchEq.symm⟩
  have prefixValid := valid.prefix (show (earlier.flatten ++ fifo ++ [event]).IsPrefix
    inputs.flatten from ⟨tail ++ later.flatten, by simp [inputEq, batchEq, List.append_assoc]⟩)
  obtain ⟨_, matching, fresh⟩ := validGraphEvents_last prefixValid
  refine ⟨?_, ?_⟩
  · intro publication member
    simp only [List.flatMap_append, List.length_append] at member
    obtain ⟨absent, registered⟩ := frame.2.2 publication member
    exact ⟨absent.cacheTaskFailures available, fun child incoming same =>
      matching.childTask_not_registered frame.1 fresh incoming (same ▸ registered)⟩
  · simpa only [List.flatMap_append, List.length_append]
      using batchHandlerPublicationCut batches started inputEq batchEq

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
