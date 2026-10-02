import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticePublicationExclusion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFoldNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNoticeContents

/-! Internal successful-carrier boundaries retain exact task and membership metadata. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every processed owner and bounded drain prefix retains both task invariants
-----------------------------------------------------------------------------------------

/-- The single-pass owner fold retains sound memberships and registered-task provenance.
Witness: decrementing a counter keeps the selected record's memberships, and successful
flushing preserves both invariants. The result applies to any processed owner prefix.
-/
theorem State.successGroupFold_noticeTaskProvenance {queue : State} {work}
    (sound : queue.GroupMembershipSound) (registered : queue.RegisteredTasksMatch work)
    (groups : List Execution.DeliveryNode)
    : let boundary := (groups.foldl successGroupStep (queue, [], {})).1
      boundary.GroupMembershipSound ∧ boundary.RegisteredTasksMatch work := by
  have loop (more : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (sound : acc.1.GroupMembershipSound) (registered : acc.1.RegisteredTasksMatch work)
      : (more.foldl successGroupStep acc).1.GroupMembershipSound
        ∧ (more.foldl successGroupStep acc).1.RegisteredTasksMatch work := by
    induction more generalizing acc with
    | nil => exact ⟨sound, registered⟩
    | cons group rest ih =>
        simp only [List.foldl_cons, successGroupStep]
        split
        · exact ih acc sound registered
        · rename_i node found
          let updated := { node with pending := node.pending - 1 }
          have nextSound := sound.putGroupNode updated
            (sound node (List.mem_of_find?_eq_some found))
          have nextRegistered := registered.putGroupNode updated
          split
          · exact ih _ (nextSound.finishGroupSuccess updated)
              (nextRegistered.finishGroupSuccess updated)
          · exact ih _ nextSound nextRegistered
  exact loop groups (queue, [], {}) sound registered

/-- Every actual bounded drain prefix retains task provenance, including after failures.
Witness: use the existing finite-loop induction; successful flush/activation preserves
both facts, while failed cleanup only removes group records and task nodes.
-/
theorem State.drainReadyGroups_go_noticeTaskProvenance {queue : State} {work}
    (sound : queue.GroupMembershipSound) (registered : queue.RegisteredTasksMatch work)
    (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.GroupMembershipSound
      ∧ (State.drainReadyGroups.go fuel queue).1.RegisteredTasksMatch work := by
  apply State.drainReadyGroups_go_preserves
    (fun current => current.GroupMembershipSound ∧ current.RegisteredTasksMatch work)
    (valid := ⟨sound, registered⟩)
  · intro current node prior _ _ _ _
    exact ⟨(prior.1.finishGroupSuccess node).startNewWork _,
      (prior.2.finishGroupSuccess node).startNewWork _⟩
  · intro current node errors prior _ _ _
    exact ⟨prior.1.finishGroupFailure node errors, prior.2.finishGroupFailure node errors⟩

-----------------------------------------------------------------------------------------
-- The incoming task derives its prepared metadata from actual source replay
-----------------------------------------------------------------------------------------

/-- A matching successful input supplies task metadata before any owner is processed.
Witness: initialization and matching replay preserve both invariants; storing a value
changes neither, and each integrated child has exact structural task provenance.
-/
theorem createWorkQueue_taskSuccess_prepared_noticeTaskProvenance
    {work before occurrence result}
    (prior : ∀ event ∈ before, event.MatchesWork work)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (incoming : TaskNode)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      prepared.GroupMembershipSound ∧ prepared.RegisteredTasksMatch work := by
  obtain ⟨sound, registered⟩ := State.replay_noticeTaskProvenance
    (createWorkQueue_groupMembershipSound _) (createWorkQueue_fromSpec_registeredTasksMatch work)
    before prior
  intro current stored prepared
  have storedSound : stored.GroupMembershipSound := sound
  have storedRegistered : stored.RegisteredTasksMatch work := registered
  refine ⟨storedSound.maybeIntegrateWork result.work (some occurrence),
    storedRegistered.maybeIntegrateWork result.work ?_ (some occurrence)⟩
  intro task member
  obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
  exact ⟨⟨address, payload, some occurrence, same, known⟩,
    matching.childTask_groupsExact member⟩

/-- The successful input's actual activation boundary supplies task metadata to its drain.
Witness: prepare the matched work, retain metadata through the complete owner fold, then
activate its accumulated child work without changing membership provenance.
-/
theorem createWorkQueue_taskSuccess_drain_noticeTaskProvenance
    {work before occurrence result}
    (prior : ∀ event ∈ before, event.MatchesWork work)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (incoming : TaskNode)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := released.1.startNewWork released.2.2
      active.GroupMembershipSound ∧ active.RegisteredTasksMatch work := by
  obtain ⟨sound, registered⟩ :=
    createWorkQueue_taskSuccess_prepared_noticeTaskProvenance prior matching incoming
  obtain ⟨foldedSound, foldedRegistered⟩ :=
    State.successGroupFold_noticeTaskProvenance sound registered incoming.task.groups
  exact ⟨foldedSound.startNewWork _, foldedRegistered.startNewWork _⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
