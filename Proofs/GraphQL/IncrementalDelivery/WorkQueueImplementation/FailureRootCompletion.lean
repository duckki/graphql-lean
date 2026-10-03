import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedRootCompletion

/-! Failure-owner processing closes, rather than silently cancels, every removed active root. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Both active failure removal and latent error retention preserve announced-root accounting
-----------------------------------------------------------------------------------------

/-- One failed-owner step preserves the structural frame and exact notice tracking.
Witness: active cleanup closes its only removed announced ref; latent caching changes no
root or descriptor and leaves earlier tracking untouched.
-/
theorem RootClosureFrame.failureGroupStep_groupNoticeCompletion
    {acc : State × List WorkQueueEvent} {work parents initial}
    (frame : RootClosureFrame acc.1 work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (tracked : GroupNoticeCompletion initial acc) (errors : Nat)
    (group : Execution.DeliveryNode)
    : RootClosureFrame (failureGroupStep errors acc group).1 work parents
      ∧ GroupNoticeCompletion initial (failureGroupStep errors acc group) := by
  obtain ⟨queue, outputs⟩ := acc
  unfold failureGroupStep
  dsimp only
  split
  · exact ⟨frame, tracked⟩
  · rename_i node found
    split
    · rename_i active
      have activeRef : node.group.node.ref ∈ queue.rootGroups := by
        rw [State.groupNode?_ref found]
        exact List.contains_iff_mem.mp active
      exact ⟨frame.removeGroup _, tracked.append
        (frame.finishGroupFailure_groupNoticeCompletion generated canonical node errors
          activeRef)⟩
    · let updated : GroupNode := {
        node with
        pending := node.pending - 1
        failure := some (node.failure.getD 0 + errors)
      }
      have member := List.mem_of_find?_eq_some found
      exact ⟨⟨frame.records.putGroupNode updated (frame.records node member),
        frame.links.putGroupNode updated (frame.links node member),
        frame.roots.mono (fun _ included => included)
          (fun _ retired => retired.putGroupNode updated), frame.support⟩, tracked⟩

/-- The full failed-owner pass cannot silently remove any previously announced group.
Witness: iterate the exact single-pass handler with the preserved structural frame.
No source ordering, distinct-owner, or successful-output premise is required locally.
-/
theorem RootClosureFrame.failureGroupFold_groupNoticeCompletion {queue work parents}
    (frame : RootClosureFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (errors : Nat) (groups : List Execution.DeliveryNode)
    : GroupNoticeCompletion queue.rootGroups
        (groups.foldl (failureGroupStep errors) (queue, [])) := by
  have loop (remaining : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (current : RootClosureFrame acc.1 work parents)
      (tracked : GroupNoticeCompletion queue.rootGroups acc)
      : GroupNoticeCompletion queue.rootGroups
          (remaining.foldl (failureGroupStep errors) acc) := by
    induction remaining generalizing acc with
    | nil => exact tracked
    | cons group rest ih =>
        obtain ⟨next, tracked⟩ := current.failureGroupStep_groupNoticeCompletion
          generated canonical tracked errors group
        exact ih _ next tracked
  exact loop groups (queue, []) frame (.silent (List.Subset.refl _))

/-- Task-failure handling completes every announced root it removes.
Witness: ignored settlements keep roots; accepted settlements remove task memberships,
then the exact owner pass closes its only removable announced refs.
-/
theorem RootClosureFrame.taskFailure_groupNoticeCompletion {queue work parents}
    (frame : RootClosureFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (errors : Nat)
    : GroupNoticeCompletion queue.rootGroups (queue.taskFailure occurrence errors) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskFailure, found]
      exact .silent (List.Subset.refl _)
  | some incoming =>
      rw [queue.taskFailure_eq occurrence errors incoming found]
      split
      · exact .silent (List.Subset.refl _)
      · exact (frame.removeTask occurrence).failureGroupFold_groupNoticeCompletion
          generated canonical errors incoming.task.groups

-----------------------------------------------------------------------------------------
-- Actual matching replay derives this frame without assuming output admission
-----------------------------------------------------------------------------------------

/-- Matching eventwise replay preserves canonical child links.
Witness: fold the existing individual-handler preservation theorem.
-/
theorem State.ChildLinksCanonical.replayGraphEvents {queue : State} {work parents}
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.replayGraphEvents events).ChildLinksCanonical parents := by
  induction events generalizing queue with
  | nil => exact links
  | cons event rest ih =>
      exact ih (links.handleGraphEvent event (matching event List.mem_cons_self) canonical)
        (fun _ member => matching _ (List.mem_cons_of_mem _ member))

/-- Generated matching replay supplies the complete root-closure frame.
Witness: generated canonical ancestry, actual notice metadata, and independently proved
retirement preservation. Failure licensing and already-admitted outputs are not premises.
-/
theorem ExecutedWork.replay_rootClosureFrame {work before}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    : ∃ parents,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ RootClosureFrame
            ((State.initialize (Work.fromExecution work)).replayGraphEvents before) work
            parents := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  obtain ⟨_, records, support⟩ := generated.replay_noticeMetadata matching
  have links := createWorkQueue_childLinksCanonical (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical Located.root canonical member)
  exact ⟨parents, canonical, records, links.replayGraphEvents canonical before matching,
    (generated.replayGraphEvents_structuralRetirement before matching).1, support.roots⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
