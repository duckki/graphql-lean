import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulGroupHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainClosureBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.LiveRegistration

/-! Joint source-independent health evidence through registration and rejection draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ReleaseHealth

/-- Independent metadata, rejection retention, membership, and historical health facts.
These certificates describe the existing queue; no output-admission rule is assumed.
-/
structure HealthFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (failed : List Occurrence)
    : Prop where
  groups : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  counts : queue.RetainedFailures work failed
  retired : queue.UncancelledRetiredHealthy work failed
  roots : queue.RootAncestorsHealthy work failed
  refs : queue.GroupRefsUnique
  sound : queue.GroupMembershipSound
  tasks : queue.RegisteredTasksMatch work
  live : queue.LiveGroupsRegistered

/-- Matching registration preserves the frame, leaving the active root set unchanged. -/
theorem HealthFrame.maybeIntegrateWork {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (newWork : Work)
    (known
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (parentLinks
      : ∀ group ∈ newWork.groups, group.parent = (parents group.node.ref).head?)
    (children : ∀ task ∈ newWork.tasks, TaskMatches work task)
    (producer : Option Occurrence := none)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (closed
      : ∀ group ∈ newWork.groups,
          ∀ parent,
            group.parent = some parent
            → parent
              ∈ queue.registeredGroups
                ++ newWork.groups.map (fun group => group.node.ref))
    : HealthFrame (queue.maybeIntegrateWork newWork producer).1 work parents failed := by
  refine ⟨
    prior.groups.maybeIntegrateWork newWork known producer,
    prior.links.maybeIntegrateWork newWork parentLinks producer,
    prior.counts.maybeIntegrateWork prior.refs newWork producer,
    prior.retired.maybeIntegrateWork newWork producer prior.counts generated prior.live
      (by
        intro group member
        obtain ⟨dependencies, record⟩ := known group member
        exact ⟨
          dependencies,
          record,
          by rw [canonical _ _ record]; exact parentLinks group member
        ⟩)
      closed,
    ?_,
    prior.refs.maybeIntegrateWork newWork producer,
    prior.sound.maybeIntegrateWork newWork producer,
    prior.tasks.maybeIntegrateWork newWork children producer,
    prior.live.maybeIntegrateWork newWork producer
  ⟩
  intro ref active
  rw [State.maybeIntegrateWork_rootGroups] at active
  exact prior.roots ref active

/-- Activation preserves the frame when released groups have healthy ancestors. -/
theorem HealthFrame.startNewWork {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (released : NewWork)
    (healthy : ∀ group ∈ released.newGroups, GroupAncestorsHealthy work failed group.ref)
    (available : List (Occurrence × Nat) := [])
    : HealthFrame (queue.startNewWork released available).1 work parents failed :=
  ⟨
    prior.groups.startNewWork released available,
    prior.links.startNewWork released available,
    prior.counts.startNewWork released available,
    prior.retired.startNewWork released available,
    prior.roots.startNewWork released healthy available,
    prior.refs.startNewWork released available,
    prior.sound.startNewWork released available,
    prior.tasks.startNewWork released available,
    prior.live.startNewWork released available
  ⟩

/-- Flushing nonfailed memberships preserves the frame and proves its release ancestry. -/
theorem HealthFrame.finishGroupSuccess {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {node : GroupNode} (member : node ∈ queue.groupNodes)
    (active : node.group.node.ref ∈ queue.rootGroups)
    (notFailed : ∀ occurrence ∈ node.tasks, occurrence ∉ failed)
    : HealthFrame (queue.finishGroupSuccess node).1 work parents failed
      ∧ (∀ child ∈ (queue.finishGroupSuccess node).2.2.newGroups,
          GroupAncestorsHealthy work failed child.ref)
      ∧ SuccessfulGroupsHealthy work failed (queue.finishGroupSuccess node).2.1 := by
  have closed := prior.retired.finishGroupSuccess generated prior.groups prior.links
    canonical prior.counts failedKnown member notFailed (prior.roots _ active)
  obtain ⟨dependencies, known⟩ := prior.groups node member
  exact ⟨⟨prior.groups.finishGroupSuccess node, prior.links.finishGroupSuccess node,
    prior.counts.finishGroupSuccess node notFailed, closed.1,
    fun ref included => prior.roots ref (queue.finishGroupSuccess_rootsSubset node included),
    prior.refs.finishGroupSuccess node, prior.sound.finishGroupSuccess node,
    prior.tasks.finishGroupSuccess node, prior.live.finishGroupSuccess node⟩, closed.2,
    queue.finishGroupSuccess_successfulGroupsHealthy generated prior.counts
      failedKnown member known notFailed (prior.roots _ active)⟩

/-- Rejection replay preserves the fixed historical frame. -/
theorem HealthFrame.taskFailure {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (occurrence : Occurrence)
    (errors : Nat)
    : HealthFrame (queue.taskFailure occurrence errors).1 work parents failed :=
  ⟨
    prior.groups.taskFailure occurrence errors,
    prior.links.taskFailure occurrence errors,
    prior.counts.taskFailure_preserves occurrence errors,
    prior.retired.taskFailure_preserves occurrence errors,
    fun ref included =>
      prior.roots ref (queue.taskFailure_rootsSubset occurrence errors included),
    prior.refs.taskFailure occurrence errors,
    prior.sound.taskFailure occurrence errors,
    prior.tasks.taskFailure occurrence errors,
    prior.live.taskFailure occurrence errors
  ⟩

/-- A ready drain preserves the independently supplied successful-settlement bound. -/
private theorem pendingBound_drainReadyGroups_go {queue : State} {settled}
    (bounded : queue.PendingBound (fun _ => True) settled) (fuel : Nat)
    (available : List (Occurrence × Nat))
    : (State.drainReadyGroups.go available fuel queue).1.PendingBound (fun _ => True)
        settled :=
  State.drainReadyGroups_go_preserves
    (fun current =>
      current.PendingBound (fun _ => True) settled)
    (fun _ node prior member _ zero =>
      (prior.finishGroupSuccess node (prior.allSettled member trivial zero)).startNewWork
        _ available)
    bounded fuel

/-- Every bounded drain preserves the frame.
Witness: zero pending debt names only successful settlements. Startup removal marks
failed retirements cancelled and preserves health of surviving roots.
-/
theorem HealthFrame.drainReadyGroups_frame {queue work parents failed settled}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (fuel : Nat) (bounded : queue.PendingBound (fun _ => True) settled)
    (disjoint : ∀ occurrence ∈ settled, occurrence ∉ failed)
    (available : List (Occurrence × Nat) := [])
    : HealthFrame (State.drainReadyGroups.go available fuel queue).1 work parents
        failed := by
  let invariant (current : State) := HealthFrame current work parents failed
    ∧ current.PendingBound (fun _ => True) settled
  have result := State.drainReadyGroups_go_preserves invariant (available := available)
    (fun current node valid member active zero => by
      have all := valid.2.allSettled member trivial zero
      have safe := fun occurrence member => disjoint occurrence (all occurrence member)
      have closed := valid.1.finishGroupSuccess generated canonical failedKnown member active safe
      exact ⟨closed.1.startNewWork _ closed.2.1 available,
        (valid.2.finishGroupSuccess node all).startNewWork _ available⟩)
    (show invariant queue from ⟨prior, bounded⟩) fuel
  exact result.1

/-- Successful carriers in every bounded drain are healthy at their actual closure cut. -/
theorem HealthFrame.drainReadyGroups_go {queue work parents failed settled}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (fuel : Nat) (bounded : queue.PendingBound (fun _ => True) settled)
    (disjoint : ∀ occurrence ∈ settled, occurrence ∉ failed)
    (available : List (Occurrence × Nat) := [])
    : HealthFrame (State.drainReadyGroups.go available fuel queue).1 work parents failed
      ∧ SuccessfulGroupsHealthy work failed
          (State.drainReadyGroups.go available fuel queue).2.1 := by
  refine ⟨prior.drainReadyGroups_frame generated canonical failedKnown fuel bounded disjoint
    available, ?_⟩
  intro group groups streams member
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨steps, node, before, _, found, active, zero, _, output, _⟩ :=
    State.drainReadyGroups_go_success_boundary fuel queue available selected
  have frame := prior.drainReadyGroups_frame generated canonical failedKnown steps bounded
    disjoint available
  have live := List.mem_of_find?_eq_some found
  have pending := pendingBound_drainReadyGroups_go bounded steps available
  have all := pending.allSettled live trivial zero
  have safe := fun occurrence member => disjoint occurrence (all occurrence member)
  have closed := frame.finishGroupSuccess generated canonical failedKnown live active safe
  apply closed.2.2 group groups streams
  rw [output]
  exact List.mem_append_right _ List.mem_cons_self

/-- The full drain instantiates its actual live-record budget. -/
theorem HealthFrame.drainReadyGroups {queue work parents failed settled}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (disjoint : ∀ occurrence ∈ settled, occurrence ∉ failed)
    (available : List (Occurrence × Nat) := [])
    : HealthFrame (queue.drainReadyGroups available).1 work parents failed
      ∧ SuccessfulGroupsHealthy work failed (queue.drainReadyGroups available).2.1 :=
  prior.drainReadyGroups_go generated canonical failedKnown queue.groupNodes.length
    bounded disjoint available

/-- Every drain notice retains healthy ancestry at its actual emission cut. -/
theorem HealthFrame.drainReadyGroups_noticeHealth {queue work parents failed settled}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (disjoint : ∀ occurrence ∈ settled, occurrence ∉ failed)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeAncestorsHealthy work failed (queue.drainReadyGroups available).2.1 := by
  intro ref member
  obtain ⟨event, included, noticed⟩ := List.mem_flatMap.mp member
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp included
  cases event with
  | groupSuccess group groups streams =>
      obtain ⟨steps, node, before, _, found, active, zero, _, output, _⟩ :=
        State.drainReadyGroups_go_success_boundary queue.groupNodes.length queue available selected
      have frame := prior.drainReadyGroups_frame generated canonical failedKnown steps bounded
        disjoint available
      have live := List.mem_of_find?_eq_some found
      have pending := pendingBound_drainReadyGroups_go bounded steps available
      have all := pending.allSettled live trivial zero
      have safe := fun occurrence member => disjoint occurrence (all occurrence member)
      have released := frame.finishGroupSuccess generated canonical failedKnown live active safe
      apply State.finishGroupSuccess_noticeAncestorHealth released.2.1 ref
      rw [output, List.flatMap_append]
      exact List.mem_append_right _ (List.mem_append_left _ noticed)
  | streamValues stream values groups streams =>
      exact False.elim (queue.drainReadyGroups_noStreamValues stream values groups streams available
        (List.mem_of_getElem? selected))
  | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases noticed

end ReleaseHealth
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
