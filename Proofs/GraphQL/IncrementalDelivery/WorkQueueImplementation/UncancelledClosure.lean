import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledStartup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledSettlement

/-! Successful ready closure preserves ancestor markers under early cached-failure startup. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Source-derived frames needed to close and activate one successful ready group. -/
structure ClosureContext (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (settled : List Occurrence)
    : Prop where
  markers : queue.UncancelledRetiredMarkers work
  owners : queue.UncancelledTaskAccounting settled
  parent : ParentCutFrame queue work parents
  roots : RootReplayFrame queue work parents
  tasks : queue.TaskOwnerFrame work
  rejected : queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∉ settled)
  counts : queue.PendingBound (fun _ => True) settled

/-- Successful closure and cached child startup preserve the full source closure frame. -/
theorem ClosureContext.finishStart {queue work parents settled}
    (frame : ClosureContext queue work parents settled) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (node : GroupNode) (member : node ∈ queue.groupNodes)
    (active : node.group.node.ref ∈ queue.rootGroups) (zero : node.pending = 0)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∉ settled)
    : let closed := queue.finishGroupSuccess node
      ClosureContext (closed.1.startNewWork closed.2.2 available).1 work parents
        settled := by
  let closed := queue.finishGroupSuccess node
  have all := frame.counts.allSettled member trivial zero
  have owners := frame.owners.finishSettledGroupSuccess frame.parent.keys node member all
  have parent := frame.parent.finishGroupSuccess node
  have tasks := frame.tasks.finishGroupSuccess node member
  have retired := frame.roots.retired.finishGroupSuccess generated frame.parent.records
    frame.parent.links canonical frame.parent.live member (frame.roots.live.roots _ active)
  have markers := frame.markers.finishGroupSuccess frame.parent.safe frame.parent.fields
    frame.parent.closed frame.parent.live canonical node member
  have rejected := frame.rejected.finishGroupSuccess node
  have found := frame.parent.keys.groupNode?_of_mem member
  have roots := frame.roots.live.finishGroupSuccess generated canonical found active available
  exact ⟨markers.startNewWork retired owners generated parent.links parent.records
      tasks.sound tasks.matching canonical rejected closed.2.2 available licensed,
    owners.startNewWork closed.2.2 available,
    parent.startNewWork generated canonical closed.2.2 available,
    ⟨roots, retired.startNewWork closed.2.2 available⟩,
    tasks.startNewWork closed.2.2 available,
    rejected.startNewWork closed.2.2 available licensed,
    (frame.counts.finishGroupSuccess node all).startNewWork closed.2.2 available⟩

/-- Ready draining preserves ancestor-marker closure using consumed successes only.
Witness: each zero counter certifies every flushed task consumed. The selected live
record supplies its ancestor markers before startup handles cached child rejections.
-/
theorem State.UncancelledRetiredMarkers.drainReadyGroups {queue : State}
    {work parents settled}
    (markers : queue.UncancelledRetiredMarkers work)
    (owners : queue.UncancelledTaskAccounting settled)
    (parent : ParentCutFrame queue work parents)
    (roots : RootReplayFrame queue work parents) (tasks : queue.TaskOwnerFrame work)
    (rejected : queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∉ settled))
    (counts : queue.PendingBound (fun _ => True) settled) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∉ settled)
    : (queue.drainReadyGroups available).1.UncancelledRetiredMarkers work := by
  have result : ClosureContext (queue.drainReadyGroups available).1 work parents settled := by
    apply State.drainReadyGroups_preserves
      (fun current => ClosureContext current work parents settled) (available := available)
      (valid := ⟨markers, owners, parent, roots, tasks, rejected, counts⟩)
    intro current node frame member active zero
    exact frame.finishStart generated canonical node member active zero available licensed
  exact result.markers

/-- A successful contributor fold preserves ancestor markers independently of its debt.
Witness: decrements retain exact parent metadata; every selected live closing record
supplies its ancestor certificate before flushing and empty-shell pruning.
-/
theorem State.UncancelledRetiredMarkers.successGroupFold {queue : State}
    {work parents} (markers : queue.UncancelledRetiredMarkers work)
    (parent : ParentCutFrame queue work parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (groups : List Execution.DeliveryNode)
    : let released := groups.foldl successGroupStep (queue, [], {})
      released.1.UncancelledRetiredMarkers work
      ∧ ParentCutFrame released.1 work parents := by
  let invariant (current : State) := current.UncancelledRetiredMarkers work
    ∧ ParentCutFrame current work parents
  have loop (more : List Execution.DeliveryNode)
      (acc : State × List Execution.WorkQueueEvent × NewWork) (frame : invariant acc.1)
      : invariant (more.foldl successGroupStep acc).1 := by
    induction more generalizing acc with
    | nil => exact frame
    | cons group rest ih =>
        rw [List.foldl_cons]
        apply ih
        unfold successGroupStep
        dsimp only
        split
        · exact frame
        · rename_i node found
          let updated := { node with pending := node.pending - 1 }
          have next := frame.2.putGroupNode found updated rfl rfl
          have markers := frame.1.putGroupNode updated
          split
          · have present : updated ∈ (acc.1.putGroupNode updated).groupNodes :=
              List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found, by simp [updated]⟩
            exact ⟨markers.finishGroupSuccess next.safe next.fields next.closed next.live
              canonical updated present, next.finishGroupSuccess updated⟩
          · exact ⟨markers, next⟩
  exact loop groups (queue, [], {}) ⟨markers, parent⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
