import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRootCompletion

/-! Announced-group completion through cache-aware startup and successful draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def startupControls (failures : List GroupFailureEvent) : List WorkQueueEvent :=
  failures.map (fun failure => .groupFailure failure.group failure.errors)

private theorem startupControls_noticeRefs (failures : List GroupFailureEvent)
    : (startupControls failures).flatMap rawGroupNoticeRefs = [] := by
  induction failures with
  | nil => rfl
  | cons failure rest ih => simpa only [startupControls, List.map_cons,
      List.flatMap_cons, rawGroupNoticeRefs, List.nil_append] using ih

private abbrev StartupGroupCompletion (initial : NodeRefs)
    (result : State × List WorkQueueEvent × List GroupFailureEvent)
    : Prop :=
  GroupNoticeCompletion initial (result.1, result.2.1 ++ startupControls result.2.2)

private theorem StartupGroupCompletion.append {initial first second}
    (left : StartupGroupCompletion initial first)
    (right : StartupGroupCompletion first.1.rootGroups second)
    : StartupGroupCompletion initial
        (second.1, first.2.1 ++ second.2.1, first.2.2 ++ second.2.2) := by
  have combined := GroupNoticeCompletion.append left right
  apply combined.perm
  simpa only [startupControls, List.map_append, List.append_assoc]
    using (List.perm_append_comm_assoc (startupControls first.2.2)
            second.2.1 (startupControls second.2.2)).append_left
      first.2.1

/-- Successful release and cache-aware activation complete every removed announced root.
Newly failed children use their own queued controls; the successful parent uses its
immediate closure. No active or newly announced root is discharged by silent cancellation.
-/
theorem LiveRootFrame.finishGroupSuccess_groupNoticeCompletion {queue work parents}
    (frame : LiveRootFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {node : GroupNode} (found : queue.groupNode? node.group.node.ref = some node)
    (active : node.group.node.ref ∈ queue.rootGroups)
    (available : List (Occurrence × Nat) := [])
    : let result := queue.finishGroupSuccess node
      StartupGroupCompletion queue.rootGroups
        (
          (result.1.startNewWork result.2.2 available).1,
          result.2.1,
          (result.1.startNewWork result.2.2 available).2
        ) := by
  intro result
  have closed := frame.finishGroupSuccess_unactivated generated canonical found active
  have protection := queue.finishGroupSuccess_ancestorsRetired generated frame.records
    frame.links canonical frame.registered (List.mem_of_find?_eq_some found)
    (frame.roots _ active)
  have support := frame.support.finishGroupSuccess node
  have queued := closed.rootClosureFrame.startNewWork_groupNoticeCompletion
    closed.support generated canonical result.2.2 protection.2.2 support.2 available
  intro ref member
  have mentioned : ref ∈ queue.rootGroups ++ result.2.1.flatMap rawGroupNoticeRefs := by
    simpa only [List.flatMap_append, startupControls_noticeRefs, List.append_nil]
      using member
  have activated (member : ref ∈ result.1.rootGroups
      ++ result.2.2.newGroups.map Execution.DeliveryNode.ref) :=
    (queued ref (List.mem_append_left _ member)).imp_right
      (List.mem_append_right (result.2.1.flatMap rawGroupClosureRefs))
  rw [List.flatMap_append]
  rcases List.mem_append.mp mentioned with old | noticed
  · rcases queue.finishGroupSuccess_tracks_roots node ref old with retained | completed
    · exact activated (List.mem_append_left _ retained)
    · exact .inr (List.mem_append_left _ completed)
  · exact activated (List.mem_append_right _
      ((queue.finishGroupSuccess_groupNotices node).symm ▸ noticed))

/-- Every actual drain prefix retains announced groups or their own completion controls.
The proof follows successful ready closures and immediate failed child startup, retaining
both output channels until the enclosing batch forwards queued failures.
-/
theorem LiveRootFrame.drainReadyGroups_go_groupNoticeCompletion {queue work parents}
    (frame : LiveRootFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (fuel : Nat) (available : List (Occurrence × Nat) := [])
    : StartupGroupCompletion queue.rootGroups
        (State.drainReadyGroups.go available fuel queue) := by
  induction fuel generalizing queue with
  | zero => exact .silent (List.Subset.refl _)
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact .silent (List.Subset.refl _)
      · rename_i node selected
        obtain ⟨ref, active, choice⟩ := List.exists_of_findSome?_eq_some selected
        cases found : queue.groupNode? ref with
        | none => simp [found] at choice
        | some candidate =>
            simp only [found] at choice
            change (if candidate.pending == 0 then some candidate else none) = some node at choice
            split at choice
            · cases Option.some.inj choice
              have same := State.groupNode?_ref found
              exact (frame.finishGroupSuccess_groupNoticeCompletion generated canonical
                (same ▸ found) (same ▸ active) available).append
                  (ih (frame.finishGroupSuccess generated canonical
                    (same ▸ found) (same ▸ active) available))
            · contradiction

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
