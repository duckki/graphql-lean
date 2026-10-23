import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupInvalidation

/-! Cancellation history during group registration, independent of host-source laws. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration retains cancellation refs without confusing successful retirement
-----------------------------------------------------------------------------------------

/-- Registration retains every earlier cancellation ref.
Witness: all branches either retain the list or append the refused child's ref. -/
theorem State.addGroup_cancelledGroups_subset (queue : State) (group : Group)
    : queue.cancelledGroups.Subset (queue.addGroup group).cancelledGroups := by
  unfold State.addGroup
  split
  · exact List.Subset.refl _
  · split
    · exact List.Subset.refl _
    · split
      · split
        · exact List.subset_append_left _ _
        · exact List.Subset.refl _
      · exact List.Subset.refl _

/-- A registration fold retains every earlier cancellation ref.
Witness: induction composes the single-registration inclusions. -/
theorem State.foldAddGroup_cancelledGroups_subset (queue : State) (groups : List Group)
    : queue.cancelledGroups.Subset
        (groups.foldl State.addGroup queue).cancelledGroups := by
  induction groups generalizing queue with
  | nil => exact List.Subset.refl _
  | cons group rest ih =>
      exact (queue.addGroup_cancelledGroups_subset group).trans (ih _)

/-- A recursive registration batch retains every prior cancellation ref. -/
theorem State.addGroups_cancelledGroups_subset (queue : State) (groups : List Group)
    : queue.cancelledGroups.Subset (queue.addGroups groups).1.cancelledGroups := by
  exact State.addGroups_preserves (fun current => queue.cancelledGroups ⊆ current.cancelledGroups)
    groups (fun current group _ earlier =>
      earlier.trans (current.addGroup_cancelledGroups_subset group)) queue (List.Subset.refl _)

/-- Registration cannot introduce cancellation without an earlier cancelled parent.
Witness: an empty history makes the parent's membership check false. -/
theorem State.addGroup_cancelledGroups_empty {queue : State}
    (empty : queue.cancelledGroups = []) (group : Group)
    : (queue.addGroup group).cancelledGroups = [] := by
  unfold State.addGroup
  split
  · exact empty
  · split
    · exact empty
    · split
      · simp [empty]
      · exact empty

/-- Even arbitrary candidate order cannot create a first cancellation during integration.
Witness: the registration fold preserves emptiness and parent linking changes no refs. -/
theorem State.addGroups_cancelledGroups_empty {queue : State}
    (empty : queue.cancelledGroups = []) (groups : List Group)
    : (queue.addGroups groups).1.cancelledGroups = [] := by
  exact State.addGroups_preserves (fun current => current.cancelledGroups = []) groups
    (fun _ group _ valid => State.addGroup_cancelledGroups_empty valid group) queue empty

/-- A fresh child of a cancelled parent is immediately retired and remembered.
Witness: the refused-registration branch records both refs and creates no live node. -/
theorem State.addGroup_retired_of_cancelled_parent {queue : State} {group : Group}
    (fresh : group.node.ref ∉ queue.registeredGroups)
    (absent : queue.groupNode? group.node.ref = none) {parent : Nat}
    (parentEq : group.parent = some parent)
    (parentAbsent : queue.groupNode? parent = none)
    (cancelled : parent ∈ queue.cancelledGroups)
    : (queue.addGroup group).RetiredGroup group.node.ref
      ∧ group.node.ref ∈ (queue.addGroup group).cancelledGroups := by
  have missing : group.node.ref ∉ queue.groupNodes.map (fun node => node.group.node.ref) := by
    rintro member
    obtain ⟨node, member, same⟩ := List.mem_map.mp member
    exact List.find?_eq_none.mp absent node member (beq_iff_eq.mpr same)
  simpa [State.addGroup, fresh, absent, parentEq, parentAbsent, cancelled,
    State.RetiredGroup]
    using missing

/-- A refused late child stays absent through any later queue/publisher replay.
Witness: refused registration establishes permanent retirement; arbitrary replay preserves it.
-/
theorem State.addGroup_cancelled_child_never_recreated {queue : State} {group : Group}
    (fresh : group.node.ref ∉ queue.registeredGroups)
    (absent : queue.groupNode? group.node.ref = none) {parent : Nat}
    (parentEq : group.parent = some parent)
    (parentAbsent : queue.groupNode? parent = none)
    (cancelled : parent ∈ queue.cancelledGroups) (batches : List (List GraphEvent))
    : ((queue.addGroup group).runNormalized batches).1.groupNode? group.node.ref
      = none := by
  have retired := State.addGroup_retired_of_cancelled_parent fresh absent parentEq parentAbsent cancelled
  exact retired.1.never_recreated batches

-----------------------------------------------------------------------------------------
-- Refused children inherit a real causal invalidation witness
-----------------------------------------------------------------------------------------

/-- Each retained cancellation ref is invalidated by the recorded failed occurrences.
This is internal replay evidence, not a restriction on the host event source. -/
def State.CancelledGroupsSupported (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  ∀ ref ∈ queue.cancelledGroups, GroupInvalidated work failed ref

/-- A causally healthy ref cannot occur in supported cancellation history.
Witness: membership would provide the contradictory invalidation witness. -/
theorem State.CancelledGroupsSupported.healthy_not_mem {queue work failed ref}
    (supported : State.CancelledGroupsSupported queue work failed)
    (healthy : ¬GroupInvalidated work failed ref)
    : ref ∉ queue.cancelledGroups :=
  fun member => healthy (supported ref member)

/-- Registering a structurally matched child preserves cancellation provenance.
Witness: a refused child's immediate parent is an invalidated dependency. -/
theorem State.CancelledGroupsSupported.addGroup {queue work failed}
    (supported : State.CancelledGroupsSupported queue work failed) (group : Group)
    (matching
      : ∃ dependencies producer,
          NodeAt work group.node .group dependencies producer
          ∧ group.parent = dependencies.head?)
    : (queue.addGroup group).CancelledGroupsSupported work failed := by
  unfold State.addGroup
  split
  · exact supported
  · split
    · exact supported
    · rename_i parent parentEq
      split
      · split
        · rename_i blocked
          intro ref member
          rcases List.mem_append.mp member with old | new
          · exact supported ref old
          · obtain rfl := List.mem_singleton.mp new
            obtain ⟨dependencies, producer, known, canonical⟩ := matching
            have cancelled : parent ∈ queue.cancelledGroups := by simpa using blocked
            exact .groupDependency ⟨group.node, producer, known, rfl⟩
              (List.mem_of_head? (canonical.symm.trans parentEq)) (supported _ cancelled)
        · exact supported
      · exact supported

/-- A registration batch preserves cancellation provenance in any candidate order.
Witness: every newly retained ref inherits invalidation from its immediate parent. -/
theorem State.CancelledGroupsSupported.addGroups {queue work failed}
    (supported : State.CancelledGroupsSupported queue work failed) (groups : List Group)
    (matching
      : ∀ group ∈ groups,
          ∃ dependencies producer,
            NodeAt work group.node .group dependencies producer
            ∧ group.parent = dependencies.head?)
    : (queue.addGroups groups).1.CancelledGroupsSupported work failed := by
  exact State.addGroups_preserves (fun current => current.CancelledGroupsSupported work failed)
    groups (fun _ group member valid => valid.addGroup group (matching group member)) queue supported

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
