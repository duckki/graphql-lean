import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPruningNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage

/-! Carried group notices refer to the permanent registry at their actual handler boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful flushing and recursive draining introduce no registrations
-----------------------------------------------------------------------------------------

/-- Each group announced by this raw event belongs to the supplied permanent registry. -/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.GroupNoticesRegistered
    (registered : NodeRefs) : WorkQueueEvent → Prop
  | .groupSuccess _ groups _ | .streamValues _ _ groups _ =>
      ∀ group ∈ groups, group.ref ∈ registered
  | _ => True

/-- Notice registration survives extension of the permanent registry.
Witness: only the carried group refs are inspected; the event itself is unchanged.
-/
theorem
    _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.GroupNoticesRegistered.mono
    {before after : NodeRefs} {event : WorkQueueEvent}
    (known : event.GroupNoticesRegistered before) (included : before.Subset after)
    : event.GroupNoticesRegistered after := by
  cases event <;> try trivial
  all_goals exact fun group member => included (known group member)

/-- Every group released by a successful flush was already permanently registered.
Witness: flushing retains live refs, closing only filters them, and promoted descendants
come from live lookups. The pruning traversal cannot invent an unregistered descriptor.
-/
theorem State.finishGroupSuccess_released_registered {queue : State}
    (live : queue.LiveGroupsRegistered) (group : GroupNode)
    : ∀ child ∈ (queue.finishGroupSuccess group).2.2.newGroups,
        child.ref ∈ queue.registeredGroups := by
  have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      (known : ∀ node ∈ acc.1.groupNodes, node.group.node.ref ∈ queue.registeredGroups)
      : ∀ node ∈ (tasks.foldl flushGroupTask acc).1.groupNodes,
          node.group.node.ref ∈ queue.registeredGroups := by
    induction tasks generalizing acc with
    | nil => exact known
    | cons occurrence rest ih =>
        simp only [List.foldl_cons, flushGroupTask]
        split
        · exact ih acc known
        · apply ih
          intro node member
          obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
          subst node
          exact known old oldMember
  let flushed := group.tasks.foldl flushGroupTask (queue, [], [])
  have flushedKnown := loop group.tasks (queue, [], []) live
  let current : State := { flushed.1 with
    groupNodes := flushed.1.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := flushed.1.rootGroups.filter (· != group.group.node.ref) }
  let children := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  have records : ∀ node ∈ current.groupNodes, node.group.node.ref ∈ queue.registeredGroups :=
    fun node member => flushedKnown node (List.mem_filter.mp member).1
  change ∀ child ∈ (current.pruneEmptyGroups children).2, child.ref ∈ queue.registeredGroups
  apply current.pruneEmptyGroups_noticeProperty
    (property := fun child => child.ref ∈ queue.registeredGroups) records children
  intro child member
  obtain ⟨ref, _, selected⟩ := List.mem_filterMap.mp member
  cases found : current.groupNode? ref with
  | none => simp [found] at selected
  | some node =>
      have same : node.group.node = child := by simpa [found] using selected
      exact same ▸ records node (List.mem_of_find?_eq_some found)

/-- A successful flush's emitted notices use only previously registered group refs.
Witness: its optional value block has no notices; its closure copies the release list.
-/
theorem State.finishGroupSuccess_groupNoticesRegistered {queue : State}
    (live : queue.LiveGroupsRegistered) (group : GroupNode)
    : ∀ event ∈ (queue.finishGroupSuccess group).2.1,
        event.GroupNoticesRegistered queue.registeredGroups := by
  obtain ⟨values, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications group
  intro event member
  rw [output] at member
  rcases List.mem_append.mp member with first | last
  · split at first
    · cases first
    · obtain rfl := List.mem_singleton.mp first
      trivial
  · obtain rfl := List.mem_singleton.mp last
    exact queue.finishGroupSuccess_released_registered live group

/-- Every notice emitted by a bounded drain uses the drain-entry registry.
Witness: success releases registered children and retains registration coverage; failure
only removes live records. Child activation and every later iteration keep that registry.
-/
theorem State.drainReadyGroups_go_groupNoticesRegistered {queue : State}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered) (fuel : Nat)
    : ∀ event ∈ (State.drainReadyGroups.go fuel queue).2,
        event.GroupNoticesRegistered queue.registeredGroups := by
  induction fuel generalizing queue with
  | zero => simp [State.drainReadyGroups.go]
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · simp
      · rename_i node selected
        cases failed : node.failure with
        | none =>
            have closed := queue.finishGroupSuccess_registration live tasks node
            have active := State.startNewWork_registration closed.1 closed.2.1
              (queue.finishGroupSuccess node).2.2
            have later := ih active.1 active.2
            rw [State.startNewWork_registeredGroups, closed.2.2] at later
            intro event member
            exact (List.mem_append.mp member).elim
              (queue.finishGroupSuccess_groupNoticesRegistered live node event) (later event)
        | some errors =>
            have later := ih (queue := queue.removeGroup node.group.node.ref)
              (fun record member => live record (List.mem_filter.mp member).1) tasks
            intro event member
            rcases List.mem_append.mp member with first | rest
            · obtain rfl := List.mem_singleton.mp first
              trivial
            · exact later event rest

-----------------------------------------------------------------------------------------
-- The single-pass owner fold shares the same permanent registry
-----------------------------------------------------------------------------------------

/-- An owner fold retains registration coverage and emits only registered group notices.
Witness: counter decrements preserve refs, each successful flush retains its registry,
and the actual fold carries earlier notices without changing their registration evidence.
-/
theorem State.successGroupFold_groupNoticesRegistered {queue : State}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (groups : List Execution.DeliveryNode)
    : let result := groups.foldl successGroupStep (queue, [], {})
      result.1.LiveGroupsRegistered
      ∧ result.1.TaskGroupsRegistered
      ∧ result.1.registeredGroups = queue.registeredGroups
      ∧ ∀ event ∈ result.2.1, event.GroupNoticesRegistered queue.registeredGroups := by
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (covered : acc.1.LiveGroupsRegistered) (taskCoverage : acc.1.TaskGroupsRegistered)
      (same : acc.1.registeredGroups = queue.registeredGroups)
      (notices : ∀ event ∈ acc.2.1, event.GroupNoticesRegistered queue.registeredGroups)
      : let result := more.foldl successGroupStep acc
        result.1.LiveGroupsRegistered ∧ result.1.TaskGroupsRegistered
        ∧ result.1.registeredGroups = queue.registeredGroups
        ∧ ∀ event ∈ result.2.1, event.GroupNoticesRegistered queue.registeredGroups := by
    induction more generalizing acc with
    | nil => exact ⟨covered, taskCoverage, same, notices⟩
    | cons group rest ih =>
        simp only [List.foldl_cons, successGroupStep]
        split
        · exact ih acc covered taskCoverage same notices
        · rename_i node found
          let updated := { node with pending := node.pending - 1 }
          have next : (acc.1.putGroupNode updated).LiveGroupsRegistered :=
            covered.putGroupNode updated (covered node (List.mem_of_find?_eq_some found))
          split
          · have closed := State.finishGroupSuccess_registration next taskCoverage updated
            have emitted := State.finishGroupSuccess_groupNoticesRegistered next updated
            exact ih _ closed.1 closed.2.1 (closed.2.2.trans same)
              (fun event member => (List.mem_append.mp member).elim (notices event)
                (fun newMember => same ▸ emitted event newMember))
          · exact ih _ next taskCoverage same notices
  exact loop groups (queue, [], {}) live tasks rfl (by simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
