import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalCoverage

/-! Cancelled delivery refs retain their permanent retirement certificates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A cancellation marker names a registered ref with no remaining live group record.
This is proof evidence about the existing registry and cancellation list, not runtime state.
-/
def State.CancellationsRetired (queue : State) : Prop :=
  ∀ ref ∈ queue.cancelledGroups, queue.RetiredGroup ref

/-- A transition with unchanged cancellation history only needs to preserve retirement. -/
theorem State.CancellationsRetired.of_frame {queue next : State}
    (prior : queue.CancellationsRetired)
    (same : next.cancelledGroups = queue.cancelledGroups)
    (retained : ∀ ref, queue.RetiredGroup ref → next.RetiredGroup ref)
    : next.CancellationsRetired := by
  intro ref member
  rw [same] at member
  exact retained ref (prior ref member)

theorem State.CancellationsRetired.putGroupNode {queue : State}
    (prior : queue.CancellationsRetired) (updated : GroupNode)
    : (queue.putGroupNode updated).CancellationsRetired :=
  prior.of_frame rfl (fun _ retired => retired.putGroupNode updated)

theorem State.CancellationsRetired.putTaskNode {queue : State}
    (prior : queue.CancellationsRetired) (updated : TaskNode)
    : (queue.putTaskNode updated).CancellationsRetired :=
  prior

/-- Refused child registration records a new retired ref; old refs cannot be revived. -/
theorem State.CancellationsRetired.addGroup {queue : State}
    (prior : queue.CancellationsRetired) (group : Group)
    : (queue.addGroup group).CancellationsRetired := by
  intro ref member
  by_cases old : ref ∈ queue.cancelledGroups
  · exact (prior ref old).addGroup group
  · unfold State.addGroup at member
    split at member
    · exact (old member).elim
    · rename_i fresh
      have freshness : group.node.ref ∉ queue.registeredGroups
          ∧ queue.groupNode? group.node.ref = none := by simpa using fresh
      cases parentEq : group.parent with
      | none => simp only [parentEq] at member; exact (old member).elim
      | some parent =>
          simp only [parentEq] at member
          cases parentAbsent : queue.groupNode? parent with
          | some node =>
              simp only [parentAbsent, State.putGroupNode] at member
              exact (old member).elim
          | none =>
              simp only [parentAbsent] at member
              split at member
              · rename_i cancelled
                rcases List.mem_append.mp member with earlier | added
                · exact (old earlier).elim
                · cases List.mem_singleton.mp added
                  exact (State.addGroup_retired_of_cancelled_parent freshness.1 freshness.2
                    parentEq parentAbsent (List.contains_iff_mem.mp cancelled)).1
              · exact (old member).elim

theorem State.CancellationsRetired.addGroups {queue : State}
    (prior : queue.CancellationsRetired) (groups : List Group)
    : (queue.addGroups groups).1.CancellationsRetired := by
  exact State.addGroups_preserves State.CancellationsRetired groups
    (fun _ group _ valid => valid.addGroup group) queue prior

theorem State.CancellationsRetired.addTask {queue : State}
    (prior : queue.CancellationsRetired) (task : Task)
    : (queue.addTask task).CancellationsRetired :=
  prior.of_frame (queue.addTask_cancelledGroups task)
    (fun _ retired => retired.addTask task)

theorem State.CancellationsRetired.addStreams {queue : State}
    (prior : queue.CancellationsRetired) (streams : List Stream)
    (producer : Option Occurrence := none)
    : (queue.addStreams streams producer).1.CancellationsRetired :=
  prior.of_frame (queue.addStreams_cancelledGroups streams producer)
    (fun _ retired => retired.addStreams streams producer)

theorem State.CancellationsRetired.maybeIntegrateWork {queue : State}
    (prior : queue.CancellationsRetired) (incoming : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork incoming producer).1.CancellationsRetired := by
  have tasks (more : List Task) (current : State) (known : current.CancellationsRetired)
      : (more.foldl State.addTask current).CancellationsRetired := by
    induction more generalizing current with
    | nil => exact known
    | cons task rest ih => exact ih _ (known.addTask task)
  exact (tasks incoming.tasks _ (prior.addGroups incoming.groups)).addStreams
    incoming.streams producer

theorem State.CancellationsRetired.pruneEmptyGroups {queue : State}
    (prior : queue.CancellationsRetired) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.CancellationsRetired :=
  prior.of_frame (queue.pruneEmptyGroups_cancelledGroups groups)
    (fun _ retired => retired.pruneEmptyGroups groups)

theorem State.CancellationsRetired.cacheTaskFailures {queue : State}
    (prior : queue.CancellationsRetired) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).CancellationsRetired :=
  prior.of_frame (queue.cacheTaskFailures_cancelledGroups available)
    (fun _ retired => retired.cacheTaskFailures available)

/-- Actual subtree removal records only live registered refs and removes all their copies. -/
theorem State.CancellationsRetired.removeGroup {queue : State}
    (prior : queue.CancellationsRetired) (live : queue.LiveGroupsRegistered) (root : Nat)
    : (queue.removeGroup root).CancellationsRetired := by
  let removed := State.removeGroup.collect (queue.groupNodes.length + 1) queue [root] []
  have targetPresent {source target} (path : queue.LiveDescendant source target)
      : ∃ node, queue.groupNode? target = some node := by
    induction path with
    | self found => exact ⟨_, found⟩
    | child _ _ _ ih => exact ih
  intro ref member
  rcases List.mem_append.mp member with earlier | collected
  · exact (prior ref earlier).removeGroup root
  · have known : ref ∈ removed := collected
    obtain impossible | ⟨source, initial, path⟩ :=
      State.removeGroup_collect_provenance _ _ _ _ known
    · cases impossible
    · obtain ⟨node, found⟩ := targetPresent path
      refine ⟨?_, ?_⟩
      · exact (State.groupNode?_ref found) ▸ live node (List.mem_of_find?_eq_some found)
      · intro member
        obtain ⟨node, kept, same⟩ := List.mem_map.mp member
        have retained : (!removed.contains node.group.node.ref) = true :=
          (List.mem_filter.mp kept).2
        have gone : removed.contains node.group.node.ref = true := by
          rw [same]
          exact List.contains_iff_mem.mpr known
        simp only [gone, Bool.not_true, Bool.false_eq_true] at retained

/-- A cancelled ref cannot simultaneously name any live group record. -/
theorem State.CancellationsRetired.live_uncancelled {queue : State}
    (prior : queue.CancellationsRetired) {node : GroupNode}
    (member : node ∈ queue.groupNodes)
    : node.group.node.ref ∉ queue.cancelledGroups := by
  intro cancelled
  exact (prior _ cancelled).2 (List.mem_map_of_mem member)

private theorem State.CancellationsRetired.startTask {queue : State}
    (prior : queue.CancellationsRetired) (occurrence : Occurrence)
    (available : List (Occurrence × Nat))
    : (queue.startTask occurrence available).CancellationsRetired := by
  unfold State.startTask
  split
  · exact prior
  · split <;> exact prior

/-- Cached startup either retains old retirement or records the whole removed subtree. -/
theorem State.CancellationsRetired.startGroup {queue : State}
    (prior : queue.CancellationsRetired) (live : queue.LiveGroupsRegistered)
    (ref : Nat) (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.CancellationsRetired := by
  have tasks (more : List Occurrence) (current : State) (known : current.CancellationsRetired)
      : (more.foldl (fun current task => current.startTask task available)
          current).CancellationsRetired := by
    induction more generalizing current with
    | nil => exact known
    | cons task rest ih => exact ih _ (known.startTask task available)
  have cachedLive : (queue.cacheTaskFailures available).LiveGroupsRegistered := by
    intro node member
    rw [State.cacheTaskFailures_groupNodes] at member
    rw [State.cacheTaskFailures_registeredGroups]
    exact live node member
  unfold State.startGroup
  dsimp only
  split
  · exact prior.cacheTaskFailures available
  · split
    · exact tasks _ _ (prior.cacheTaskFailures available)
    · exact (prior.cacheTaskFailures available).removeGroup cachedLive _

/-- The actual startup fold preserves permanent retirement for every cancellation marker. -/
theorem State.CancellationsRetired.startNewWork {queue : State}
    (prior : queue.CancellationsRetired) (live : queue.LiveGroupsRegistered)
    (released : NewWork) (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.CancellationsRetired := by
  have groups (more : NodeRefs) (acc : State × List GroupFailureEvent)
      (known : acc.1.CancellationsRetired) (registered : acc.1.LiveGroupsRegistered)
      : (more.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.CancellationsRetired := by
    induction more generalizing acc with
    | nil => exact known
    | cons ref rest ih =>
        have nextLive : (acc.1.startGroup ref available).1.LiveGroupsRegistered := by
          intro node member
          rw [State.startGroup_registeredGroups]
          exact registered node ((acc.1.startGroup_groupNodes_sublist ref available).subset member)
        exact ih _ (known.startGroup registered ref available) nextLive
  have streams (more : NodeRefs) (current : State) (known : current.CancellationsRetired)
      : (more.foldl State.startStream current).CancellationsRetired := by
    induction more generalizing current with
    | nil => exact known
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact known
  exact streams _ _ (groups _ _ prior live)

theorem State.CancellationsRetired.finishGroupSuccess {queue : State}
    (prior : queue.CancellationsRetired) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.CancellationsRetired :=
  prior.of_frame (queue.finishGroupSuccess_cancelledGroups group)
    (fun _ retired => retired.finishGroupSuccess group)

/-- Real initialization has no cancellation marker before its first supplied batch. -/
theorem createWorkQueue_cancellationsRetired (work : Work)
    : (State.initialize work).CancellationsRetired := by
  intro ref member
  rw [createWorkQueue_cancelledGroups_empty] at member
  cases member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
