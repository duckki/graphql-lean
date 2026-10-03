import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingCounts

/-! Pending counters during the single-pass settlement/flush loop. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The remaining contributor refs still owe one physical decrement. The logical
settlement list already includes the current success, even if another group has flushed
its value and removed its memberships. This debt is proof evidence, not queue state.
-/
def State.PendingDebt (queue : State) (eligible : Nat → Prop)
    (settled : List Occurrence) (remaining : NodeRefs)
    : Prop :=
  ∀ node ∈ queue.groupNodes,
    eligible node.group.node.ref
    → node.pending
      = unsettledCount node.tasks settled
        + if node.group.node.ref ∈ remaining then 1 else 0

/-- A counter may include decrement debt but never undercounts unsettled memberships.
The eligibility predicate restricts which live groups require this safety bound.
-/
def State.PendingBound (queue : State) (eligible : Nat → Prop) (settled : List Occurrence)
    : Prop :=
  ∀ node ∈ queue.groupNodes,
    eligible node.group.node.ref → unsettledCount node.tasks settled ≤ node.pending

/-- Debt is nonnegative, so its exact ledger supplies the safety bound. -/
theorem State.PendingDebt.toBound {queue : State} {eligible settled remaining}
    (tracks : queue.PendingDebt eligible settled remaining)
    : queue.PendingBound eligible settled := by
  intro node member relevant
  rw [tracks node member relevant]
  exact Nat.le_add_right _ _

/-- Removing settled memberships preserves the lower bound. Witness: their logical
unsettled count is unchanged by the filter.
-/
theorem State.PendingBound.removeTask {queue : State} {eligible settled}
    (tracks : queue.PendingBound eligible settled)
    (occurrence : Occurrence) (already : occurrence ∈ settled)
    : (queue.removeTask occurrence).PendingBound eligible settled := by
  intro node member relevant
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  change unsettledCount (old.tasks.filter (· != occurrence)) settled ≤ old.pending
  rw [unsettledCount_remove_settled _ _ _ already]
  exact tracks old oldMember relevant

/-- A zero bounded counter has no unsettled memberships. Witness: the natural-number
bound forces an empty unsettled-token count.
-/
theorem State.PendingBound.allSettled {queue : State} {eligible settled}
    (tracks : queue.PendingBound eligible settled)
    {node : GroupNode} (member : node ∈ queue.groupNodes)
    (relevant : eligible node.group.node.ref) (zero : node.pending = 0)
    : ∀ occurrence ∈ node.tasks, occurrence ∈ settled := by
  have count := tracks node member relevant
  have empty : unsettledCount node.tasks settled = 0 := by omega
  exact GroupNode.PendingTracks.allSettled node settled
    (by change node.pending = _; rw [zero, empty]) zero

/-- A fresh shared settlement creates exactly one decrement debt at each contributor.
Witness: duplicate-free task membership and exact ownership identify each added token.
-/
theorem State.PendingDebt.beginSettlement {queue : State} {eligible : Nat → Prop}
    {settled : List Occurrence} {occurrence : Occurrence} {refs : NodeRefs}
    (tracks
      : ∀ node ∈ queue.groupNodes,
          eligible node.group.node.ref → node.PendingTracks settled)
    (unique : queue.TaskMembershipsUnique)
    (owned
      : ∀ node ∈ queue.groupNodes,
          eligible node.group.node.ref
          → (occurrence ∈ node.tasks ↔ node.group.node.ref ∈ refs))
    (fresh : occurrence ∉ settled)
    : queue.PendingDebt eligible (occurrence :: settled) refs := by
  intro node member relevant
  rw [tracks node member relevant]
  by_cases contributes : node.group.node.ref ∈ refs
  · rw [ite_eq_left contributes]
    exact unsettledCount_settle node.tasks settled occurrence (unique node member)
      ((owned node member relevant).mpr contributes) fresh
  · rw [ite_eq_right contributes, Nat.add_zero]
    exact (unsettledCount_settle_absent node.tasks settled occurrence
      (fun present => contributes ((owned node member relevant).mp present))).symm

/-- Removing an already logically settled membership leaves decrement debt unchanged.
Witness: filtering that occurrence changes no logical unsettled-token count.
-/
theorem State.PendingDebt.removeTask {queue : State} {eligible settled remaining}
    (tracks : queue.PendingDebt eligible settled remaining)
    (occurrence : Occurrence) (already : occurrence ∈ settled)
    : (queue.removeTask occurrence).PendingDebt eligible settled remaining := by
  intro node member relevant
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  change old.pending = unsettledCount (old.tasks.filter (· != occurrence)) settled
    + if old.group.node.ref ∈ remaining then 1 else 0
  rw [unsettledCount_remove_settled _ _ _ already]
  exact tracks old oldMember relevant

/-- Pruning only removes group nodes; every retained node has the same counter debt.
Witness: induction through the finite pruning traversal.
-/
theorem State.PendingDebt.pruneEmptyGroups {queue : State} {eligible settled remaining}
    (tracks : queue.PendingDebt eligible settled remaining)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.PendingDebt eligible settled remaining := by
  have loop (fuel : Nat) (current : State) (todo kept : List Execution.DeliveryNode)
      (currentTracks : current.PendingDebt eligible settled remaining)
      : (State.pruneEmptyGroups.go fuel current todo kept).1.PendingDebt
          eligible settled remaining := by
    induction fuel generalizing current todo kept with
    | zero => exact currentTracks
    | succ fuel ih =>
        cases todo with
        | nil => exact currentTracks
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentTracks
            · split
              · apply ih
                intro node member relevant
                exact currentTracks node (List.mem_filter.mp member).1 relevant
              · exact ih _ _ _ currentTracks
  exact loop _ queue groups [] tracks

/-- Flushing only logically settled tasks preserves every remaining decrement debt.
Witness: settled-membership removal followed by unchanged-node filtering and pruning.
-/
theorem State.PendingDebt.finishGroupSuccess {queue : State} {eligible settled remaining}
    (tracks : queue.PendingDebt eligible settled remaining)
    (group : GroupNode) (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.PendingDebt eligible settled remaining := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have foldTracks (tasks : List Occurrence)
      (included : ∀ occurrence ∈ tasks, occurrence ∈ settled) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.PendingDebt eligible settled remaining →
        (tasks.foldl step acc).1.PendingDebt eligible settled remaining := by
    induction tasks with
    | nil => intro acc currentTracks; exact currentTracks
    | cons occurrence rest ih =>
        intro acc currentTracks
        apply ih (fun task member => included task (by simp [member]))
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · exact currentTracks
        · exact currentTracks.removeTask occurrence (included occurrence (by simp))
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedTracks : flushed.PendingDebt eligible settled remaining :=
    foldTracks group.tasks all _ tracks
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentTracks : current.PendingDebt eligible settled remaining := by
    intro node member relevant
    exact flushedTracks node (List.mem_filter.mp member).1 relevant
  exact currentTracks.pruneEmptyGroups _

/-- A zero physical counter implies that every remaining membership has logically
settled, even while other groups still owe decrements. Witness: both summands are natural.
-/
theorem State.PendingDebt.allSettled {queue : State} {eligible settled remaining}
    (tracks : queue.PendingDebt eligible settled remaining)
    {node : GroupNode} (member : node ∈ queue.groupNodes)
    (relevant : eligible node.group.node.ref) (zero : node.pending = 0)
    : ∀ occurrence ∈ node.tasks, occurrence ∈ settled := by
  exact tracks.toBound.allSettled member relevant zero

/-- Updating the current contributor pays its one debt and leaves every other ref's
debt intact. Witness: unique group refs and the duplicate-free contributor suffix.
-/
theorem State.PendingDebt.decrement {queue : State} {eligible settled remaining ref}
    (tracks : queue.PendingDebt eligible settled (ref :: remaining))
    (unique : queue.GroupRefsUnique) (absent : ref ∉ remaining)
    {node : GroupNode} (found : queue.groupNode? ref = some node)
    (failure : Option Nat := node.failure)
    : (queue.putGroupNode { node with pending := node.pending - 1, failure }).PendingDebt
        eligible settled remaining := by
  have nodeRef := queue.groupNode?_ref found
  have nodeMember := List.mem_of_find?_eq_some found
  intro next member relevant
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · rename_i equal
    have sameNode := unique.sameNode oldMember nodeMember (beq_iff_eq.mp equal)
    subst old
    subst next
    have count := tracks node nodeMember relevant
    simp only [nodeRef, List.mem_cons_self, ite_true] at count
    simp [nodeRef, absent, count]
  · rename_i different
    subst next
    have unequal : old.group.node.ref ≠ ref := by
      simpa only [nodeRef, beq_iff_eq] using different
    simpa [unequal] using tracks old oldMember relevant

/-- A missing contributor cannot occur in any live node's counter debt.
Witness: a successful lookup would otherwise exist at that ref.
-/
theorem State.PendingDebt.skipMissing {queue : State} {eligible settled remaining ref}
    (tracks : queue.PendingDebt eligible settled (ref :: remaining))
    (missing : queue.groupNode? ref = none)
    : queue.PendingDebt eligible settled remaining := by
  intro node member relevant
  have unequal : node.group.node.ref ≠ ref := by
    intro equal
    have none := List.find?_eq_none.mp missing node member
    simp [equal] at none
  simpa [unequal] using tracks node member relevant

/-- The literal single-pass success fold, named only for induction proofs. -/
def successGroupStep (acc : State × List WorkQueueEvent × NewWork)
    (group : Execution.DeliveryNode)
    : State × List WorkQueueEvent × NewWork :=
  let (current, events, released) := acc
  match current.groupNode? group.ref with
  | none => (current, events, released)
  | some node =>
      let node := { node with pending := node.pending - 1 }
      let current := current.putGroupNode node
      if current.rootGroups.contains group.ref
          && node.pending == 0
          && node.failure.isNone then
        let (next, finished, newWork) := current.finishGroupSuccess node
        (
          next,
          events ++ finished,
          ⟨
            released.newGroups ++ newWork.newGroups,
            released.newStreams ++ newWork.newStreams
          ⟩
        )
      else
        (current, events, released)

/-- The interleaved loop discharges each contributor's decrement debt exactly once.
Witness: induction on the duplicate-free contributor list, carrying any additional
queue invariant preserved by decrement and by a flush of logically settled tasks.
-/
theorem successGroupFold_preserves (eligible : Nat → Prop) (settled : List Occurrence)
    (invariant : State → Prop)
    (refs : ∀ queue, invariant queue → queue.GroupRefsUnique)
    (roots : ∀ queue, invariant queue → ∀ ref ∈ queue.rootGroups, eligible ref)
    (decrement
      : ∀ queue node,
          invariant queue
          → queue.groupNode? node.group.node.ref = some node
          → invariant (queue.putGroupNode { node with pending := node.pending - 1 }))
    (flush
      : ∀ queue node remaining,
          invariant queue
          → queue.PendingDebt eligible settled remaining
          → node ∈ queue.groupNodes
          → node.group.node.ref ∈ queue.rootGroups
          → node.pending = 0
          → (∀ occurrence ∈ node.tasks, occurrence ∈ settled)
          → invariant (queue.finishGroupSuccess node).1)
    (groups : List Execution.DeliveryNode)
    (unique : (groups.map Execution.DeliveryNode.ref).Nodup)
    (acc : State × List WorkQueueEvent × NewWork)
    (valid : invariant acc.1)
    (tracks : acc.1.PendingDebt eligible settled (groups.map Execution.DeliveryNode.ref))
    : invariant (groups.foldl successGroupStep acc).1
      ∧ (groups.foldl successGroupStep acc).1.PendingDebt eligible settled [] := by
  induction groups generalizing acc with
  | nil => exact ⟨valid, tracks⟩
  | cons group rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      apply ih tailUnique
      · obtain ⟨queue, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact valid
        · rename_i node found
          have nodeRef := queue.groupNode?_ref found
          have nextValid := decrement queue node valid (nodeRef ▸ found)
          have nextTracks := tracks.decrement (refs queue valid) absent found
          split
          · rename_i ready
            have active : group.ref ∈ queue.rootGroups := by
              simpa [State.putGroupNode]
                using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready).1).1
            have zero : node.pending - 1 = 0 := by
              simpa using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready).1).2
            have member : { node with pending := node.pending - 1 } ∈
                (queue.putGroupNode { node with pending := node.pending - 1 }).groupNodes := by
              apply List.mem_map.mpr
              exact ⟨node, List.mem_of_find?_eq_some found, by simp⟩
            exact flush _ _ _ nextValid nextTracks member (nodeRef ▸ active) zero
              (nextTracks.allSettled member (nodeRef ▸ roots queue valid _ active) zero)
          · exact nextValid
      · obtain ⟨queue, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · rename_i missing
          exact tracks.skipMissing missing
        · rename_i node found
          have nodeRef := queue.groupNode?_ref found
          have nextTracks := tracks.decrement (refs queue valid) absent found
          split
          · rename_i ready
            have active : group.ref ∈ queue.rootGroups := by
              simpa [State.putGroupNode]
                using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready).1).1
            have zero : node.pending - 1 = 0 := by
              simpa using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready).1).2
            have member : { node with pending := node.pending - 1 } ∈
                (queue.putGroupNode { node with pending := node.pending - 1 }).groupNodes := by
              apply List.mem_map.mpr
              exact ⟨node, List.mem_of_find?_eq_some found, by simp⟩
            exact nextTracks.finishGroupSuccess _
              (nextTracks.allSettled member (nodeRef ▸ roots queue valid _ active) zero)
          · exact nextTracks

/-- Decompose task success into cancellation or its single-pass fold and release drain.
Witness: definitional equality; the owner guard is evaluated before the settlement.
-/
theorem State.taskSuccess_eq {queue : State} (occurrence : Occurrence)
    (result : TaskResult) (taskNode : TaskNode)
    (found : queue.taskNode? occurrence = some taskNode)
    : queue.taskSuccess occurrence result
      = if !queue.taskHasHealthyOwner taskNode.task then
          (queue.removeTask occurrence, [])
        else
          let integrated :=
            ((queue.putTaskNode
                { taskNode with value := some result.value }).maybeIntegrateWork
              result.work (some occurrence)).1
          let released := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
          let drained := (released.1.startNewWork released.2.2).drainReadyGroups
          (drained.1, released.2.1 ++ drained.2) := by
  simp only [State.taskSuccess, found]
  rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
