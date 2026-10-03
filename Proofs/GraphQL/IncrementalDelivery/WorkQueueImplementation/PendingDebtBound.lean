import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDebt

/-! Safe counter debt when cancelled memberships leave surplus pending counts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Remaining decrements cannot consume an unsettled task's counter
-----------------------------------------------------------------------------------------

/-- Selected groups have enough pending tokens for unsettled memberships and the one
decrement still owed at each remaining contributor ref. Surplus tokens are permitted:
ignored cancelled settlements remove memberships without decrementing failed groups.
-/
def State.PendingDebtBound (queue : State) (eligible : Nat → Prop)
    (settled : List Occurrence) (remaining : NodeRefs)
    : Prop :=
  ∀ node ∈ queue.groupNodes,
    eligible node.group.node.ref
    → unsettledCount node.tasks settled
        + (if node.group.node.ref ∈ remaining then 1 else 0)
      ≤ node.pending

/-- Exact decrement debt implies its lower bound. Witness: equality implies inequality.
-/
theorem State.PendingDebt.toDebtBound {queue : State} {eligible settled remaining}
    (tracks : queue.PendingDebt eligible settled remaining)
    : queue.PendingDebtBound eligible settled remaining := by
  intro node member relevant
  exact Nat.le_of_eq (tracks node member relevant).symm

/-- Unsettled memberships are bounded even before every decrement has been paid.
Witness: dropping the nonnegative debt summand only weakens the bound.
-/
theorem State.PendingDebtBound.toBound {queue : State} {eligible settled remaining}
    (bounded : queue.PendingDebtBound eligible settled remaining)
    : queue.PendingBound eligible settled := by
  intro node member relevant
  exact Nat.le_trans (Nat.le_add_right _ _) (bounded node member relevant)

/-- With no decrement left, the debt bound is the ordinary safety bound.
Witness: the remaining-ref membership test is false.
-/
theorem State.pendingDebtBound_nil {queue : State} {eligible settled}
    : queue.PendingDebtBound eligible settled []
      ↔ queue.PendingBound eligible settled := by
  simp only [PendingDebtBound, PendingBound, List.not_mem_nil, ite_false, Nat.add_zero]

/-- A fresh settlement reserves one decrement token at each contributor, even when
failed groups already overcount. Witness: unique memberships remove exactly one token;
the owner equation identifies precisely the refs that owe a decrement.
-/
theorem State.PendingBound.beginSettlement {queue : State} {eligible : Nat → Prop}
    {settled : List Occurrence} {occurrence : Occurrence} {refs : NodeRefs}
    (bounded : queue.PendingBound eligible settled)
    (unique : queue.TaskMembershipsUnique)
    (owned
      : ∀ node ∈ queue.groupNodes,
          eligible node.group.node.ref
          → (occurrence ∈ node.tasks ↔ node.group.node.ref ∈ refs))
    (fresh : occurrence ∉ settled)
    : queue.PendingDebtBound eligible (occurrence :: settled) refs := by
  intro node member relevant
  have count := bounded node member relevant
  by_cases contributes : node.group.node.ref ∈ refs
  · rw [ite_eq_left contributes]
    rw [unsettledCount_settle node.tasks settled occurrence (unique node member)
      ((owned node member relevant).mpr contributes) fresh] at count
    exact count
  · rw [ite_eq_right contributes, Nat.add_zero,
      unsettledCount_settle_absent node.tasks settled occurrence
        (fun present => contributes ((owned node member relevant).mp present))]
    exact count

/-- Removing a logically settled task preserves all reserved decrement tokens.
Witness: the unsettled-membership count is unchanged by the removal filter.
-/
theorem State.PendingDebtBound.removeTask {queue : State} {eligible settled remaining}
    (bounded : queue.PendingDebtBound eligible settled remaining)
    (occurrence : Occurrence) (already : occurrence ∈ settled)
    : (queue.removeTask occurrence).PendingDebtBound eligible settled remaining := by
  intro node member relevant
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  change unsettledCount (old.tasks.filter (· != occurrence)) settled
    + (if old.group.node.ref ∈ remaining then 1 else 0) ≤ old.pending
  rw [unsettledCount_remove_settled _ _ _ already]
  exact bounded old oldMember relevant

/-- Pruning preserves every surviving group's debt bound.
Witness: induction through a traversal that only filters group records.
-/
theorem State.PendingDebtBound.pruneEmptyGroups {queue : State}
    {eligible settled remaining}
    (bounded : queue.PendingDebtBound eligible settled remaining)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.PendingDebtBound eligible settled remaining := by
  have loop (fuel : Nat) (current : State) (todo kept : List Execution.DeliveryNode)
      (currentBound : current.PendingDebtBound eligible settled remaining)
      : (State.pruneEmptyGroups.go fuel current todo kept).1.PendingDebtBound
          eligible settled remaining := by
    induction fuel generalizing current todo kept with
    | zero => exact currentBound
    | succ fuel ih =>
        cases todo with
        | nil => exact currentBound
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ currentBound
            · split
              · apply ih
                intro node member relevant
                exact currentBound node (List.mem_filter.mp member).1 relevant
              · exact ih _ _ _ currentBound
  exact loop _ queue groups [] bounded

/-- Flushing settled memberships cannot spend another group's reserved decrement.
Witness: induction over settled-task removal, followed by group filtering and pruning.
-/
theorem State.PendingDebtBound.finishGroupSuccess {queue : State}
    {eligible settled remaining}
    (bounded : queue.PendingDebtBound eligible settled remaining) (group : GroupNode)
    (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.PendingDebtBound eligible settled remaining := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have foldBound (tasks : List Occurrence)
      (included : ∀ occurrence ∈ tasks, occurrence ∈ settled) :
      ∀ acc : State × List ExecutionGroupValue × NodeRefs,
        acc.1.PendingDebtBound eligible settled remaining →
        (tasks.foldl step acc).1.PendingDebtBound eligible settled remaining := by
    induction tasks with
    | nil => intro acc currentBound; exact currentBound
    | cons occurrence rest ih =>
        intro acc currentBound
        apply ih (fun task member => included task (by simp [member]))
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · exact currentBound
        · exact currentBound.removeTask occurrence (included occurrence (by simp))
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have flushedBound : flushed.PendingDebtBound eligible settled remaining :=
    foldBound group.tasks all _ bounded
  let current : State :=
    { flushed with
        groupNodes := flushed.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentBound : current.PendingDebtBound eligible settled remaining := by
    intro node member relevant
    exact flushedBound node (List.mem_filter.mp member).1 relevant
  exact currentBound.pruneEmptyGroups _

/-- Group failure removes records without weakening any survivor's debt bound.
Witness: surviving group records are unchanged members of the earlier list.
-/
theorem State.PendingDebtBound.removeGroup {queue : State} {eligible settled remaining}
    (bounded : queue.PendingDebtBound eligible settled remaining) (ref : NodeRef)
    : (queue.removeGroup ref).PendingDebtBound eligible settled remaining := by
  intro node member relevant
  exact bounded node (List.mem_filter.mp member).1 relevant

/-- A zero bounded counter certifies that every membership has settled.
Witness: the ordinary pending bound derived by forgetting remaining decrement debt.
-/
theorem State.PendingDebtBound.allSettled {queue : State} {eligible settled remaining}
    (bounded : queue.PendingDebtBound eligible settled remaining)
    {node : GroupNode} (member : node ∈ queue.groupNodes)
    (relevant : eligible node.group.node.ref) (zero : node.pending = 0)
    : ∀ occurrence ∈ node.tasks, occurrence ∈ settled :=
  bounded.toBound.allSettled member relevant zero

/-- Paying a contributor's reserved decrement preserves all remaining lower bounds.
Witness: unique group refs isolate the update and the old bound reserves one token.
-/
theorem State.PendingDebtBound.decrement {queue : State} {eligible settled remaining ref}
    (bounded : queue.PendingDebtBound eligible settled (ref :: remaining))
    (unique : queue.GroupRefsUnique) (absent : ref ∉ remaining)
    {node : GroupNode} (found : queue.groupNode? ref = some node)
    (failure : Option Nat := node.failure)
    : (queue.putGroupNode
        { node with pending := node.pending - 1, failure }).PendingDebtBound
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
    have count := bounded node nodeMember relevant
    simp only [nodeRef, List.mem_cons_self, ite_true] at count
    simp only [nodeRef, ite_eq_right absent, Nat.add_zero]
    omega
  · rename_i different
    subst next
    have unequal : old.group.node.ref ≠ ref := by
      simpa only [nodeRef, beq_iff_eq] using different
    simpa [unequal] using bounded old oldMember relevant

/-- Missing contributors have no live decrement obligation.
Witness: every live group's ref differs from a ref with an unsuccessful lookup.
-/
theorem State.PendingDebtBound.skipMissing {queue : State}
    {eligible settled remaining ref}
    (bounded : queue.PendingDebtBound eligible settled (ref :: remaining))
    (missing : queue.groupNode? ref = none)
    : queue.PendingDebtBound eligible settled remaining := by
  intro node member relevant
  have unequal : node.group.node.ref ≠ ref := by
    intro equal
    have none := List.find?_eq_none.mp missing node member
    simp [equal] at none
  simpa [unequal] using bounded node member relevant

-----------------------------------------------------------------------------------------
-- The original single-pass owner loops preserve bounds, not just exact ledgers
-----------------------------------------------------------------------------------------

/-- The success fold pays each decrement without undercounting unsettled work.
Witness: contributor-list induction carrying a separate invariant; every immediate flush
is justified by the bound at its own zero-counter boundary, despite surplus failed counts.
-/
theorem successGroupFold_preservesBound (eligible : Nat → Prop)
    (settled : List Occurrence) (invariant : State → Prop)
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
          → queue.PendingDebtBound eligible settled remaining
          → node ∈ queue.groupNodes
          → node.group.node.ref ∈ queue.rootGroups
          → node.pending = 0
          → (∀ occurrence ∈ node.tasks, occurrence ∈ settled)
          → invariant (queue.finishGroupSuccess node).1)
    (groups : List Execution.DeliveryNode)
    (unique : (groups.map Execution.DeliveryNode.ref).Nodup)
    (acc : State × List WorkQueueEvent × NewWork) (valid : invariant acc.1)
    (bounded
      : acc.1.PendingDebtBound eligible settled (groups.map Execution.DeliveryNode.ref))
    : invariant (groups.foldl successGroupStep acc).1
      ∧ (groups.foldl successGroupStep acc).1.PendingBound eligible settled := by
  suffices result : invariant (groups.foldl successGroupStep acc).1 ∧
      (groups.foldl successGroupStep acc).1.PendingDebtBound eligible settled [] from
    ⟨result.1, result.2.toBound⟩
  induction groups generalizing acc with
  | nil => exact ⟨valid, bounded⟩
  | cons group rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      have step : invariant (successGroupStep acc group).1 ∧
          (successGroupStep acc group).1.PendingDebtBound eligible settled
            (rest.map Execution.DeliveryNode.ref) := by
        obtain ⟨queue, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · rename_i missing
          exact ⟨valid, bounded.skipMissing missing⟩
        · rename_i node found
          have nodeRef := queue.groupNode?_ref found
          have nextValid := decrement queue node valid (nodeRef ▸ found)
          have nextBound := bounded.decrement (refs queue valid) absent found
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
            have all := nextBound.allSettled member
              (nodeRef ▸ roots queue valid _ active) zero
            exact ⟨flush _ _ _ nextValid nextBound member (nodeRef ▸ active) zero all,
              nextBound.finishGroupSuccess _ all⟩
          · exact ⟨nextValid, nextBound⟩
      exact ih tailUnique (successGroupStep acc group) step.1 step.2

/-- The failure fold also preserves the pending lower bound on every surviving group.
Witness: distinct-owner induction; active failures remove their debt-bearing records,
while latent failures pay exactly one reserved decrement before retaining the error.
-/
theorem failureGroupFold_preservesBound (eligible : Nat → Prop)
    (settled : List Occurrence) (invariant : State → Prop)
    (refs : ∀ queue, invariant queue → queue.GroupRefsUnique)
    (decrement
      : ∀ queue (node : GroupNode) errors,
          invariant queue
          → queue.groupNode? node.group.node.ref = some node
          → invariant
              (queue.putGroupNode
                {
                  node with
                    pending := node.pending - 1
                    failure := some (node.failure.getD 0 + errors)
                }))
    (remove : ∀ queue ref, invariant queue → invariant (queue.removeGroup ref))
    (errors : Nat) (groups : List Execution.DeliveryNode)
    (unique : (groups.map Execution.DeliveryNode.ref).Nodup)
    (acc : State × List WorkQueueEvent) (valid : invariant acc.1)
    (bounded
      : acc.1.PendingDebtBound eligible settled (groups.map Execution.DeliveryNode.ref))
    : invariant (groups.foldl (failureGroupStep errors) acc).1
      ∧ (groups.foldl (failureGroupStep errors) acc).1.PendingBound eligible settled := by
  suffices result : invariant (groups.foldl (failureGroupStep errors) acc).1 ∧
      (groups.foldl (failureGroupStep errors) acc).1.PendingDebtBound eligible settled [] from
    ⟨result.1, result.2.toBound⟩
  induction groups generalizing acc with
  | nil => exact ⟨valid, bounded⟩
  | cons group rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      have step : invariant (failureGroupStep errors acc group).1 ∧
          (failureGroupStep errors acc group).1.PendingDebtBound eligible settled
            (rest.map Execution.DeliveryNode.ref) := by
        obtain ⟨queue, events⟩ := acc
        dsimp only [failureGroupStep]
        cases found : queue.groupNode? group.ref with
        | none => exact ⟨valid, bounded.skipMissing found⟩
        | some node =>
            dsimp only
            split
            · have same := queue.groupNode?_ref found
              change invariant (queue.removeGroup node.group.node.ref) ∧
                (queue.removeGroup node.group.node.ref).PendingDebtBound eligible settled _
              rw [same]
              exact ⟨remove queue group.ref valid,
                (bounded.removeGroup group.ref).skipMissing
                  (queue.removeGroup_ownGroupAbsent group.ref)⟩
            · have same := queue.groupNode?_ref found
              exact ⟨decrement queue node errors valid (same ▸ found),
                bounded.decrement (refs queue valid) absent found
                  (some (node.failure.getD 0 + errors))⟩
      exact ih tailUnique (failureGroupStep errors acc group) step.1 step.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
