import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! The executable healthy-owner guard and ignored task settlements. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Retained records and healthy ownership are different facts
-----------------------------------------------------------------------------------------

/-- The task guard succeeds exactly when a contributing group passes its health check.
Witness: the existential membership characterization of Boolean list search.
-/
theorem State.taskHasHealthyOwner_iff {queue : State} {task : Task}
    : queue.taskHasHealthyOwner task = true
      ↔ ∃ group ∈ task.groups, queue.groupIsHealthy group.ref = true := by
  simp [State.taskHasHealthyOwner, List.any_eq_true]

/-- A rejected task has no healthy contributor, whether announced or still latent.
Witness: negate the existential healthy-owner characterization.
-/
theorem State.taskHasHealthyOwner_false_iff {queue : State} {task : Task}
    : queue.taskHasHealthyOwner task = false
      ↔ ∀ group ∈ task.groups, queue.groupIsHealthy group.ref = false := by
  simp [State.taskHasHealthyOwner, List.any_eq_false]

/-- A healthy group has a present record without a cached failure of its own.
Witness: inspect the first lookup and the first conjunct of the ancestor check.
-/
theorem State.groupIsHealthy_present {queue : State} {ref : NodeRef}
    (healthy : queue.groupIsHealthy ref = true)
    : ∃ node, queue.groupNode? ref = some node ∧ node.failure = none := by
  unfold State.groupIsHealthy at healthy
  split at healthy
  · cases healthy
  · rename_i node found
    exact ⟨node, found, Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp healthy).1⟩

/-- An ancestor-closed healthy predicate makes the executable group guard succeed.
Witness: strictly decreasing parent refs give distinct visited records, so the finite
node-count budget cannot expire before the parent walk ends. Healthy refs are excluded
from cancellation history, so missing healthy ancestors end the walk successfully.
No assumption requires successfully completed ancestors to remain present.
-/
theorem State.groupIsHealthy_of_invariant {queue : State} {ref : NodeRef}
    {node : GroupNode} (found : queue.groupNode? ref = some node) (healthy : Nat → Prop)
    (caches
      : ∀ node ∈ queue.groupNodes, healthy node.group.node.ref → node.failure = none)
    (parents
      : ∀ node ∈ queue.groupNodes,
          ∀ parent,
            node.group.parent = some parent
            → healthy node.group.node.ref
            → healthy parent)
    (decreasing
      : ∀ node ∈ queue.groupNodes,
          ∀ parent, node.group.parent = some parent → parent < node.group.node.ref)
    (uncancelled : ∀ ref, healthy ref → ref ∉ queue.cancelledGroups) (safe : healthy ref)
    : queue.groupIsHealthy ref = true := by
  have lookupRef {ref : NodeRef} {node : GroupNode}
      (found : queue.groupNode? ref = some node) : node.group.node.ref = ref := by
    have selected := List.find?_some
      (p := fun candidate : GroupNode => candidate.group.node.ref == ref) found
    exact beq_iff_eq.mp selected
  let refs := queue.groupNodes.map (fun node => node.group.node.ref)
  have walk (fuel : Nat) (current : Option Nat) (visited : NodeRefs)
      (unique : visited.Nodup) (listed : visited.Subset refs)
      (room : queue.groupNodes.length < visited.length + fuel)
      (earlier : ∀ ref, current = some ref → ∀ old ∈ visited, ref < old)
      (safe : ∀ ref, current = some ref → healthy ref)
      : State.groupIsHealthy.ancestorsHealthy queue fuel current = true := by
    induction fuel generalizing current visited with
    | zero =>
        have bound := unique.length_le_of_subset listed
        have length : refs.length = queue.groupNodes.length := List.length_map _
        omega
    | succ fuel ih =>
        cases current with
        | none => rfl
        | some ref =>
            cases found : queue.groupNode? ref with
            | none =>
                simp [State.groupIsHealthy.ancestorsHealthy, found,
                  uncancelled ref (safe ref rfl)]
            | some node =>
                have member := List.mem_of_find?_eq_some found
                have same := lookupRef found
                have nodeSafe : healthy node.group.node.ref := same ▸ safe ref rfl
                have uncached := caches node member nodeSafe
                simp only [State.groupIsHealthy.ancestorsHealthy, found, uncached,
                  Option.isNone_none, Bool.true_and]
                apply ih node.group.parent (ref :: visited)
                · exact List.nodup_cons.mpr
                    ⟨fun present => Nat.lt_irrefl ref (earlier ref rfl ref present), unique⟩
                · intro other present
                  rcases List.mem_cons.mp present with rfl | old
                  · exact List.mem_map.mpr ⟨node, member, same⟩
                  · exact listed old
                · simp only [List.length_cons]
                  omega
                · intro parent parentEq old oldMember
                  have smaller : parent < ref := same ▸ decreasing node member parent parentEq
                  rcases List.mem_cons.mp oldMember with rfl | prior
                  · exact smaller
                  · exact Nat.lt_trans smaller (earlier ref rfl old prior)
                · intro parent parentEq
                  exact parents node member parent parentEq nodeSafe
  have member := List.mem_of_find?_eq_some found
  have same := lookupRef found
  have nodeSafe : healthy node.group.node.ref := same ▸ safe
  simp only [State.groupIsHealthy, found, caches node member nodeSafe,
    Option.isNone_none, Bool.true_and]
  apply walk queue.groupNodes.length node.group.parent [ref] (by simp)
  · intro other present
    have equal := List.mem_singleton.mp present
    subst other
    exact List.mem_map.mpr ⟨node, member, same⟩
  · simp
  · intro parent parentEq old present
    have equal := List.mem_singleton.mp present
    subst old
    exact same ▸ decreasing node member parent parentEq
  · intro parent parentEq
    exact parents node member parent parentEq nodeSafe

-----------------------------------------------------------------------------------------
-- Late cancelled settlements perform cleanup, not publication or integration
-----------------------------------------------------------------------------------------

/-- An ignored success removes only its task bookkeeping, without publishing child work.
Witness: unfold the public handler at the started node and its failed health guard.
-/
theorem State.taskSuccess_of_noHealthyOwner {queue : State} {occurrence : Occurrence}
    {node : TaskNode} (found : queue.taskNode? occurrence = some node)
    (inactive : queue.taskHasHealthyOwner node.task = false) (result : TaskResult)
    : queue.taskSuccess occurrence result = (queue.removeTask occurrence, []) := by
  simp only [State.taskSuccess, found, inactive, Bool.not_false, ↓reduceIte]

/-- An ignored failure adds no errors to retained notification records.
Witness: the same pre-settlement guard selects cleanup before the contributor fold.
-/
theorem State.taskFailure_of_noHealthyOwner {queue : State} {occurrence : Occurrence}
    {node : TaskNode} (found : queue.taskNode? occurrence = some node)
    (inactive : queue.taskHasHealthyOwner node.task = false) (errors : Nat)
    : queue.taskFailure occurrence errors = (queue.removeTask occurrence, []) := by
  simp only [State.taskFailure, found, inactive, Bool.not_false, ↓reduceIte]

/-- Any output from task success requires a started task with a healthy owner.
Witness: missing and fully invalidated task branches both emit the empty list.
-/
theorem State.taskSuccess_output_hasHealthyOwner {queue : State}
    {occurrence : Occurrence} {result : TaskResult}
    (emitted : (queue.taskSuccess occurrence result).2 ≠ [])
    : ∃ node,
        queue.taskNode? occurrence = some node
        ∧ queue.taskHasHealthyOwner node.task = true := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found] at emitted
  | some node =>
      refine ⟨node, rfl, ?_⟩
      cases active : queue.taskHasHealthyOwner node.task with
      | false => exact (emitted (congrArg Prod.snd
          (State.taskSuccess_of_noHealthyOwner found active result))).elim
      | true => rfl

/-- A task-failure output likewise requires a healthy owner before that failure.
Witness: cancellation cleanup cannot emit a group completion, even for a retained cache.
-/
theorem State.taskFailure_output_hasHealthyOwner {queue : State}
    {occurrence : Occurrence} {errors : Nat}
    (emitted : (queue.taskFailure occurrence errors).2 ≠ [])
    : ∃ node,
        queue.taskNode? occurrence = some node
        ∧ queue.taskHasHealthyOwner node.task = true := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found] at emitted
  | some node =>
      refine ⟨node, rfl, ?_⟩
      cases active : queue.taskHasHealthyOwner node.task with
      | false => exact (emitted (congrArg Prod.snd
          (State.taskFailure_of_noHealthyOwner found active errors))).elim
      | true => rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
