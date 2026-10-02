import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MissingParentHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthStability

/-! Health of uncancelled retired records through registration and bookkeeping. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Retired record health supplies the missing-parent guard boundary
-----------------------------------------------------------------------------------------

/-- Every known retired record not marked cancelled is healthy under `failed` in `work`.
This is internal proof evidence about `queue`, not additional implementation state or a
source premise. Unlike healthy-retirement closure, it asserts health rather than assuming it.
-/
def State.UncancelledRetiredHealthy (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  ∀ node dependencies,
    GroupRecordAt work node dependencies
    → queue.RetiredGroup node.key
    → node.key ∉ queue.cancelledGroups
    → ¬GroupRecordInvalidated work failed node.key

/-- With no failures, every uncancelled retirement is healthy.
Witness: invalidation always originates in a recorded failed task.
-/
theorem State.UncancelledRetiredHealthy.of_empty (queue : State) (work : Execution.Work)
    : queue.UncancelledRetiredHealthy work [] := by
  intro node dependencies known retired uncancelled invalid
  exact invalid.nonempty rfl

/-- Healthy uncancelled retirement justifies every accepting missing-parent boundary.
Witness: permanent parent registration makes the absent parent retired; its health and
the exact generated parent chain give all of the child's ancestor health.
-/
theorem State.UncancelledRetiredHealthy.missingParent {queue : State}
    {work failed parents} (prior : queue.UncancelledRetiredHealthy work failed)
    (generated : ExecutedWork work) (fields : queue.GroupParentsCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (registered
      : ∀ node ∈ queue.groupNodes,
          ∀ parent, node.group.parent = some parent → parent ∈ queue.registeredGroups)
    : queue.MissingParentAncestorsHealthy work failed := by
  intro node member uncached dependencies known parent parentEq missing uncancelled
  have retired : queue.RetiredGroup parent :=
    .of_lookup_none (registered node member parent parentEq) missing
  have head : dependencies.head? = some parent := by
    rw [canonical _ _ known, ← fields node member, parentEq]
  cases dependencies with
  | nil => cases head
  | cons key rest =>
      have same : key = parent := Option.some.inj head
      subst key
      obtain ⟨record, recordKey, parentKnown⟩ := known.parent
      have healthy := prior record rest parentKnown (recordKey.symm ▸ retired)
        (recordKey.symm ▸ uncancelled)
      exact (GroupAncestorsHealthy.child generated known parentKnown
        (recordKey.symm ▸ head) healthy) _ _ known rfl

-----------------------------------------------------------------------------------------
-- Operations that create no uncancelled retirement preserve the health invariant
-----------------------------------------------------------------------------------------

/-- Reflecting uncancelled retirements to an earlier queue preserves record health.
Witness: apply the earlier certificate to the unchanged structural record and inventory.
-/
theorem State.UncancelledRetiredHealthy.of_retirementOrigins {before after : State}
    {work failed} (prior : before.UncancelledRetiredHealthy work failed)
    (origins
      : ∀ key,
          after.RetiredGroup key
          → key ∉ after.cancelledGroups
          → before.RetiredGroup key ∧ key ∉ before.cancelledGroups)
    : after.UncancelledRetiredHealthy work failed := by
  intro node dependencies known retired uncancelled
  have old := origins node.key retired uncancelled
  exact prior node dependencies known old.1 old.2

/-- Updating a live record changes neither retired keys nor cancellation history.
Witness: replacement retains the exact live-key list and permanent registry.
-/
theorem State.UncancelledRetiredHealthy.putGroupNode {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (node : GroupNode)
    : (queue.putGroupNode node).UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro key retired uncancelled
  exact ⟨
    ⟨retired.1, by simpa only [State.putGroupNode_keys] using retired.2⟩,
    uncancelled
  ⟩

/-- Task cleanup changes memberships but retains the exact retirement and cancellation sets.
Witness: the group-node map keeps all keys and both permanent registries.
-/
theorem State.UncancelledRetiredHealthy.removeTask {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (occurrence : Occurrence)
    : (queue.removeTask occurrence).UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro key retired uncancelled
  refine ⟨⟨retired.1, ?_⟩, uncancelled⟩
  simpa only [State.removeTask, List.map_map, Function.comp_def] using retired.2

/-- Activation does not affect retired-record health.
Witness: group records, registration history, and cancellation markers are unchanged.
-/
theorem State.UncancelledRetiredHealthy.startNewWork {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (released : NewWork)
    : (queue.startNewWork released).UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro key retired uncancelled
  simpa only [State.RetiredGroup, State.startNewWork_registeredGroups,
    (queue.startNewWork_groupCore released).1, State.startNewWork_cancelledGroups]
    using And.intro retired uncancelled

/-- Failure removal creates only cancelled retirements, excluded from this invariant.
Witness: an absent uncancelled key after cleanup was already absent and uncancelled.
-/
theorem State.UncancelledRetiredHealthy.removeGroup {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (root : Nat)
    : (queue.removeGroup root).UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro key retired uncancelled
  have old := queue.removeGroup_missing_uncancelled root key retired.lookup_none uncancelled
  exact ⟨.of_lookup_none retired.1 old.1, old.2⟩

/-- Candidate registration creates no new uncancelled retirement, even in child-first order.
Witness: newly refused records carry cancellation markers; other retirements are inherited.
-/
theorem State.UncancelledRetiredHealthy.addGroups {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (groups : List Group)
    : (queue.addGroups groups).1.UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro key retired uncancelled
  exact ⟨(queue.addGroups_retired_or_cancelled groups key retired).resolve_right uncancelled,
    fun member => uncancelled (queue.addGroups_cancelledGroups_subset groups member)⟩

/-- Task registration preserves all uncancelled retired records' health.
Witness: registration leaves permanent groups unchanged and retains each old live key.
-/
theorem State.UncancelledRetiredHealthy.addTask {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (task : Task)
    : (queue.addTask task).UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro key retired uncancelled
  refine ⟨⟨?_, fun live => retired.2 (queue.addTask_includesKeys task key live)⟩, ?_⟩
  · have registered := retired.1
    rwa [State.addTask_registeredGroups] at registered
  · rwa [State.addTask_cancelledGroups] at uncancelled

/-- Stream registration does not modify group retirement or cancellation data.
Witness: both root and producer-linked stream installation leave those fields unchanged.
-/
theorem State.UncancelledRetiredHealthy.addStreams {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.UncancelledRetiredHealthy work failed := by
  unfold State.addStreams
  split
  · exact prior
  · dsimp
    split <;> exact prior

/-- Arbitrary work integration preserves healthy uncancelled retirements.
Witness: group registration, each task insertion, and stream installation preserve the
certificate. No generated-work or contributor-availability premise is needed here.
-/
theorem State.UncancelledRetiredHealthy.maybeIntegrateWork {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (newWork : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.UncancelledRetiredHealthy work
        failed := by
  have loop (tasks : List Task) (current : State)
      (invariant : current.UncancelledRetiredHealthy work failed)
      : (tasks.foldl State.addTask current).UncancelledRetiredHealthy work failed := by
    induction tasks generalizing current with
    | nil => exact invariant
    | cons task rest ih => exact ih _ (invariant.addTask task)
  exact (loop newWork.tasks _ (prior.addGroups newWork.groups)).addStreams
    newWork.streams parentTask

-----------------------------------------------------------------------------------------
-- Health at successful removal and fresh-failure extension
-----------------------------------------------------------------------------------------

/-- Filtering a healthy key preserves healthy uncancelled retirement.
Witness: a newly retired target is the healthy removed key; every other target was already
retired. Failure health is a static fact about `work` and `failed`, not the live lookup.
-/
theorem State.UncancelledRetiredHealthy.filter_parent {queue : State} {work failed key}
    (prior : queue.UncancelledRetiredHealthy work failed)
    (healthy : ¬GroupRecordInvalidated work failed key)
    : ({
        queue with
          groupNodes := queue.groupNodes.filter (fun node => node.group.node.key != key)
      }).UncancelledRetiredHealthy
        work failed := by
  intro node dependencies known retired uncancelled
  by_cases same : node.key = key
  · exact same ▸ healthy
  · have old : queue.RetiredGroup node.key := by
      refine ⟨retired.1, ?_⟩
      intro live
      obtain ⟨other, member, sameKey⟩ := List.mem_map.mp live
      exact retired.2 (List.mem_map.mpr ⟨other,
        List.mem_filter.mpr ⟨member, by simp [sameKey, same]⟩, sameKey⟩)
    exact prior node dependencies known old uncancelled

/-- A fresh registered failure cannot invalidate an uncancelled healthy retirement.
Witness: the structural ancestor certificate and healthy-owner accounting discharge the
general retired-record fresh-failure theorem before the actual handler mutates state.
-/
theorem State.UncancelledRetiredHealthy.cons_fresh {queue : State} {work settled failed}
    (prior : queue.UncancelledRetiredHealthy work failed)
    (ancestors : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    {task : Task} (registered : task ∈ queue.tasks)
    (matching : TaskMatches work task) (fresh : task.occurrence ∉ settled)
    : queue.UncancelledRetiredHealthy work (task.occurrence :: failed) := by
  intro node dependencies known retired uncancelled
  exact retired.healthy_cons_fresh (ancestors node.key retired uncancelled) generated known
    (prior node dependencies known retired uncancelled) accounted registered matching fresh

-----------------------------------------------------------------------------------------
-- Full-chain registration turns the health certificate into the guard's local boundary
-----------------------------------------------------------------------------------------

/-- Registering a parent-covered work chunk preserves the missing-parent health boundary.
Witness: registration preserves healthy retirements and closes the permanent parent
registry. Thus a missing uncancelled parent is healthy, including for newly added children.
The old queue need not have every parent live, and candidate order is unrestricted.
-/
theorem State.UncancelledRetiredHealthy.maybeIntegrateWork_missingParent
    {queue : State} {work failed parents}
    (prior : queue.UncancelledRetiredHealthy work failed) (generated : ExecutedWork work)
    (fields : queue.GroupParentsCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (registry : queue.ParentRegistryClosed parents)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (newWork : Work)
    (parentLinks
      : ∀ group ∈ newWork.groups, group.parent = (parents group.node.key).head?)
    (parentsCovered : newWork.ParentsCovered)
    (covered
      : ∀ task ∈ newWork.tasks,
        ∀ key ∈ task.groups.map Execution.DeliveryNode.key,
          ∃ group ∈ newWork.groups, group.node.key = key)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork newWork parentTask).1.MissingParentAncestorsHealthy
        work failed := by
  have nextFields := fields.maybeIntegrateWork newWork parentLinks parentTask
  have nextRegistry :=
    registry.maybeIntegrateWork live newWork parentLinks parentsCovered parentTask
  have nextLive := (queue.maybeIntegrateWork_registration live tasks newWork covered parentTask).1
  exact (prior.maybeIntegrateWork newWork parentTask).missingParent generated nextFields canonical
    (fun node member parent parentEq =>
      nextRegistry.parent_registered nextLive nextFields member parentEq)

/-- Fresh integration candidates have healthy ancestry because their full parent list is
empty. Witness: candidate extraction gives a parentless registered descriptor and generated
canonical ancestry equates every occurrence of its key. Pruned descendants are separate.
-/
theorem State.maybeIntegrateWork_newGroups_ancestorsHealthy {work failed}
    {parents : Nat → Keys} (queue : State) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (newWork : Work)
    (known
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (parentLinks
      : ∀ group ∈ newWork.groups, group.parent = (parents group.node.key).head?)
    (parentTask : Option Occurrence := none)
    : ∀ node ∈ (queue.maybeIntegrateWork newWork parentTask).2.newGroups,
        GroupAncestorsHealthy work failed node.key := by
  intro node member
  obtain ⟨group, included, same, parentless, _, _⟩ :=
    queue.addGroups_newGroup_candidate newWork.groups member
  obtain ⟨dependencies, descriptor⟩ := known group included
  have empty : dependencies = [] := by
    apply List.head?_eq_none_iff.mp
    rw [canonical _ _ descriptor, ← parentLinks group included, parentless]
  have healthy : GroupAncestorsHealthy work failed group.node.key :=
    GroupAncestorsHealthy.of_record generated descriptor (by simp [empty])
  exact same ▸ healthy

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
