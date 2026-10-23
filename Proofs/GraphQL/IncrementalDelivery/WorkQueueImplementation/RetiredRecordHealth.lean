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
    → queue.RetiredGroup node.ref
    → node.ref ∉ queue.cancelledGroups
    → ¬GroupRecordInvalidated work failed node.ref

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
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered
      : ∀ node ∈ queue.groupNodes,
          ∀ parent, node.group.parent = some parent → parent ∈ queue.registeredGroups)
    : queue.MissingParentAncestorsHealthy work failed := by
  intro node member dependencies known parent parentEq missing uncancelled
  have retired : queue.RetiredGroup parent :=
    .of_lookup_none (registered node member parent parentEq) missing
  have head : dependencies.head? = some parent := by
    rw [canonical _ _ known, ← fields node member, parentEq]
  cases dependencies with
  | nil => cases head
  | cons ref rest =>
      have same : ref = parent := Option.some.inj head
      subst ref
      obtain ⟨record, recordRef, parentKnown⟩ := known.parent
      have healthy := prior record rest parentKnown (recordRef.symm ▸ retired)
        (recordRef.symm ▸ uncancelled)
      exact (GroupAncestorsHealthy.child generated known parentKnown
        (recordRef.symm ▸ head) healthy) _ _ known rfl

-----------------------------------------------------------------------------------------
-- Operations that create no uncancelled retirement preserve the health invariant
-----------------------------------------------------------------------------------------

/-- Reflecting uncancelled retirements to an earlier queue preserves record health.
Witness: apply the earlier certificate to the unchanged structural record and inventory.
-/
theorem State.UncancelledRetiredHealthy.of_retirementOrigins {before after : State}
    {work failed} (prior : before.UncancelledRetiredHealthy work failed)
    (origins
      : ∀ ref,
          after.RetiredGroup ref
          → ref ∉ after.cancelledGroups
          → before.RetiredGroup ref ∧ ref ∉ before.cancelledGroups)
    : after.UncancelledRetiredHealthy work failed := by
  intro node dependencies known retired uncancelled
  have old := origins node.ref retired uncancelled
  exact prior node dependencies known old.1 old.2

/-- Updating a live record changes neither retired refs nor cancellation history.
Witness: replacement retains the exact live-ref list and permanent registry.
-/
theorem State.UncancelledRetiredHealthy.putGroupNode {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (node : GroupNode)
    : (queue.putGroupNode node).UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro ref retired uncancelled
  exact ⟨
    ⟨retired.1, by simpa only [State.putGroupNode_refs] using retired.2⟩,
    uncancelled
  ⟩

/-- Task cleanup changes memberships but retains the exact retirement and cancellation sets.
Witness: the group-node map keeps all refs and both permanent registries.
-/
theorem State.UncancelledRetiredHealthy.removeTask {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (occurrence : Occurrence)
    : (queue.removeTask occurrence).UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro ref retired uncancelled
  refine ⟨⟨retired.1, ?_⟩, uncancelled⟩
  simpa only [State.removeTask, List.map_map, Function.comp_def] using retired.2

/-- Failure removal creates only cancelled retirements, excluded from this invariant.
Witness: an absent uncancelled ref after cleanup was already absent and uncancelled.
-/
theorem State.UncancelledRetiredHealthy.removeGroup {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (root : Nat)
    : (queue.removeGroup root).UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro ref retired uncancelled
  have old := queue.removeGroup_missing_uncancelled root ref retired.lookup_none uncancelled
  exact ⟨.of_lookup_none retired.1 old.1, old.2⟩

/-- Cache exposure changes no retirement or cancellation record. -/
theorem State.UncancelledRetiredHealthy.cacheTaskFailures {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro ref retired uncancelled
  simpa only [State.RetiredGroup, State.cacheTaskFailures_registeredGroups,
    State.cacheTaskFailures_groupNodes, State.cacheTaskFailures_cancelledGroups]
    using And.intro retired uncancelled

/-- Startup only creates cancelled retirements; uncancelled health is inherited. -/
theorem State.UncancelledRetiredHealthy.startGroup {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (ref : Nat)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.UncancelledRetiredHealthy work failed := by
  have tasks (more : List Occurrence) (current : State)
      (known : current.UncancelledRetiredHealthy work failed)
      : (more.foldl (fun current task => current.startTask task available)
          current).UncancelledRetiredHealthy work failed := by
    induction more generalizing current with
    | nil => exact known
    | cons task rest ih =>
        apply ih
        change (current.startTask task available).UncancelledRetiredHealthy work failed
        unfold State.startTask
        split
        · exact known
        · split <;> exact known
  unfold State.startGroup
  dsimp only
  split
  · exact prior.cacheTaskFailures available
  · split
    · exact tasks _ _ (prior.cacheTaskFailures available)
    · exact (prior.cacheTaskFailures available).removeGroup _

/-- Actual activation preserves health at the same fixed failure inventory. -/
theorem State.UncancelledRetiredHealthy.startNewWork {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.UncancelledRetiredHealthy work
        failed := by
  have groups (more : NodeRefs) (acc : State × List GroupFailureEvent)
      (known : acc.1.UncancelledRetiredHealthy work failed)
      : (more.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.UncancelledRetiredHealthy work failed := by
    induction more generalizing acc with
    | nil => exact known
    | cons ref rest ih => exact ih _ (known.startGroup ref available)
  have streams (more : NodeRefs) (current : State)
      (known : current.UncancelledRetiredHealthy work failed)
      : (more.foldl State.startStream current).UncancelledRetiredHealthy work failed := by
    induction more generalizing current with
    | nil => exact known
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact known
  exact streams _ _ (groups _ _ prior)

/-- Replaying a rejected task creates only cancelled retirements.
Witness: replacing a task leaves retirement unchanged and each owner pass removes a group.
-/
theorem State.UncancelledRetiredHealthy.taskFailure_preserves {queue : State}
    {work failed} (prior : queue.UncancelledRetiredHealthy work failed)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.UncancelledRetiredHealthy work failed := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using prior
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      exact failureGroupFold_preserves
        (fun current => current.UncancelledRetiredHealthy work failed)
        (fun _ ref valid => valid.removeGroup ref) errors task.task.groups _ prior

/-- A refused fresh record is healthy when earlier failures remain accounted for.
Its own fresh ref has no failed contributor, and its absent uncancelled parent retired
healthy. The generated parent chain excludes inherited failures as well.
-/
theorem State.UncancelledRetiredHealthy.addGroup {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed)
    (counts : queue.RetainedFailures work failed) (generated : ExecutedWork work)
    (group : Group)
    (matching
      : ∃ dependencies,
          GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head?)
    (parentRegistered
      : ∀ parent, group.parent = some parent → parent ∈ queue.registeredGroups)
    : (queue.addGroup group).UncancelledRetiredHealthy work failed := by
  intro node dependencies known retired uncancelled
  rcases queue.addGroup_retired_origin group node.ref retired with old |
    ⟨same, fresh, parent, head, absent⟩
  · exact prior node dependencies known old (fun marked =>
      uncancelled (queue.addGroup_cancelledGroups_subset group marked))
  have missing : queue.groupNode? group.node.ref = none := by
    apply (queue.groupNode?_eq_none_iff _).mpr
    intro live
    exact retired.2 (same.symm ▸ queue.addGroup_refs_subset group live)
  have parentUncancelled : parent ∉ queue.cancelledGroups := by
    intro marked
    apply uncancelled
    rw [same]
    simp [State.addGroup, same ▸ fresh, missing, head, absent, marked]
  obtain ⟨ancestry, descriptor, canonical⟩ := matching
  have parentHead : ancestry.head? = some parent := canonical.symm.trans head
  cases ancestry with
  | nil => cases parentHead
  | cons first rest =>
      have equal : first = parent := Option.some.inj parentHead
      subst first
      obtain ⟨parentNode, parentRef, parentKnown⟩ := descriptor.parent
      have parentRetired : queue.RetiredGroup parent :=
        .of_lookup_none (parentRegistered parent head) absent
      have parentHealthy := prior parentNode rest parentKnown
        (parentRef.symm ▸ parentRetired) (parentRef.symm ▸ parentUncancelled)
      have ancestors := GroupAncestorsHealthy.child generated descriptor parentKnown
        (by simp [parentRef]) parentHealthy
      intro invalid
      rcases generated.groupRecordInvalidated_causes descriptor (same ▸ invalid) with
        ⟨occurrence, owners, task, owner, recorded⟩ | ⟨ancestor, member, failure⟩
      · exact counts.fresh _ (same ▸ fresh) occurrence recorded owners task owner
      · exact ancestors _ _ descriptor rfl ancestor member failure

/-- Parent-first registration retains the health of uncancelled retired records.
Witness: rejection retention excludes failures on fresh refs; declaration closure puts
absent parents in the registry before refused-child health is established.
-/
theorem State.UncancelledRetiredHealthy.addGroups {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (groups : List Group)
    (counts : queue.RetainedFailures work failed) (generated : ExecutedWork work)
    (coverage : queue.LiveGroupsRegistered)
    (matching
      : ∀ group ∈ groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (closed
      : ∀ group ∈ groups,
          ∀ parent,
            group.parent = some parent
            → parent ∈ queue.registeredGroups ++ groups.map (fun group => group.node.ref))
    : (queue.addGroups groups).1.UncancelledRetiredHealthy work failed := by
  let property (current : State) := current.UncancelledRetiredHealthy work failed
    ∧ current.RetainedFailures work failed ∧ queue.registeredGroups ⊆ current.registeredGroups
  have ordered : ∀ group ∈ groups, ∀ parent, group.parent = some parent → parent < group.node.ref := by
    intro group member parent parentEq
    obtain ⟨dependencies, known, canonical⟩ := matching group member
    exact generated.groupRecordAncestorSmaller known
      (List.mem_of_head? (canonical.symm.trans parentEq))
  exact (State.addGroups_preserves_parentRegistered property groups ordered
          (fun current group member _ parents valid =>
            ⟨
              valid.1.addGroup valid.2.1 generated group (matching group member)
                (fun parent parentEq =>
                  (List.mem_append.mp (closed group member parent parentEq)).elim
                    (fun known => valid.2.2 known) (parents parent parentEq)),
              valid.2.1.addGroup group,
              valid.2.2.trans (current.addGroup_registeredGroups_subset_old group)
            ⟩)
          queue coverage ⟨prior, counts, List.Subset.refl _⟩).1

/-- Task registration preserves all uncancelled retired records' health.
Witness: registration leaves permanent groups unchanged and retains each old live ref.
-/
theorem State.UncancelledRetiredHealthy.addTask {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (task : Task)
    : (queue.addTask task).UncancelledRetiredHealthy work failed := by
  apply prior.of_retirementOrigins
  intro ref retired uncancelled
  refine ⟨⟨?_, fun live => retired.2 (queue.addTask_includesRefs task ref live)⟩, ?_⟩
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

/-- Certified integration retains the health of uncancelled retirements.
Witness: retained failures and generated parent closure justify refused records;
task and stream installation then preserve the certificate.
-/
theorem State.UncancelledRetiredHealthy.maybeIntegrateWork {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (newWork : Work)
    (parentTask : Option Occurrence := none)
    (counts : queue.RetainedFailures work failed) (generated : ExecutedWork work)
    (coverage : queue.LiveGroupsRegistered)
    (matching
      : ∀ group ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (closed
      : ∀ group ∈ newWork.groups,
          ∀ parent,
            group.parent = some parent
            → parent
              ∈ queue.registeredGroups
                ++ newWork.groups.map (fun group => group.node.ref))
    : (queue.maybeIntegrateWork newWork parentTask).1.UncancelledRetiredHealthy work
        failed := by
  have loop (tasks : List Task) (current : State)
      (invariant : current.UncancelledRetiredHealthy work failed)
      : (tasks.foldl State.addTask current).UncancelledRetiredHealthy work failed := by
    induction tasks generalizing current with
    | nil => exact invariant
    | cons task rest ih => exact ih _ (invariant.addTask task)
  exact (loop newWork.tasks _
          (prior.addGroups newWork.groups counts generated coverage matching
            closed)).addStreams
    newWork.streams parentTask

-----------------------------------------------------------------------------------------
-- Health at successful removal and fresh-failure extension
-----------------------------------------------------------------------------------------

/-- Filtering a healthy ref preserves healthy uncancelled retirement.
Witness: a newly retired target is the healthy removed ref; every other target was already
retired. Failure health is a static fact about `work` and `failed`, not the live lookup.
-/
theorem State.UncancelledRetiredHealthy.filter_parent {queue : State} {work failed ref}
    (prior : queue.UncancelledRetiredHealthy work failed)
    (healthy : ¬GroupRecordInvalidated work failed ref)
    : ({
        queue with
          groupNodes := queue.groupNodes.filter (fun node => node.group.node.ref != ref)
      }).UncancelledRetiredHealthy
        work failed := by
  intro node dependencies known retired uncancelled
  by_cases same : node.ref = ref
  · exact same ▸ healthy
  · have old : queue.RetiredGroup node.ref := by
      refine ⟨retired.1, ?_⟩
      intro live
      obtain ⟨other, member, sameRef⟩ := List.mem_map.mp live
      exact retired.2 (List.mem_map.mpr ⟨other,
        List.mem_filter.mpr ⟨member, by simp [sameRef, same]⟩, sameRef⟩)
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
  exact retired.healthy_cons_fresh (ancestors node.ref retired uncancelled) generated known
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
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registry : queue.ParentRegistryClosed parents)
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (newWork : Work)
    (parentLinks
      : ∀ group ∈ newWork.groups, group.parent = (parents group.node.ref).head?)
    (parentsCovered : newWork.ParentsCovered queue.registeredGroups)
    (covered
      : ∀ task ∈ newWork.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ref ∈ queue.registeredGroups ∨ ∃ group ∈ newWork.groups, group.node.ref = ref)
    (parentTask : Option Occurrence := none)
    (counts : queue.RetainedFailures work failed)
    (known
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    : (queue.maybeIntegrateWork newWork parentTask).1.MissingParentAncestorsHealthy
        work failed := by
  have nextFields := fields.maybeIntegrateWork newWork parentLinks parentTask
  have nextRegistry :=
    registry.maybeIntegrateWork live newWork parentLinks parentsCovered parentTask
  have nextLive := (queue.maybeIntegrateWork_registration live tasks newWork covered parentTask).1
  exact (prior.maybeIntegrateWork newWork parentTask counts generated live
          (by
            intro group member
            obtain ⟨dependencies, record⟩ := known group member
            exact ⟨
              dependencies,
              record,
              by rw [canonical _ _ record]; exact parentLinks group member
            ⟩)
          (by
            intro group member parent head
            rcases parentsCovered group member parent head with old | fresh
            · exact List.mem_append_left _ old
            · obtain ⟨candidate, included, same⟩ := fresh
              exact List.mem_append_right _ (List.mem_map.mpr ⟨candidate, included, same⟩))).missingParent
    generated nextFields canonical
    (fun node member parent parentEq =>
      nextRegistry.parent_registered nextLive nextFields member parentEq)

/-- Fresh integration candidates have healthy ancestry because their full parent list is
empty. Witness: candidate extraction gives a parentless registered descriptor and generated
canonical ancestry equates every occurrence of its ref. Pruned descendants are separate.
-/
theorem State.maybeIntegrateWork_newGroups_ancestorsHealthy {work failed}
    {parents : Nat → NodeRefs} (queue : State) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (newWork : Work)
    (known
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (parentLinks
      : ∀ group ∈ newWork.groups, group.parent = (parents group.node.ref).head?)
    (parentTask : Option Occurrence := none)
    : ∀ node ∈ (queue.maybeIntegrateWork newWork parentTask).2.newGroups,
        GroupAncestorsHealthy work failed node.ref := by
  intro node member
  obtain ⟨group, included, same, parentless, _, _⟩ :=
    queue.addGroups_newGroup_candidate newWork.groups member
  obtain ⟨dependencies, descriptor⟩ := known group included
  have empty : dependencies = [] := by
    apply List.head?_eq_none_iff.mp
    rw [canonical _ _ descriptor, ← parentLinks group included, parentless]
  have healthy : GroupAncestorsHealthy work failed group.node.ref :=
    GroupAncestorsHealthy.of_record generated descriptor (by simp [empty])
  exact same ▸ healthy

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
