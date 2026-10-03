import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedWork

/-! Queue-local group removal and its connection to historical causal failure. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Which groups does task-failure cleanup invalidate?
-----------------------------------------------------------------------------------------

/-- A group is invalidated by a failed contributing task or an invalidated defer
ancestor. `failed` lists settled task failures; `ref` is the affected group ref.
This proof-side relation has no producer-cancellation or stream-dependency rule.
It is not a replacement for the publication-aware scheduler contract.
-/
inductive GroupInvalidated (work : Execution.Work) (failed : List Occurrence) : Nat → Prop
  | task {occurrence owners ref}
    (known : TaskHasOwners work occurrence owners)
    (owner : ref ∈ owners) (member : occurrence ∈ failed)
    : GroupInvalidated work failed ref
  | groupDependency {ref dependencies ancestor}
    (known : NodeHasDependencies work ref .group dependencies)
    (member : ancestor ∈ dependencies)
    (failure : GroupInvalidated work failed ancestor)
    : GroupInvalidated work failed ref

/-- Cleanup invalidation persists when more task failures are recorded.
Witness: induction on the contributing-task/defer-ancestor derivation.
-/
theorem GroupInvalidated.mono {work before after ref}
    (failure : GroupInvalidated work before ref) (included : before.Subset after)
    : GroupInvalidated work after ref := by
  induction failure with
  | task known owner member => exact .task known owner (included member)
  | groupDependency known member _ ih => exact .groupDependency known member ih

/-- Recording a task whose owners are already invalidated adds no new invalidated groups.
Witness: replace uses of the new failure token by the corresponding prior owner cause,
then propagate the unchanged causes through defer ancestry. This concerns causal health,
not error totals: an ignored failure still must not be counted as a new contribution.
-/
theorem groupInvalidated_cons_iff_of_ownersInvalidated {work failed occurrence owners ref}
    (known : TaskHasOwners work occurrence owners)
    (invalid : ∀ owner ∈ owners, GroupInvalidated work failed owner)
    : GroupInvalidated work (occurrence :: failed) ref
      ↔ GroupInvalidated work failed ref := by
  constructor
  · intro failure
    induction failure with
    | @task other otherOwners ref task owner member =>
        rcases List.mem_cons.mp member with same | earlier
        · subst other
          obtain ⟨producer, payload, task⟩ := task
          obtain ⟨knownProducer, knownPayload, descriptor⟩ := known
          obtain ⟨rfl, _, _⟩ := task.unique descriptor
          exact invalid ref owner
        · exact .task task owner earlier
    | groupDependency descriptor member _ ih =>
        exact .groupDependency descriptor member ih
  · intro failure
    exact failure.mono (by intro item member; exact List.mem_cons_of_mem _ member)

/-- Every cleanup invalidation originates in a recorded task failure.
Witness: follow defer ancestry to its contributing-task leaf.
-/
theorem GroupInvalidated.nonempty {work failed ref}
    (failure : GroupInvalidated work failed ref)
    : failed ≠ [] := by
  induction failure with
  | task _ _ member => intro empty; simp [empty] at member
  | groupDependency _ _ _ ih => exact ih

/-- Queue-local invalidation is a causal failure at any publication snapshot.
Witness: the two cleanup rules embed directly in the causal kernel.
-/
theorem GroupInvalidated.toCausality {work failed ref}
    (failure : GroupInvalidated work failed ref) (published : Occurrence → Prop)
    : Causality.NodeFailed work failed published ref := by
  induction failure with
  | task known owner member => exact .task known owner member
  | groupDependency known member _ ih => exact .groupDependency known member ih

/-- Recorded cleanup failures give historical scheduler failures in an explained
history. Witness: embed at the current snapshot and recover a recorded failure cut.
The converse is not asserted: the scheduler also accounts for producer cancellation.
-/
theorem GroupInvalidated.toNodeFailed
    {work failed ref groups streams events matching cuts}
    (failure : GroupInvalidated work failed ref)
    (explained : Explains work groups streams events matching cuts)
    (included : failed.Subset (failedBefore cuts events.length))
    : NodeFailed work matching events cuts ref :=
  explained.snapshot_nodeFailed
    ((failure.mono included).toCausality (Published matching events))

/-- A generated group's invalidation is direct or comes from one of its own
defer ancestors. Witness: generated descriptors agree on the dependency list.
-/
theorem ExecutedWork.groupInvalidated_causes {work : Execution.Work}
    (generated : ExecutedWork work) {node dependencies producer failed}
    (known : NodeAt work node .group dependencies producer)
    (failure : GroupInvalidated work failed node.ref)
    : (∃ occurrence owners,
        TaskHasOwners work occurrence owners ∧ node.ref ∈ owners ∧ occurrence ∈ failed)
      ∨ ∃ dependency ∈ dependencies, GroupInvalidated work failed dependency := by
  cases failure with
  | task task owner member => exact .inl ⟨_, _, task, owner, member⟩
  | @groupDependency ref otherDependencies ancestor descriptor member prior =>
      obtain ⟨other, birth, otherKnown, refEq⟩ := descriptor
      obtain ⟨parents, canonical⟩ := generated.groupDependenciesCanonical
      have dependenciesEq := canonical node dependencies producer known
      have otherEq := canonical other otherDependencies birth otherKnown
      have same : otherDependencies = dependencies := by
        rw [refEq] at otherEq
        exact otherEq.trans dependenciesEq.symm
      exact .inr ⟨ancestor, same ▸ member, prior⟩

-----------------------------------------------------------------------------------------
-- Invalidation has one failed contributing task as its origin
-----------------------------------------------------------------------------------------

/-- Recursive invalidation traces back to one failed contributor of this ref or one
of its full defer ancestors. Witness: follow the derivation and flatten ancestor chains
using generated ancestry transitivity. No event ordering or queue invariant is assumed.
-/
private theorem GroupInvalidated.origin {work failed ref}
    (failure : GroupInvalidated work failed ref) (generated : ExecutedWork work)
    : ∃ occurrence owners owner,
        TaskHasOwners work occurrence owners
        ∧ occurrence ∈ failed
        ∧ owner ∈ owners
        ∧ (owner = ref
            ∨ ∃ node dependencies producer,
                NodeAt work node .group dependencies producer
                ∧ node.ref = ref
                ∧ owner ∈ dependencies) := by
  induction failure with
  | @task occurrence owners ref known owner member =>
      exact ⟨occurrence, owners, ref, known, member, owner, .inl rfl⟩
  | @groupDependency ref dependencies ancestor known member _ ih =>
      obtain ⟨node, producer, nodeKnown, nodeRef⟩ := known
      obtain ⟨occurrence, owners, owner, task, failed, contributes, direct | earlier⟩ := ih
      · exact ⟨occurrence, owners, owner, task, failed, contributes,
          .inr ⟨node, dependencies, producer, nodeKnown, nodeRef, direct ▸ member⟩⟩
      · obtain ⟨ancestorNode, ancestorDependencies, ancestorProducer,
          ancestorKnown, ancestorRef, inAncestors⟩ := earlier
        have included := generated.groupAncestors_trans nodeKnown ancestorKnown
          (ancestorRef.symm ▸ member)
        exact ⟨occurrence, owners, owner, task, failed, contributes,
          .inr ⟨node, dependencies, producer, nodeKnown, nodeRef, included inAncestors⟩⟩

/-- A generated group is invalidated exactly when a recorded failed task contributes
to that group or one of its full defer ancestors. Witness: flatten recursive causes in
one direction and apply the direct or ancestor rule in the other.
-/
theorem ExecutedWork.groupInvalidated_iff
    {work : Execution.Work} (generated : ExecutedWork work)
    {node dependencies producer failed}
    (known : NodeAt work node .group dependencies producer)
    : GroupInvalidated work failed node.ref
      ↔ ∃ occurrence owners owner,
          TaskHasOwners work occurrence owners
          ∧ occurrence ∈ failed
          ∧ owner ∈ owners
          ∧ owner ∈ node.ref :: dependencies := by
  constructor
  · intro failure
    obtain ⟨occurrence, owners, owner, task, failed, contributes, direct | ancestor⟩ :=
      failure.origin generated
    · exact ⟨occurrence, owners, owner, task, failed, contributes, by simp [direct]⟩
    · obtain ⟨other, otherDependencies, otherProducer, otherKnown, sameRef, member⟩ :=
        ancestor
      obtain ⟨parents, canonical⟩ := generated.groupDependenciesCanonical
      have same : otherDependencies = dependencies := by
        rw [canonical other otherDependencies otherProducer otherKnown,
          canonical node dependencies producer known, sameRef]
      exact ⟨occurrence, owners, owner, task, failed, contributes,
        List.mem_cons.mpr (.inr (same ▸ member))⟩
  · rintro ⟨occurrence, owners, owner, task, recorded, contributes, member⟩
    have direct : GroupInvalidated work failed owner := .task task contributes recorded
    rcases List.mem_cons.mp member with same | ancestor
    · exact same ▸ direct
    · exact .groupDependency ⟨node, producer, known, rfl⟩ ancestor direct

/-- When a previously healthy group becomes invalidated after one new task failure,
that task itself owns the group or an ancestor. Witness: the flat characterization;
an older contributing failure would contradict the group's previous health.
-/
theorem ExecutedWork.groupInvalidated_cons_iff
    {work : Execution.Work} (generated : ExecutedWork work)
    {node dependencies producer failed occurrence owners}
    (known : NodeAt work node .group dependencies producer)
    (healthy : ¬GroupInvalidated work failed node.ref)
    (task : TaskHasOwners work occurrence owners)
    : GroupInvalidated work (occurrence :: failed) node.ref
      ↔ ∃ owner ∈ owners, owner ∈ node.ref :: dependencies := by
  constructor
  · intro failure
    obtain ⟨other, otherOwners, owner, otherTask, member, contributes, ancestor⟩ :=
      (generated.groupInvalidated_iff known).mp failure
    rcases List.mem_cons.mp member with same | earlier
    · subst other
      obtain ⟨birth, result, descriptor⟩ := task
      obtain ⟨otherBirth, otherResult, otherDescriptor⟩ := otherTask
      have ownersEq := (TaskAt.unique otherDescriptor descriptor).1
      exact ⟨owner, ownersEq ▸ contributes, ancestor⟩
    · exact False.elim (healthy ((generated.groupInvalidated_iff known).mpr
        ⟨other, otherOwners, owner, otherTask, earlier, contributes, ancestor⟩))
  · rintro ⟨owner, contributes, ancestor⟩
    exact (generated.groupInvalidated_iff known).mpr
      ⟨occurrence, owners, owner, task, by simp, contributes, ancestor⟩

-----------------------------------------------------------------------------------------
-- Initially satisfied defer dependencies cannot be invalidated by later task failures
-----------------------------------------------------------------------------------------

/-- Every cleanup-invalidated ref has a contributing task, even when its actual
failure came from an ancestor. Witness: a direct task or the execution-group descriptor
in the ancestor rule. This is specific to cleanup, not general causal cancellation.
-/
theorem GroupInvalidated.hasContributor {work failed ref}
    (failure : GroupInvalidated work failed ref)
    : ∃ occurrence owners, TaskHasOwners work occurrence owners ∧ ref ∈ owners := by
  cases failure with
  | task known owner _ => exact ⟨_, _, known, owner⟩
  | groupDependency known _ _ =>
      obtain ⟨node, producer, descriptor, same⟩ := known
      obtain ⟨address, groups, path, result, children, enclosing, group,
        located, member, nodeEq, _⟩ := descriptor
      refine ⟨.executionGroup address, groups.map (fun group => group.node.ref),
        ⟨producer, .object path result, .executionGroup located⟩, ?_⟩
      rw [← same, nodeEq]
      exact List.mem_map_of_mem member

/-- A dependency satisfied before any output has no contributing task: nothing has
been published or cancelled yet. Hence no later cleanup failure list can invalidate it.
Witness: empty-history accounting, followed by the contributor-existence lemma.
-/
theorem dependencySatisfied_initial_uninvalidated
    {work initial matching ref}
    (satisfied : DependencySatisfied work initial matching [] [] ref)
    (failed : List Occurrence)
    : ¬GroupInvalidated work failed ref := by
  intro failure
  obtain ⟨occurrence, owners, task, owner⟩ := failure.hasContributor
  obtain ⟨producer, payload, known⟩ := task
  rcases satisfied.2 with absent | completed | ⟨_, accounted⟩
  · obtain ⟨node, kind, dependencies, birth, descriptor, same⟩ := known.owner_known owner
    exact absent ⟨birth, node, kind, dependencies, descriptor, same⟩
  · simp [completedRefs] at completed
  · have impossible := accounted occurrence owners ⟨producer, payload, known⟩ owner
    simp [TaskAccounted, TaskCancelled, Published] at impossible

/-- Every dependency of an initially announced group stays outside queue-local
invalidation for any later task-failure list. Witness: the initialization contract and
the fact that each dependency was already satisfied in the empty output history.
-/
theorem Initializes.groupDependencies_uninvalidated
    {work groups streams} (initialized : Initializes work groups streams)
    {node} (member : node ∈ groups)
    : ∃ dependencies producer,
        NodeAt work node .group dependencies producer
        ∧ ∀ failed ref, ref ∈ dependencies → ¬GroupInvalidated work failed ref := by
  obtain ⟨dependencies, producer, known, eligible⟩ := initialized.1.2.1 node member
  exact ⟨dependencies, producer, known, fun failed ref ancestor =>
    dependencySatisfied_initial_uninvalidated (eligible.2.2.2 ref ancestor) failed⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
