import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedWork

/-! Queue-local group removal and its connection to historical causal failure. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Which groups does task-failure cleanup invalidate?
-----------------------------------------------------------------------------------------

/-- A group is invalidated by a failed contributing task or an invalidated defer
ancestor. `failed` lists settled task failures; `key` is the affected group key.
This proof-side relation has no producer-cancellation or stream-dependency rule.
It is not a replacement for the publication-aware scheduler contract.
-/
inductive GroupInvalidated (work : Execution.Work) (failed : List Occurrence) : Nat → Prop
  | task {occurrence owners key}
    (known : TaskHasOwners work occurrence owners)
    (owner : key ∈ owners) (member : occurrence ∈ failed)
    : GroupInvalidated work failed key
  | groupDependency {key dependencies ancestor}
    (known : NodeHasDependencies work key .group dependencies)
    (member : ancestor ∈ dependencies)
    (failure : GroupInvalidated work failed ancestor)
    : GroupInvalidated work failed key

/-- Cleanup invalidation persists when more task failures are recorded.
Witness: induction on the contributing-task/defer-ancestor derivation.
-/
theorem GroupInvalidated.mono {work before after key}
    (failure : GroupInvalidated work before key) (included : before.Subset after)
    : GroupInvalidated work after key := by
  induction failure with
  | task known owner member => exact .task known owner (included member)
  | groupDependency known member _ ih => exact .groupDependency known member ih

/-- Recording a task whose owners are already invalidated adds no new invalidated groups.
Witness: replace uses of the new failure token by the corresponding prior owner cause,
then propagate the unchanged causes through defer ancestry. This concerns causal health,
not error totals: an ignored failure still must not be counted as a new contribution.
-/
theorem groupInvalidated_cons_iff_of_ownersInvalidated {work failed occurrence owners key}
    (known : TaskHasOwners work occurrence owners)
    (invalid : ∀ owner ∈ owners, GroupInvalidated work failed owner)
    : GroupInvalidated work (occurrence :: failed) key
      ↔ GroupInvalidated work failed key := by
  constructor
  · intro failure
    induction failure with
    | @task other otherOwners key task owner member =>
        rcases List.mem_cons.mp member with same | earlier
        · subst other
          obtain ⟨producer, payload, task⟩ := task
          obtain ⟨knownProducer, knownPayload, descriptor⟩ := known
          obtain ⟨rfl, _, _⟩ := task.unique descriptor
          exact invalid key owner
        · exact .task task owner earlier
    | groupDependency descriptor member _ ih =>
        exact .groupDependency descriptor member ih
  · intro failure
    exact failure.mono (by intro item member; exact List.mem_cons_of_mem _ member)

/-- Every cleanup invalidation originates in a recorded task failure.
Witness: follow defer ancestry to its contributing-task leaf.
-/
theorem GroupInvalidated.nonempty {work failed key}
    (failure : GroupInvalidated work failed key)
    : failed ≠ [] := by
  induction failure with
  | task _ _ member => intro empty; simp [empty] at member
  | groupDependency _ _ _ ih => exact ih

/-- Queue-local invalidation is a causal failure at any publication snapshot.
Witness: the two cleanup rules embed directly in the causal kernel.
-/
theorem GroupInvalidated.toCausality {work failed key}
    (failure : GroupInvalidated work failed key) (published : Occurrence → Prop)
    : Causality.NodeFailed work failed published key := by
  induction failure with
  | task known owner member => exact .task known owner member
  | groupDependency known member _ ih => exact .groupDependency known member ih

/-- Recorded cleanup failures give historical scheduler failures in an explained
history. Witness: embed at the current snapshot and recover a recorded failure cut.
The converse is not asserted: the scheduler also accounts for producer cancellation.
-/
theorem GroupInvalidated.toNodeFailed
    {work failed key groups streams events matching cuts}
    (failure : GroupInvalidated work failed key)
    (explained : Explains work groups streams events matching cuts)
    (included : failed.Subset (failedBefore cuts events.length))
    : NodeFailed work matching events cuts key :=
  explained.snapshot_nodeFailed
    ((failure.mono included).toCausality (Published matching events))

/-- A generated group's invalidation is direct or comes from one of its own
defer ancestors. Witness: generated descriptors agree on the dependency list.
-/
theorem ExecutedWork.groupInvalidated_causes {work : Execution.Work}
    (generated : ExecutedWork work) {node dependencies producer failed}
    (known : NodeAt work node .group dependencies producer)
    (failure : GroupInvalidated work failed node.key)
    : (∃ occurrence owners,
        TaskHasOwners work occurrence owners ∧ node.key ∈ owners ∧ occurrence ∈ failed)
      ∨ ∃ dependency ∈ dependencies, GroupInvalidated work failed dependency := by
  cases failure with
  | task task owner member => exact .inl ⟨_, _, task, owner, member⟩
  | @groupDependency key otherDependencies ancestor descriptor member prior =>
      obtain ⟨other, birth, otherKnown, keyEq⟩ := descriptor
      obtain ⟨parents, canonical⟩ := generated.groupDependenciesCanonical
      have dependenciesEq := canonical node dependencies producer known
      have otherEq := canonical other otherDependencies birth otherKnown
      have same : otherDependencies = dependencies := by
        rw [keyEq] at otherEq
        exact otherEq.trans dependenciesEq.symm
      exact .inr ⟨ancestor, same ▸ member, prior⟩

-----------------------------------------------------------------------------------------
-- Invalidation has one failed contributing task as its origin
-----------------------------------------------------------------------------------------

/-- Recursive invalidation traces back to one failed contributor of this key or one
of its full defer ancestors. Witness: follow the derivation and flatten ancestor chains
using generated ancestry transitivity. No event ordering or queue invariant is assumed.
-/
private theorem GroupInvalidated.origin {work failed key}
    (failure : GroupInvalidated work failed key) (generated : ExecutedWork work)
    : ∃ occurrence owners owner,
        TaskHasOwners work occurrence owners
        ∧ occurrence ∈ failed
        ∧ owner ∈ owners
        ∧ (owner = key
            ∨ ∃ node dependencies producer,
                NodeAt work node .group dependencies producer
                ∧ node.key = key
                ∧ owner ∈ dependencies) := by
  induction failure with
  | @task occurrence owners key known owner member =>
      exact ⟨occurrence, owners, key, known, member, owner, .inl rfl⟩
  | @groupDependency key dependencies ancestor known member _ ih =>
      obtain ⟨node, producer, nodeKnown, nodeKey⟩ := known
      obtain ⟨occurrence, owners, owner, task, failed, contributes, direct | earlier⟩ := ih
      · exact ⟨occurrence, owners, owner, task, failed, contributes,
          .inr ⟨node, dependencies, producer, nodeKnown, nodeKey, direct ▸ member⟩⟩
      · obtain ⟨ancestorNode, ancestorDependencies, ancestorProducer,
          ancestorKnown, ancestorKey, inAncestors⟩ := earlier
        have included := generated.groupAncestors_trans nodeKnown ancestorKnown
          (ancestorKey.symm ▸ member)
        exact ⟨occurrence, owners, owner, task, failed, contributes,
          .inr ⟨node, dependencies, producer, nodeKnown, nodeKey, included inAncestors⟩⟩

/-- A generated group is invalidated exactly when a recorded failed task contributes
to that group or one of its full defer ancestors. Witness: flatten recursive causes in
one direction and apply the direct or ancestor rule in the other.
-/
theorem ExecutedWork.groupInvalidated_iff
    {work : Execution.Work} (generated : ExecutedWork work)
    {node dependencies producer failed}
    (known : NodeAt work node .group dependencies producer)
    : GroupInvalidated work failed node.key
      ↔ ∃ occurrence owners owner,
          TaskHasOwners work occurrence owners
          ∧ occurrence ∈ failed
          ∧ owner ∈ owners
          ∧ owner ∈ node.key :: dependencies := by
  constructor
  · intro failure
    obtain ⟨occurrence, owners, owner, task, failed, contributes, direct | ancestor⟩ :=
      failure.origin generated
    · exact ⟨occurrence, owners, owner, task, failed, contributes, by simp [direct]⟩
    · obtain ⟨other, otherDependencies, otherProducer, otherKnown, sameKey, member⟩ :=
        ancestor
      obtain ⟨parents, canonical⟩ := generated.groupDependenciesCanonical
      have same : otherDependencies = dependencies := by
        rw [canonical other otherDependencies otherProducer otherKnown,
          canonical node dependencies producer known, sameKey]
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
    (healthy : ¬GroupInvalidated work failed node.key)
    (task : TaskHasOwners work occurrence owners)
    : GroupInvalidated work (occurrence :: failed) node.key
      ↔ ∃ owner ∈ owners, owner ∈ node.key :: dependencies := by
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

/-- Every cleanup-invalidated key has a contributing task, even when its actual
failure came from an ancestor. Witness: a direct task or the execution-group descriptor
in the ancestor rule. This is specific to cleanup, not general causal cancellation.
-/
theorem GroupInvalidated.hasContributor {work failed key}
    (failure : GroupInvalidated work failed key)
    : ∃ occurrence owners, TaskHasOwners work occurrence owners ∧ key ∈ owners := by
  cases failure with
  | task known owner _ => exact ⟨_, _, known, owner⟩
  | groupDependency known _ _ =>
      obtain ⟨node, producer, descriptor, same⟩ := known
      obtain ⟨address, groups, path, result, children, enclosing, group,
        located, member, nodeEq, _⟩ := descriptor
      refine ⟨.executionGroup address, groups.map (fun group => group.node.key),
        ⟨producer, .object path result, .executionGroup located⟩, ?_⟩
      rw [← same, nodeEq]
      exact List.mem_map_of_mem member

/-- A dependency satisfied before any output has no contributing task: nothing has
been published or cancelled yet. Hence no later cleanup failure list can invalidate it.
Witness: empty-history accounting, followed by the contributor-existence lemma.
-/
theorem dependencySatisfied_initial_uninvalidated
    {work initial matching key}
    (satisfied : DependencySatisfied work initial matching [] [] key)
    (failed : List Occurrence)
    : ¬GroupInvalidated work failed key := by
  intro failure
  obtain ⟨occurrence, owners, task, owner⟩ := failure.hasContributor
  obtain ⟨producer, payload, known⟩ := task
  rcases satisfied.2 with absent | completed | ⟨_, accounted⟩
  · obtain ⟨node, kind, dependencies, birth, descriptor, same⟩ := known.owner_known owner
    exact absent ⟨birth, node, kind, dependencies, descriptor, same⟩
  · simp [completedKeys] at completed
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
        ∧ ∀ failed key, key ∈ dependencies → ¬GroupInvalidated work failed key := by
  obtain ⟨dependencies, producer, known, eligible⟩ := initialized.1.2.1 node member
  exact ⟨dependencies, producer, known, fun failed key ancestor =>
    dependencySatisfied_initial_uninvalidated (eligible.2.2.2 key ancestor) failed⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
